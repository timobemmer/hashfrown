#![feature(allocator_api, ptr_internals)]

use ctrl::{Ctrl, Flag};
use group::{Group, SIZE as GROUP_SIZE};
use std::{
    alloc::{handle_alloc_error, AllocInit, AllocRef, Global, Layout},
    collections::hash_map::RandomState,
    fmt,
    hash::{BuildHasher, Hash, Hasher},
    iter::FromIterator,
    marker::PhantomData,
    mem,
    ops::{Add, Index},
    ptr::{self, NonNull, Unique},
};

mod ctrl;
mod group;

fn is_zst<T>() -> bool {
    mem::size_of::<T>() == 0
}

fn h1(hash: u64) -> u64 {
    hash >> 7
}

fn h2(hash: u64) -> Ctrl {
    Ctrl::from(hash)
}

/// A very simple, probably incorrect implementation
/// of Google's swiss map based on [this talk](https://youtu.be/ncHmEUmJZf4).
pub struct CustomSet<T> {
    slot: Unique<T>,
    ctrl: Unique<Ctrl>,
    load_factor: f64,
    load: usize,
    groups: usize,
    hash_builder: RandomState,
}

impl<T> CustomSet<T> {
    /// Returns an empty set. Doesn't allocate.
    fn empty() -> Self {
        Self {
            slot: Unique::dangling(),
            ctrl: Unique::dangling(),
            load: 0,
            load_factor: 0.5,
            groups: 0,
            hash_builder: RandomState::new(),
        }
    }

    /// Returns a new set with the capacity specified.
    ///
    /// Doesn't allocate if `cap == 0`.
    fn with_capacity(cap: usize) -> Self {
        assert!(cap < isize::MAX as usize, "capacity overflow");
        if cap == 0 {
            Self::empty()
        } else {
            unsafe {
                let groups = Self::groups_from_cap(cap);
                let (slot, ctrl) = Self::allocate_groups(groups);
                Self {
                    slot: Unique::new_unchecked(slot),
                    ctrl: Unique::new_unchecked(ctrl),
                    groups,
                    load: 0,
                    load_factor: 0.5,
                    hash_builder: RandomState::new(),
                }
            }
        }
    }

    /// Return the raw pointer to the ctrl array.
    fn ctrl(&self) -> *mut Ctrl {
        self.ctrl.as_ptr()
    }

    /// Return the raw pointer to the slot array.
    fn slot(&self) -> *mut T {
        self.slot.as_ptr()
    }

    /// Return a raw pointer to the slot at `idx`.
    fn slot_at(&self, idx: Idx) -> *mut T {
        self.slot() + idx
    }

    /// Return a raw pointer to the ctrl at `idx`.
    fn ctrl_at(&self, idx: Idx) -> *mut Ctrl {
        self.ctrl() + idx
    }

    /// Return the `group`th group of ctrls.
    fn ctrl_group(&self, group: usize) -> Group {
        Group(self.ctrl() + Idx::group(group))
    }

    /// Returns the the layout of the slot array and the ctrl array.
    fn layout(groups: usize) -> (Layout, Layout) {
        (
            Layout::array::<T>(groups * GROUP_SIZE).unwrap(),
            Layout::array::<Ctrl>(groups * GROUP_SIZE).unwrap(),
        )
    }

    /// Allocates enough memory to hold `groups` groups of elements
    /// and control bytes. Sets all control bytes to [Flag::Empty](ctrl::Flag::Empty).
    fn allocate_groups(groups: usize) -> (*mut T, *mut Ctrl) {
        let (slot_layout, ctrl_layout) = Self::layout(groups);

        let slot = match Global.alloc(slot_layout, AllocInit::Uninitialized) {
            Ok(block) => block.ptr.as_ptr(),
            Err(_) => handle_alloc_error(slot_layout),
        } as *mut T;
        let ctrl = match Global.alloc(ctrl_layout, AllocInit::Uninitialized) {
            Ok(block) => block.ptr.as_ptr(),
            Err(_) => handle_alloc_error(ctrl_layout),
        } as *mut Ctrl;

        // SAFETY: This is safe because we got `ctrl` from
        // the global allocator, and we make sure that the
        // `Ctrl` type has a byte layout.
        unsafe {
            Self::init_ctrl_array(ctrl, groups);
        }

        (slot, ctrl)
    }

    /// Initializes an array of length `groups * GROUP_SIZE`
    /// of `Ctrl`s starting at `ptr` with [`Flag::Empty`](ctrl::Flag::Empty).
    ///
    /// # Safety
    ///
    /// See [`ptr::write_bytes`](std::ptr::write_bytes) for safety.
    unsafe fn init_ctrl_array(ptr: *mut Ctrl, groups: usize) {
        #[cfg(any(arch = "x86", arch = "x86_64"))]
        {
            if std::is_x86_feature_detected!("sse2") {
                // SAFETY: This is safe because we checked that SSE2 is
                // available.
                return unsafe { Self::init_ctrl_array_sse2(ptr, groups) };
            }
        }
        ptr::write_bytes(ptr, Flag::Empty as u8, groups * GROUP_SIZE);
    }

    #[cfg(any(arch = "x86", arch = "x86_64"))]
    #[target_feature(enable = "sse2")]
    unsafe fn init_ctrl_array_sse2(ptr: *mut Ctrl, groups: usize) {
        #[cfg(arch = "x86")]
        use std::arch::x86::{_mm_set1_epi8, _mm_store_si128};
        #[cfg(arch = "x86_64")]
        use std::arch::x86_64::{_mm_set1_epi8, _mm_store_si128};

        let vector = _mm_set1_epi8(Flag::Empty as i8);

        for group in 0..groups {
            _mm_store_si128(ptr + Index::group(group) as *mut _, vector);
        }
    }

    /// Returns the set's capacity for elements. Only used
    /// to calculate when to grow the buffer.
    fn cap(&self) -> usize {
        assert!(!is_zst::<T>());
        self.groups * GROUP_SIZE
    }

    /// Calculates the minimum number of groups needed to hold
    /// `cap` elements.
    fn groups_from_cap(cap: usize) -> usize {
        (cap / GROUP_SIZE) + (cap % GROUP_SIZE != 0) as usize
    }

    fn iter(&self) -> CustomSetIter<'_, T> {
        CustomSetIter::new(self)
    }
}

impl<T> CustomSet<T>
where
    T: Hash + Eq + Clone,
{
    /// Return a new set containing all elements in `input`.
    ///
    /// Doesn't allocate if `input` is empty.
    pub fn new(input: &[T]) -> Self {
        let mut set = Self::with_capacity(input.len() * 2);
        for el in input {
            set.add(el.clone());
        }
        set
    }

    /// Returns the intersection `self` ∩ `other`.
    pub fn intersection(&self, other: &Self) -> Self {
        self.iter().filter(|el| other.contains(el)).collect()
    }

    /// Returns the difference `self` ∖ `other`.
    pub fn difference(&self, other: &Self) -> Self {
        self.iter().filter(|el| !other.contains(el)).collect()
    }

    /// Returns the union `self` ∪ `other`.
    pub fn union(&self, other: &Self) -> Self {
        self.iter().chain(other.iter()).collect()
    }
}

impl<T> CustomSet<T>
where
    T: Hash + Eq,
{
    /// Returns true, if the set contains `element`.
    pub fn contains(&self, element: &T) -> bool {
        if is_zst::<T>() {
            self.load > 0
        } else {
            !self.is_empty() && self.find(element)
        }
    }

    /// Adds an element to the set.
    pub fn add(&mut self, element: T) {
        if is_zst::<T>() {
            self.load = 1;
            return;
        }
        if self.contains(&element) {
            return;
        }
        if self.groups == 0 || self.load as f64 >= self.cap() as f64 * self.load_factor {
            self.grow();
            return self.add(element);
        }
        let (mut group, h2) = self.group_of(&element);
        unsafe {
            while group < self.groups {
                let g = self.ctrl_group(group);
                if let Some(slot) = g.empty().next() {
                    let idx = Idx { group, slot };
                    self.load += 1;
                    ptr::write(self.ctrl_at(idx), h2);
                    ptr::write(self.slot_at(idx), element);
                    return;
                }
                group = (group + 1) % self.groups;
            }
        }
    }

    /// Returns true if `self` ⊆ `other`.
    pub fn is_subset(&self, other: &Self) -> bool {
        self.is_empty() || self.iter().all(|el| other.contains(el))
    }

    /// Returns true if the set is empty.
    pub fn is_empty(&self) -> bool {
        self.load == 0
    }

    /// Returns true if `self` ∩ `other` == ∅.
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.iter().all(|el| !other.contains(el))
    }

    /// Probes the table for `element`, returning true if found.
    fn find(&self, element: &T) -> bool {
        let (mut group, h2) = self.group_of(element);
        while group < self.groups {
            unsafe {
                let g = self.ctrl_group(group);
                let h2_matches = g.matches(h2);
                for h2_match in h2_matches {
                    let h2_match = h2_match;
                    let idx = Idx {
                        group,
                        slot: h2_match,
                    };
                    if &*self.slot_at(idx) == element {
                        return true;
                    }
                }
                if g.matches_mask(Flag::Empty.into()) > 0 {
                    return false;
                }
                group = (group + 1) % self.groups
            }
        }
        false
    }

    /// Returns the index of `elements`' group.
    fn group_of(&self, element: &T) -> (usize, Ctrl) {
        let hash = self.hash(element);
        let (h1, h2) = (h1(hash), h2(hash));
        ((h1 % self.groups as u64) as usize, h2)
    }

    /// Returns the hash of `element`.
    fn hash(&self, element: &T) -> u64 {
        let mut state = self.hash_builder.build_hasher();
        element.hash(&mut state);
        state.finish()
    }

    /// Grows the arrays.
    ///
    /// If the set hasn't been allocated before, it allocates
    /// them with capacity for one group, otherwise increases
    /// the number of groups by 2.
    fn grow(&mut self) {
        assert!(!is_zst::<T>());
        unsafe {
            if self.groups == 0 {
                let groups = 1;
                let (slot, ctrl) = Self::allocate_groups(groups);
                self.slot = Unique::new_unchecked(slot);
                self.ctrl = Unique::new_unchecked(ctrl);
                self.groups = groups;
            } else {
                let old_groups = self.groups;
                let (old_slot_layout, old_ctrl_layout) = Self::layout(old_groups);
                let old_slot = self.slot();
                let old_ctrl = self.ctrl();
                let new_groups = old_groups * 2;

                assert!(
                    new_groups * (GROUP_SIZE) < isize::MAX as usize,
                    "capacity overflow"
                );

                let (new_slot, new_ctrl) = Self::allocate_groups(new_groups);
                self.groups = new_groups;
                self.slot = Unique::new_unchecked(new_slot);
                self.ctrl = Unique::new_unchecked(new_ctrl);

                let mut load = self.load;
                self.load = 0;

                for group in 0..old_groups {
                    if load == 0 {
                        break;
                    }

                    let g = Group(old_ctrl + Idx::group(group));
                    for slot in g.filled() {
                        let idx = Idx { group, slot };
                        self.add(ptr::read(old_slot + idx));
                        load -= 1;
                    }
                }

                Global.dealloc(NonNull::new_unchecked(old_slot).cast(), old_slot_layout);
                Global.dealloc(NonNull::new_unchecked(old_ctrl).cast(), old_ctrl_layout);
            };
        }
    }
}

impl<T> Drop for CustomSet<T> {
    fn drop(&mut self) {
        let (slot_layout, ctrl_layout) = Self::layout(self.groups);
        unsafe {
            Global.dealloc(NonNull::new_unchecked(self.slot()).cast(), slot_layout);
            Global.dealloc(NonNull::new_unchecked(self.ctrl()).cast(), ctrl_layout);
        }
    }
}

impl<T> FromIterator<T> for CustomSet<T>
where
    T: Hash + Eq,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let iter = iter.into_iter();
        let (lower, upper) = iter.size_hint();
        let mut set = CustomSet::with_capacity(2 * upper.unwrap_or(lower));
        for elem in iter {
            set.add(elem);
        }
        set
    }
}

impl<'set, T> FromIterator<&'set T> for CustomSet<T>
where
    T: Hash + Eq + Clone + 'set,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = &'set T>,
    {
        let iter = iter.into_iter();
        let (lower, upper) = iter.size_hint();
        let mut set = CustomSet::with_capacity(2 * upper.unwrap_or(lower));
        for elem in iter {
            set.add(elem.clone());
        }
        set
    }
}

struct CustomSetIter<'set, T> {
    load: usize,
    ctrl: *const Ctrl,
    slot: *const T,
    ctrl_match: group::MaskIter,
    _marker: PhantomData<&'set T>,
}

impl<'set, T> CustomSetIter<'set, T> {
    fn new(set: &'set CustomSet<T>) -> Self {
        let ctrl = set.ctrl();
        Self {
            load: set.load,
            ctrl,
            slot: set.slot(),
            ctrl_match: if set.groups == 0 {
                group::MaskIter(0)
            } else {
                group::MaskIter(Group(ctrl).filled_mask())
            },
            _marker: PhantomData,
        }
    }
}

impl<'set, T> Iterator for CustomSetIter<'set, T> {
    type Item = &'set T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.load == 0 {
            return None;
        }
        unsafe {
            if let Some(slot) = self.ctrl_match.next() {
                self.load -= 1;
                Some(&*(self.slot + Idx::slot(slot)))
            } else {
                self.ctrl = self.ctrl + Idx::group(1);
                self.slot = self.slot + Idx::group(1);
                self.ctrl_match = group::MaskIter(Group(self.ctrl).filled_mask());
                self.next()
            }
        }
    }
}

/// `Index` represents a position in the set,
/// namely the element in group `Index.group`,
/// in the slot `Index.slot`.
#[derive(Clone, Copy, Default, Debug)]
struct Idx {
    group: usize,
    slot: usize,
}

impl Idx {
    /// Return the absolute offset from the start
    /// of the array of this index.
    fn offset(self) -> usize {
        self.group * GROUP_SIZE + self.slot
    }

    /// Return the index of the first slot in
    /// group `group`.
    fn group(group: usize) -> Self {
        Idx { group, slot: 0 }
    }

    /// Return the index of the slot `slot` in
    /// the first group.
    fn slot(slot: usize) -> Self {
        debug_assert!(slot < GROUP_SIZE);
        Idx { group: 0, slot }
    }
}

impl<T> Add<Idx> for *const T {
    type Output = Self;
    fn add(self, rhs: Idx) -> Self::Output {
        unsafe { self.add(rhs.offset()) }
    }
}

impl<T> Add<Idx> for *mut T {
    type Output = Self;
    fn add(self, rhs: Idx) -> Self::Output {
        unsafe { self.add(rhs.offset()) }
    }
}

impl<T> PartialEq for CustomSet<T>
where
    T: Hash + Eq,
{
    fn eq(&self, other: &Self) -> bool {
        self.load == other.load && { self.is_subset(other) && other.is_subset(self) }
    }
}

impl<T> fmt::Debug for CustomSet<T>
where
    T: fmt::Debug + Hash + Eq + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let v: Vec<_> = self.iter().collect();
        write!(f, "{:?}", v)
    }
}
