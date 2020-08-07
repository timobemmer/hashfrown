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
    groups: isize,
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
                let (buf, ctrl) = Self::allocate_groups(groups);
                Self {
                    slot: Unique::new_unchecked(buf),
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
    fn slot_at(&self, idx: Index) -> *mut T {
        self.slot() + idx
    }

    /// Return a raw pointer to the ctrl at `idx`.
    fn ctrl_at(&self, idx: Index) -> *mut Ctrl {
        self.ctrl() + idx
    }

    /// Return the `group`th group of ctrls.
    fn ctrl_group(&self, group: isize) -> Group {
        unsafe { Group(self.ctrl().offset(group * GROUP_SIZE as isize)) }
    }

    /// Returns the the layout of the buf array and the ctrl array.
    fn layout(groups: isize) -> (Layout, Layout) {
        (
            Layout::array::<T>(groups as usize * GROUP_SIZE).unwrap(),
            Layout::array::<Ctrl>(groups as usize * GROUP_SIZE).unwrap(),
        )
    }

    /// Allocates enough memory to hold `groups` groups of elements
    /// and control bytes. Sets all control bytes to [Flag::Empty](ctrl::Flag::Empty).
    fn allocate_groups(groups: isize) -> (*mut T, *mut Ctrl) {
        let (buf_layout, ctrl_layout) = Self::layout(groups);

        let buf = match Global.alloc(buf_layout, AllocInit::Uninitialized) {
            Ok(block) => block.ptr.as_ptr(),
            Err(_) => handle_alloc_error(buf_layout),
        };
        let ctrl = match Global.alloc(ctrl_layout, AllocInit::Zeroed) {
            Ok(block) => block.ptr.as_ptr(),
            Err(_) => handle_alloc_error(ctrl_layout),
        } as *mut Ctrl;

        unsafe {
            ptr::write_bytes(ctrl, Flag::Empty as u8, groups as usize * GROUP_SIZE);
        }

        (buf as *mut _, ctrl)
    }

    /// Returns the set's capacity for elements. Only used
    /// to calculate when to grow the buffer.
    fn cap(&self) -> isize {
        assert!(!is_zst::<T>());
        self.groups * GROUP_SIZE as isize
    }

    /// Calculates the minimum number of groups need to hold
    /// `cap` elements.
    fn groups_from_cap(cap: usize) -> isize {
        (cap / GROUP_SIZE) as isize + (cap % GROUP_SIZE != 0) as isize
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
        (is_zst::<T>() && self.load > 0) || (!self.is_empty() && self.find(element))
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
                if let Some(slot) = g.matches(Ctrl::from(Flag::Empty)).next() {
                    let idx = Index { group, slot };
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
                    let h2_match = dbg!(h2_match);
                    let idx = Index {
                        group,
                        slot: h2_match,
                    };
                    if self.slot_at(idx).as_ref().unwrap() == element {
                        return true;
                    }
                }
                if g.matches_mask(Flag::Empty.into()) > 0 {
                    return false;
                }
                group = (group + 1) % self.groups as isize
            }
        }
        false
    }

    /// Returns the index of `elements`' group.
    fn group_of(&self, element: &T) -> (isize, Ctrl) {
        let hash = self.hash(element);
        let (h1, h2) = (h1(hash), h2(hash));
        ((h1 % self.groups as u64) as isize, h2)
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
                let (buf, ctrl) = Self::allocate_groups(groups);
                self.slot = Unique::new_unchecked(buf);
                self.ctrl = Unique::new_unchecked(ctrl);
                self.groups = groups;
            } else {
                let old_groups = self.groups;
                let (old_buf_layout, old_ctrl_layout) = Self::layout(old_groups);
                let old_buf = self.slot();
                let old_ctrl = self.ctrl();

                let new_groups = old_groups * 2;

                assert!(
                    new_groups * (GROUP_SIZE as isize) < isize::MAX,
                    "capacity overflow"
                );

                let (new_buf, new_ctrl) = Self::allocate_groups(new_groups);
                self.groups = new_groups;
                self.slot = Unique::new_unchecked(new_buf);
                self.ctrl = Unique::new_unchecked(new_ctrl);

                let mut load = self.load;
                self.load = 0;

                for group in 0..old_groups as isize {
                    if load == 0 {
                        break;
                    }

                    let g = Group(old_ctrl.offset(group * GROUP_SIZE as isize));
                    for slot in g.filled() {
                        let idx = Index { group, slot };
                        self.add(ptr::read(self.slot_at(idx)));
                        load -= 1;
                    }
                }

                Global.dealloc(NonNull::new_unchecked(old_buf).cast(), old_buf_layout);
                Global.dealloc(NonNull::new_unchecked(old_ctrl).cast(), old_ctrl_layout);
            };
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
        let mut set = CustomSet::with_capacity(upper.unwrap_or(lower));
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
    idx: Index,
    ctrl: *const Ctrl,
    buf: *const T,
    ctrl_match: u32,
    _marker: PhantomData<&'set T>,
}

impl<'set, T> CustomSetIter<'set, T> {
    fn new(set: &'set CustomSet<T>) -> Self {
        let ctrl = set.ctrl();
        Self {
            load: set.load,
            idx: Index::default(),
            ctrl,
            buf: set.slot(),
            ctrl_match: if set.groups == 0 {
                0
            } else {
                Group(ctrl).filled_mask()
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
            if is_zst::<T>() {
                self.load = 0;
                return Some(self.buf.as_ref().unwrap());
            }
            let idx = &mut self.idx;
            while self.ctrl_match & 1 == 0 {
                if self.ctrl_match == 0 {
                    self.ctrl = self.ctrl.offset(GROUP_SIZE as isize);
                    self.ctrl_match = Group(self.ctrl).filled_mask();
                    idx.group += 1;
                    idx.slot = 0;
                }
                self.ctrl_match >>= 1;
                idx.slot += 1;
            }
            self.load -= 1;

            let el = (self.buf + *idx).as_ref().unwrap();
            idx.slot += 1;
            Some(el)
        }
    }
}

/// `Index` represents a position in the set,
/// namely the element in group `Index.group`,
/// in the slot `Index.slot`.
#[derive(Clone, Copy, Default, Debug)]
struct Index {
    group: isize,
    slot: isize,
}

impl Index {
    /// Return the absolute offset from the start
    /// of the array of this index.
    fn offset(self) -> isize {
        self.group * GROUP_SIZE as isize + self.slot
    }
}

impl<T> std::ops::Add<Index> for *const T {
    type Output = Self;
    fn add(self, rhs: Index) -> Self::Output {
        unsafe { self.offset(rhs.offset()) }
    }
}

impl<T> std::ops::Add<Index> for *mut T {
    type Output = Self;
    fn add(self, rhs: Index) -> Self::Output {
        unsafe { self.offset(rhs.offset()) }
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
