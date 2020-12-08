use ctrl::{Ctrl, Flag};
use group::{Group, SIZE as GROUP_SIZE};
use std::{
    alloc::{handle_alloc_error, AllocInit, AllocRef, Global, Layout},
    collections::hash_map::RandomState,
    fmt,
    hash::{BuildHasher, Hash, Hasher},
    marker::PhantomData,
    mem,
    ops::Add,
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
pub struct HashMap<K, V> {
    slot: Unique<(K, V)>,
    ctrl: Unique<Ctrl>,
    load_factor: f64,
    load: usize,
    groups: usize,
    hash_builder: RandomState,
}

impl<K, V> HashMap<K, V> {
    /// Returns an empty set. Doesn't allocate.
    pub(super) fn empty() -> Self {
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
    pub(super) fn with_capacity(cap: usize) -> Self {
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
    fn slot(&self) -> *mut (K, V) {
        self.slot.as_ptr()
    }

    /// Return a raw pointer to the slot at `idx`.
    fn slot_at(&self, idx: Idx) -> *mut (K, V) {
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
            Layout::array::<(K, V)>(groups * GROUP_SIZE).unwrap(),
            Layout::array::<Ctrl>(groups * GROUP_SIZE).unwrap(),
        )
    }

    /// Allocates enough memory to hold `groups` groups of key-value pairs
    /// and control bytes. Sets all control bytes to [Flag::Empty](ctrl::Flag::Empty).
    fn allocate_groups(groups: usize) -> (*mut (K, V), *mut Ctrl) {
        let (slot_layout, ctrl_layout) = Self::layout(groups);

        let slot = match Global.alloc(slot_layout, AllocInit::Uninitialized) {
            Ok(block) => block.ptr.as_ptr(),
            Err(_) => handle_alloc_error(slot_layout),
        } as *mut (K, V);
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

    /// Allocates exactly enough memory to hold one key-value pair.
    ///
    /// # Safety
    ///
    /// This is marked as unsafe because, while the map will think that it
    /// has a whole group allocated, it only owns enough memory for exactly
    /// one key-value pair. The caller has to ensure that when this function
    /// is used to allocate, no pointer beyond `self.ctrl`/`self.slot` is
    /// ever accessed.
    unsafe fn allocate_zst() -> (*mut (K, V), *mut Ctrl) {
        let (slot_layout, ctrl_layout) = (Layout::new::<(K, V)>(), Layout::new::<Ctrl>());

        let slot = match Global.alloc(slot_layout, AllocInit::Uninitialized) {
            Ok(block) => block.ptr.as_ptr(),
            Err(_) => handle_alloc_error(slot_layout),
        } as *mut (K, V);

        let ctrl = match Global.alloc(ctrl_layout, AllocInit::Uninitialized) {
            Ok(block) => block.ptr.as_ptr(),
            Err(_) => handle_alloc_error(ctrl_layout),
        } as *mut Ctrl;

        ptr::write(ctrl, Flag::Empty.into());

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

    /// Returns the set's capacity for key-value pairs. Only used
    /// to calculate when to grow the buffer.
    fn cap(&self) -> usize {
        // assert!(!is_zst::<K>() && !is_zst::<V>());
        self.groups * GROUP_SIZE
    }

    /// Calculates the minimum number of groups needed to hold
    /// `cap` key-value pairs.
    fn groups_from_cap(cap: usize) -> usize {
        (cap / GROUP_SIZE) + (cap % GROUP_SIZE != 0) as usize
    }

    pub(super) fn iter(&self) -> Iter<'_, K, V> {
        Iter::new(self)
    }

    pub(super) fn keys(&self) -> Keys<'_, K, V> {
        Keys {
            iter: Iter::new(self),
        }
    }

    pub(super) fn values(&self) -> Values<'_, K, V> {
        Values {
            iter: Iter::new(self),
        }
    }
}

impl<K, V> HashMap<K, V>
where
    K: Hash + Eq,
{
    pub(super) fn get_key_value(&self, key: &K) -> Option<&(K, V)> {
        unsafe { self.find(key).map(|idx| &*self.slot_at(idx)) }
    }

    pub(super) fn get(&mut self, key: &K) -> Option<&V> {
        self.get_key_value(key).map(|kv| &kv.1)
    }

    /// Returns true, if the set contains `element`.
    pub(super) fn contains(&self, key: &K) -> bool {
        !self.is_empty() && (is_zst::<K>() || self.find(key).is_some())
    }

    /// Adds an element to the set.
    pub(super) fn insert(&mut self, key: K, value: V) {
        if is_zst::<K>() && is_zst::<V>() {
            self.load = 1;
            return;
        }
        if self.groups == 0 {
            self.grow();
            return self.insert(key, value);
        }
        let (mut group, h2) = self.group_of(&key);
        if let Some(idx) = self.find(&key) {
            unsafe {
                ptr::write(self.ctrl_at(idx), h2);
                ptr::write(self.slot_at(idx), (key, value));
            }
        } else {
            if self.load as f64 >= self.cap() as f64 * self.load_factor {
                self.grow();
                return self.insert(key, value);
            }
            unsafe {
                if is_zst::<K>() {
                    self.load += 1;
                    ptr::write(self.ctrl(), 0u8.into());
                    ptr::write(self.slot(), (key, value));
                } else {
                    while group < self.groups {
                        let g = self.ctrl_group(group);
                        if let Some(slot) = g.empty().next() {
                            let idx = Idx { group, slot };
                            self.load += 1;
                            ptr::write(self.ctrl_at(idx), h2);
                            ptr::write(self.slot_at(idx), (key, value));
                            return;
                        }
                        group = (group + 1) % self.groups;
                    }
                }
            }
        }
    }

    /// Returns true if the set is empty.
    pub(super) fn is_empty(&self) -> bool {
        self.load == 0
    }

    /// Probes the table for `key`, returning true if found.
    fn find(&self, key: &K) -> Option<Idx> {
        if self.groups == 0 {
            return None;
        }
        if is_zst::<K>() {
            let idx = Idx { group: 0, slot: 0 };
            unsafe {
                let c = *self.ctrl_at(idx);
                if c.h2 & 0x80 == 0 {
                    Some(idx)
                } else {
                    None
                }
            }
        } else {
            let (mut group, h2) = self.group_of(key);
            while group < self.groups {
                unsafe {
                    let g = self.ctrl_group(group);
                    for h2_match in g.matches(h2) {
                        let h2_match = h2_match;
                        let idx = Idx {
                            group,
                            slot: h2_match,
                        };
                        if &(*self.slot_at(idx)).0 == key {
                            return Some(idx);
                        }
                    }
                    if g.matches_mask(Flag::Empty.into()) > 0 {
                        return None;
                    }
                    group = (group + 1) % self.groups
                }
            }
            None
        }
    }

    /// Returns `key`'s h2 hash and the index of its group.
    fn group_of(&self, key: &K) -> (usize, Ctrl) {
        let hash = self.hash(key);
        let (h1, h2) = (h1(hash), h2(hash));
        ((h1 % self.groups as u64) as usize, h2)
    }

    /// Returns the hash of `key`.
    fn hash(&self, key: &K) -> u64 {
        let mut state = self.hash_builder.build_hasher();
        key.hash(&mut state);
        state.finish()
    }

    /// Grows the arrays.
    ///
    /// If the set hasn't been allocated before, it allocates
    /// them with capacity for one group, otherwise increases
    /// the number of groups by a factor of 2.
    fn grow(&mut self) {
        unsafe {
            if self.groups == 0 {
                let groups = 1;
                let (slot, ctrl) = if is_zst::<K>() {
                    // SAFETY: This is safe because `find` and
                    // `insert` take special care to handle ZSTs
                    // correctly.
                    Self::allocate_zst()
                } else {
                    Self::allocate_groups(groups)
                };
                self.slot = Unique::new_unchecked(slot);
                self.ctrl = Unique::new_unchecked(ctrl);
                self.groups = groups;
            } else {
                debug_assert!(!is_zst::<K>());
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
                        let (k, v) = ptr::read(old_slot + idx);
                        self.insert(k, v);
                        load -= 1;
                    }
                }

                Global.dealloc(NonNull::new_unchecked(old_slot).cast(), old_slot_layout);
                Global.dealloc(NonNull::new_unchecked(old_ctrl).cast(), old_ctrl_layout);
            };
        }
    }
}

impl<K, V> Drop for HashMap<K, V> {
    fn drop(&mut self) {
        let (slot_layout, ctrl_layout) = Self::layout(self.groups);
        unsafe {
            Global.dealloc(NonNull::new_unchecked(self.slot()).cast(), slot_layout);
            Global.dealloc(NonNull::new_unchecked(self.ctrl()).cast(), ctrl_layout);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_and_get() {
        let mut rawmap = HashMap::empty();
        rawmap.insert(0, "hello");
        rawmap.insert(1, ", world!");

        assert_eq!(rawmap.get(&0), Some(&"hello"));
        assert_eq!(rawmap.get(&1), Some(&", world!"));
    }

    #[test]
    fn overwrite() {
        let mut rawmap = HashMap::empty();
        rawmap.insert(0, "goodbye");
        rawmap.insert(1, ", world!");
        rawmap.insert(0, "hello");

        assert_eq!(rawmap.get(&0), Some(&"hello"));
        assert_eq!(rawmap.get(&1), Some(&", world!"));
    }

    #[test]
    fn zst_key() {
        let mut rawmap = HashMap::empty();
        rawmap.insert((), 1);
        assert_eq!(rawmap.get(&()), Some(&1));

        rawmap.insert((), 2);
        assert_eq!(rawmap.get(&()), Some(&2));
    }

    #[test]
    fn zst_value() {
        let mut rawmap = HashMap::empty();
        rawmap.insert(0, ());
        assert_eq!(rawmap.get(&0), Some(&()));
        rawmap.insert(1, ());
        assert_eq!(rawmap.get(&1), Some(&()));
        rawmap.insert(2, ());
        assert_eq!(rawmap.get(&2), Some(&()));
    }

    #[test]
    fn iter() {
        let mut rawmap = HashMap::empty();

        rawmap.insert(0, "hello");
        rawmap.insert(1, ", world!");

        for k in rawmap.keys() {
            assert!(k == &0 || k == &1);
        }

        for v in rawmap.values() {
            assert!(v == &"hello" || v == &", world!");
        }

        let mut iter = rawmap.iter();

        let next = iter.next();
        assert!(next == Some(&(0, "hello")) || next == Some(&(1, ", world!")));
        let next = iter.next();
        assert!(next == Some(&(0, "hello")) || next == Some(&(1, ", world!")));
        assert_eq!(iter.next(), None);
    }
}

pub struct Iter<'map, K, V> {
    load: usize,
    ctrl: *const Ctrl,
    slot: *const (K, V),
    ctrl_match: group::MaskIter,
    _marker: PhantomData<&'map (K, V)>,
}

impl<'map, K, V> Iter<'map, K, V> {
    fn new(map: &'map HashMap<K, V>) -> Self {
        let ctrl = map.ctrl();
        Iter {
            load: map.load,
            ctrl,
            slot: map.slot(),
            ctrl_match: if map.groups == 0 {
                group::MaskIter(0)
            } else if is_zst::<K>() {
                group::MaskIter(1)
            } else {
                group::MaskIter(Group(ctrl).filled_mask())
            },
            _marker: PhantomData,
        }
    }
}

impl<'map, K, V> Iterator for Iter<'map, K, V> {
    type Item = &'map (K, V);

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

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.load, Some(self.load))
    }
}

pub struct Keys<'map, K, V> {
    iter: Iter<'map, K, V>,
}

impl<'map, K, V> Iterator for Keys<'map, K, V> {
    type Item = &'map K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|kv| &kv.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

pub struct Values<'map, K, V> {
    iter: Iter<'map, K, V>,
}

impl<'map, K, V> Iterator for Values<'map, K, V> {
    type Item = &'map V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|kv| &kv.1)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
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

impl<K, V> fmt::Debug for HashMap<K, V>
where
    K: fmt::Debug + Hash + Eq + Clone,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "HashMap {{")?;
        for (k, v) in self.iter() {
            write!(f, "\n\t{:?}: {:?}", k, v)?;
        }
        write!(f, "}}")
    }
}
