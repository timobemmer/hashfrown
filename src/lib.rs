#![feature(allocator_api, ptr_internals)]

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

fn is_zst<T>() -> bool {
    mem::size_of::<T>() == 0
}

/// A simple hash set using linear probing.
///
/// Uses a default load factor of 0.5.
pub struct CustomSet<T> {
    buf: Unique<T>,
    ctrl: Unique<bool>,
    load_factor: f64,
    cap: usize,
    load: usize,
    hash_builder: RandomState,
}

impl<T> CustomSet<T> {
    /// Returns an empty set. Doesn't allocate.
    fn empty() -> Self {
        // if you're handling ZSTs, set the cap to usize::MAX,
        // so the set never grows.
        let cap = if mem::size_of::<T>() == 0 { !0 } else { 0 };
        Self {
            buf: Unique::dangling(),
            ctrl: Unique::dangling(),
            cap,
            load: 0,
            load_factor: 0.5,
            hash_builder: RandomState::new(),
        }
    }

    /// Returns a new set with the capacity specified.
    ///
    /// Doesn't allocate if `cap == 0`.
    fn with_capacity(cap: usize) -> Self {
        if cap == 0 {
            Self::empty()
        } else {
            unsafe {
                let (buf, ctrl) = Self::allocate(cap);
                Self {
                    buf: Unique::new_unchecked(buf),
                    ctrl: Unique::new_unchecked(ctrl),
                    cap,
                    load: 0,
                    load_factor: 0.5,
                    hash_builder: RandomState::new(),
                }
            }
        }
    }

    /// Return the raw pointer to the ctrl array.
    fn ctrl(&self) -> *mut bool {
        self.ctrl.as_ptr()
    }

    /// Return the raw pointer to the buf array.
    fn buf(&self) -> *mut T {
        self.buf.as_ptr()
    }

    /// Returns an iterator that visits all elements in
    /// the set in an arbitrary order.
    fn iter(&self) -> CustomSetIter<'_, T> {
        CustomSetIter::new(self)
    }

    /// Returns the ctrl array as a slice.
    fn _ctrl_slice(&self) -> &[bool] {
        assert!(!is_zst::<T>());
        unsafe { std::slice::from_raw_parts(self.ctrl(), self.cap) }
    }

    /// Returns the the layout of the buf array and the ctrl array.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let (buf_layout, ctrl_layout) = Self::layout(16);
    /// ```
    fn layout(cap: usize) -> (Layout, Layout) {
        (
            Layout::array::<T>(cap).unwrap(),
            Layout::array::<bool>(cap).unwrap(),
        )
    }

    /// Allocates the buf array and the ctrl array with a given
    /// capacity and returns pointers to them.
    ///
    /// Aborts if allocation fails.
    fn allocate(cap: usize) -> (*mut T, *mut bool) {
        let (buf_layout, ctrl_layout) = Self::layout(cap);

        let buf = match Global.alloc(buf_layout, AllocInit::Uninitialized) {
            Ok(block) => block.ptr.as_ptr(),
            Err(_) => handle_alloc_error(buf_layout),
        };
        let ctrl = match Global.alloc(ctrl_layout, AllocInit::Zeroed) {
            Ok(block) => block.ptr.as_ptr(),
            Err(_) => handle_alloc_error(ctrl_layout),
        };

        (buf as *mut _, ctrl as *mut _)
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
        !self.is_empty() && self.probe_for(element).is_ok()
    }

    /// Adds an element to the set.
    pub fn add(&mut self, element: T) {
        if is_zst::<T>() {
            self.load = 1;
            return;
        }
        if self.cap == 0 {
            self.grow();
        }
        match self.probe_for(&element) {
            Ok(_) => return,
            Err(idx) => {
                if (self.load + 1) as f64 > self.cap as f64 * self.load_factor {
                    self.grow();
                    return self.add(element);
                }
                unsafe {
                    ptr::write(self.ctrl().offset(idx), true);
                    ptr::write(self.buf().offset(idx), element);
                }
                self.load += 1;
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

    /// Returns true if `self.intersection(other).is_empty()`.
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.iter().all(|el| !other.contains(el))
    }

    /// Probes the table for the position of `element`. Returns
    /// `Ok(idx)` if `element` is in the set at `idx` or `Err(idx)`
    /// if `element` isn't in the set but can be inserted at `idx`.
    fn probe_for(&self, element: &T) -> Result<isize, isize> {
        assert!(self.cap > 0);
        let mut idx = self.index(element);
        unsafe {
            while ptr::read(self.ctrl().offset(idx)) {
                if self.buf().offset(idx).as_ref().unwrap() == element {
                    return Ok(idx);
                }
                idx = (idx + 1) % self.cap as isize;
            }
            Err(idx)
        }
    }

    /// Returns the index `element` would have in the set.
    fn index(&self, element: &T) -> isize {
        let hash = self.hash(element);
        (hash % self.cap as u64) as isize
    }

    /// Returns the hash of `element`.
    fn hash(&self, element: &T) -> u64 {
        let mut state = self.hash_builder.build_hasher();
        element.hash(&mut state);
        state.finish()
    }

    /// Grows the arrays.
    ///
    /// If the set hasn't been allocated before,
    /// it allocates them with capacity 2, otherwise grows by a factor
    /// of 2.
    fn grow(&mut self) {
        assert!(!is_zst::<T>());
        unsafe {
            if self.cap == 0 {
                let new_cap = 2;
                let (buf, ctrl) = Self::allocate(new_cap);
                self.buf = Unique::new_unchecked(buf);
                self.ctrl = Unique::new_unchecked(ctrl);
                self.cap = new_cap;
            } else {
                let old_cap = self.cap;
                let (old_buf_layout, old_ctrl_layout) = Self::layout(old_cap);
                let old_buf = self.buf();
                let old_ctrl = self.ctrl();

                let new_cap = old_cap * 2;
                let (new_buf, new_ctrl) = Self::allocate(new_cap);
                self.cap = new_cap;
                self.buf = Unique::new_unchecked(new_buf);
                self.ctrl = Unique::new_unchecked(new_ctrl);

                let mut load = self.load;
                for i in 0..old_cap as isize {
                    if load == 0 {
                        break;
                    }
                    if ptr::read(old_ctrl.offset(i)) {
                        let idx = self
                            .probe_for(old_buf.offset(i).as_ref().unwrap())
                            .unwrap_err();

                        ptr::write(new_ctrl.offset(idx), true);
                        ptr::copy_nonoverlapping(old_buf.offset(i), new_buf.offset(idx), 1);

                        load -= 1;
                    }
                }

                Global.dealloc(NonNull::new_unchecked(old_buf).cast(), old_buf_layout);
                Global.dealloc(NonNull::new_unchecked(old_ctrl).cast(), old_ctrl_layout);
            };
        }
    }
}

impl<T> Drop for CustomSet<T> {
    fn drop(&mut self) {
        if self.cap != 0 && mem::size_of::<T>() != 0 {
            unsafe {
                let buf: NonNull<_> = self.buf.into();
                let ctrl: NonNull<_> = self.ctrl.into();
                let (buf_layout, ctrl_layout) = Self::layout(self.cap);

                Global.dealloc(buf.cast(), buf_layout);
                Global.dealloc(ctrl.cast(), ctrl_layout);
            }
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for CustomSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c: Vec<_> = self.iter().collect();
        write!(f, "{:?}", c)
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
        for el in iter {
            set.add(el);
        }
        set
    }
}

impl<'s, T> FromIterator<&'s T> for CustomSet<T>
where
    T: Hash + Eq + Clone + 's,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = &'s T>,
    {
        let iter = iter.into_iter();
        let (lower, upper) = iter.size_hint();
        let mut set = CustomSet::with_capacity(2 * upper.unwrap_or(lower));
        for el in iter {
            set.add(el.clone());
        }
        set
    }
}

struct CustomSetIter<'s, T> {
    ctrl: *const bool,
    buf: *const T,
    load: usize,
    _marker: PhantomData<&'s T>,
}

impl<'s, T> CustomSetIter<'s, T> {
    fn new(set: &'s CustomSet<T>) -> Self {
        Self {
            ctrl: set.ctrl(),
            buf: set.buf(),
            load: set.load,
            _marker: PhantomData,
        }
    }

    fn offset(&mut self) {
        unsafe {
            self.ctrl = self.ctrl.offset(1);
            self.buf = self.buf.offset(1);
        }
    }
}

impl<'s, T> Iterator for CustomSetIter<'s, T> {
    type Item = &'s T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.load == 0 {
            return None;
        }
        unsafe {
            if mem::size_of::<T>() == 0 {
                let el = self.buf.as_ref().unwrap();
                self.load -= 1;
                Some(el)
            } else {
                while !ptr::read(self.ctrl) {
                    self.offset();
                }
                let el = self.buf.as_ref().unwrap();
                self.load -= 1;
                self.offset();
                Some(el)
            }
        }
    }
}

impl<T> PartialEq for CustomSet<T>
where
    T: Eq + Hash,
{
    fn eq(&self, other: &Self) -> bool {
        self.is_subset(other) && other.is_subset(self)
    }
}
