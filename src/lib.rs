#![feature(allocator_api, ptr_internals)]

use std::{fmt, hash::Hash, iter::FromIterator};

mod raw;

/// A very simple, probably incorrect implementation
/// of Google's swiss map based on [this talk](https://youtu.be/ncHmEUmJZf4).
pub struct CustomSet<T> {
    map: raw::HashMap<T, ()>,
}

impl<T> CustomSet<T> {
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            map: raw::HashMap::with_capacity(cap),
        }
    }

    fn iter(&self) -> raw::Keys<'_, T, ()> {
        self.map.keys()
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
        let mut set = Self::with_capacity(2 * input.len());
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
        self.map.contains(element)
    }

    /// Adds an element to the set.
    pub fn add(&mut self, element: T) {
        self.map.insert(element, ());
    }

    /// Returns true if `self` ⊆ `other`.
    pub fn is_subset(&self, other: &Self) -> bool {
        self.is_empty() || self.iter().all(|el| other.contains(el))
    }

    /// Returns true if the set is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns true if `self` ∩ `other` == ∅.
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.iter().all(|el| !other.contains(el))
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

impl<T> PartialEq for CustomSet<T>
where
    T: Hash + Eq,
{
    fn eq(&self, other: &Self) -> bool {
        self.is_subset(other) && other.is_subset(self)
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
