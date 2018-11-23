//! Contains the sparse secondary map implementation.

use super::{is_older_version, Key, KeyData};
use std;
use std::collections::hash_map::{self, HashMap};
#[cfg(feature = "unstable")]
use std::collections::CollectionAllocErr;
use std::iter::{Extend, FromIterator, FusedIterator};
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

#[derive(Debug)]
struct Slot<T> {
    version: u32,
    value: T,
}

/// Sparse secondary map, associate data with previously stored elements in a
/// slot map.
///
/// A `SparseSecondaryMap` allows you to efficiently store additional
/// information for each element in a slot map. You can have multiple secondary
/// maps per slot map, but not multiple slot maps per secondary map. It is safe
/// but unspecified behavior if you use keys from multiple different slot maps
/// in the same `SparseSecondaryMap`.
///
/// A `SparseSecondaryMap` does not leak memory even if you never remove
/// elements. In return, when you remove a key from the primary slot map, after
/// any insert the space associated with the removed element may be reclaimed.
/// Don't expect the values associated with a removed key to stick around after
/// an insertion has happened!
///
/// Unlike a [`SlotMap`], a `SparseSecondaryMap`s elements do not need to be
/// [`Slottable`]. This means that if you can't or don't want to use nightly
/// Rust, and your data is not [`Slottable`], you can store that data as
/// secondary data.
///
/// Unlike [`SecondaryMap`], the `SparseSecondaryMap` is backed by a
/// [`HashMap`]. This means its access times are higher, but it uses less memory
/// and iterates faster if there are only a few elements of the slot map in the
/// secondary map. If most or all of the elements in a slot map are also found
/// in the secondary map, use a [`SecondaryMap`] instead.
///
/// [`SlotMap`]: ../struct.SlotMap.html
/// [`Slottable`]: ../trait.Slottable.html
/// [`SecondaryMap`]: ../secondary/struct.SecondaryMap.html
/// [`HashMap`]: https://doc.rust-lang.org/std/collections/struct.HashMap.html
///
/// Example usage:
///
/// ```
/// # use slotmap::*;
/// // Nightly Rust needed to store String which is not Copy.
/// let mut players: SlotMap<_, &'static str> = SlotMap::new();
/// // But not for secondary maps.
/// let mut nicks: SparseSecondaryMap<_, String> = SparseSecondaryMap::new();
/// let mut health = SparseSecondaryMap::new();
/// let mut ammo = SparseSecondaryMap::new();
///
/// let alice = players.insert("alice");
/// nicks.insert(alice, "the_dragon1".to_string());
/// let bob = players.insert("bob");
/// nicks.insert(bob, "bobby_".to_string());
///
/// for p in players.keys() {
///     health.insert(p, 100);
///     ammo.insert(p, 30);
/// }
///
/// // Alice attacks Bob with all her ammo!
/// health[bob] -= ammo[alice] * 3;
/// ammo[alice] = 0;
/// ```

#[derive(Debug)]
pub struct SparseSecondaryMap<K: Key, V> {
    slots: HashMap<u32, Slot<V>>,
    _k: PhantomData<fn(K) -> K>,
}

impl<K: Key, V> SparseSecondaryMap<K, V> {
    /// Constructs a new, empty `SparseSecondaryMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sec: SparseSecondaryMap<DefaultKey, i32> = SparseSecondaryMap::new();
    /// ```
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Creates an empty `SparseSecondaryMap` with the given capacity of slots.
    ///
    /// The secondary map will not reallocate until it holds at least `capacity`
    /// slots.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm: SlotMap<_, i32> = SlotMap::with_capacity(10);
    /// let mut sec: SparseSecondaryMap<DefaultKey, i32> =
    ///     SparseSecondaryMap::with_capacity(sm.capacity());
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            slots: HashMap::with_capacity(capacity),
            _k: PhantomData,
        }
    }

    /// Returns the number of elements in the secondary map.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let k = sm.insert(4);
    /// let mut squared = SparseSecondaryMap::new();
    /// assert_eq!(squared.len(), 0);
    /// squared.insert(k, 16);
    /// assert_eq!(squared.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.slots.len()
    }

    /// Returns if the secondary map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sec: SparseSecondaryMap<DefaultKey, i32> = SparseSecondaryMap::new();
    /// assert!(sec.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }

    /// Returns the number of elements the `SparseSecondaryMap` can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sec: SparseSecondaryMap<DefaultKey, i32> = SparseSecondaryMap::with_capacity(10);
    /// assert!(sec.capacity() >= 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.slots.capacity()
    }

    /// Reserves capacity for at least `additional` more slots in the
    /// `SparseSecondaryMap`. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sec: SparseSecondaryMap<DefaultKey, i32> = SparseSecondaryMap::with_capacity(10);
    /// assert!(sec.capacity() >= 10);
    /// sec.reserve(10);
    /// assert!(sec.capacity() >= 20);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.slots.reserve(additional);
    }

    /// Tries to reserve capacity for at least `additional` more slots in the
    /// `SparseSecondaryMap`.  The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sec: SparseSecondaryMap<DefaultKey, i32> = SparseSecondaryMap::with_capacity(10);
    /// assert!(sec.capacity() >= 10);
    /// sec.try_reserve(10).unwrap();
    /// assert!(sec.capacity() >= 20);
    /// ```
    #[cfg(feature = "unstable")]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), CollectionAllocErr> {
        self.slots.try_reserve(additional)
    }

    /// Returns `true` if the secondary map contains `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let k = sm.insert(4);
    /// let mut squared = SparseSecondaryMap::new();
    /// assert!(!squared.contains_key(k));
    /// squared.insert(k, 16);
    /// assert!(squared.contains_key(k));
    /// ```
    pub fn contains_key(&self, key: K) -> bool {
        let key = key.into();
        self.slots
            .get(&key.idx)
            .map_or(false, |slot| slot.version == key.version.get())
    }

    /// Inserts a value into the secondary map at the given `key`. Can silently
    /// fail if `key` was removed from the originating slot map.
    ///
    /// Returns `None` if this key was not present in the map, the old value
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let k = sm.insert(4);
    /// let mut squared = SparseSecondaryMap::new();
    /// assert_eq!(squared.insert(k, 0), None);
    /// assert_eq!(squared.insert(k, 4), Some(0));
    /// // You don't have to use insert if the key is already in the secondary map.
    /// squared[k] *= squared[k];
    /// assert_eq!(squared[k], 16);
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let key = key.into();

        if let Some(slot) = self.slots.get_mut(&key.idx) {
            if slot.version == key.version.get() {
                return Some(std::mem::replace(&mut slot.value, value));
            }

            // Don't replace existing newer values.
            if is_older_version(key.version.get(), slot.version) {
                return None;
            }

            *slot = Slot {
                version: key.version.get(),
                value,
            };

            return None;
        }

        self.slots.insert(
            key.idx,
            Slot {
                version: key.version.get(),
                value,
            },
        );

        None
    }

    /// Removes a key from the secondary map, returning the value at the key if
    /// the key was not previously removed. If `key` was removed from the
    /// originating slot map, its corresponding entry in the secondary map may
    /// or may not already be removed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let mut squared = SparseSecondaryMap::new();
    /// let k = sm.insert(4);
    /// squared.insert(k, 16);
    /// squared.remove(k);
    /// assert!(!squared.contains_key(k));
    ///
    /// // It's not necessary to remove keys deleted from the primary slot map, they
    /// // get deleted automatically when their slots are reused on a subsequent insert.
    /// squared.insert(k, 16);
    /// sm.remove(k); // Remove k from the slot map, making an empty slot.
    /// let new_k = sm.insert(2); // Since sm only has one empty slot, this reuses it.
    /// assert!(!squared.contains_key(new_k)); // Space reuse does not mean equal keys.
    /// assert!(squared.contains_key(k)); // Slot has not been reused in squared yet.
    /// squared.insert(new_k, 4);
    /// assert!(!squared.contains_key(k)); // Old key is no longer available.
    /// ```
    pub fn remove(&mut self, key: K) -> Option<V> {
        let key = key.into();

        if let hash_map::Entry::Occupied(entry) = self.slots.entry(key.idx) {
            if entry.get().version == key.version.get() {
                return Some(entry.remove_entry().1.value);
            }
        }

        None
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all key-value pairs `(k, v)` such that
    /// `f(k, &mut v)` returns false. This method invalidates any removed keys.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let mut sec = SparseSecondaryMap::new();
    ///
    /// let k1 = sm.insert(0); sec.insert(k1, 10);
    /// let k2 = sm.insert(1); sec.insert(k2, 11);
    /// let k3 = sm.insert(2); sec.insert(k3, 12);
    ///
    /// sec.retain(|key, val| key == k1 || *val == 11);
    ///
    /// assert!(sec.contains_key(k1));
    /// assert!(sec.contains_key(k2));
    /// assert!(!sec.contains_key(k3));
    ///
    /// assert_eq!(2, sec.len());
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(K, &mut V) -> bool,
    {
        self.slots.retain(|&idx, slot| {
            let key = KeyData::new(idx, slot.version);
            f(key.into(), &mut slot.value)
        })
    }

    /// Clears the secondary map. Keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let mut sec = SparseSecondaryMap::new();
    /// for i in 0..10 {
    ///     sec.insert(sm.insert(i), i);
    /// }
    /// assert_eq!(sec.len(), 10);
    /// sec.clear();
    /// assert_eq!(sec.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.slots.clear();
    }

    /// Clears the slot map, returning all key-value pairs in arbitrary order as
    /// an iterator. Keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// # use std::iter::FromIterator;
    /// let mut sm = SlotMap::new();
    /// let k = sm.insert(0);
    /// let mut sec = SparseSecondaryMap::new();
    /// sec.insert(k, 1);
    /// let v: Vec<_> = sec.drain().collect();
    /// assert_eq!(sec.len(), 0);
    /// assert_eq!(v, vec![(k, 1)]);
    /// ```
    pub fn drain(&mut self) -> Drain<K, V> {
        Drain {
            inner: self.slots.drain(),
            _k: PhantomData,
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert("foo");
    /// let mut sec = SparseSecondaryMap::new();
    /// sec.insert(key, "bar");
    /// assert_eq!(sec.get(key), Some(&"bar"));
    /// sec.remove(key);
    /// assert_eq!(sec.get(key), None);
    /// ```
    pub fn get(&self, key: K) -> Option<&V> {
        let key = key.into();
        self.slots
            .get(&key.idx)
            .filter(|slot| slot.version == key.version.get())
            .map(|slot| &slot.value)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert("test");
    /// let mut sec = SparseSecondaryMap::new();
    /// sec.insert(key, 3.5);
    /// if let Some(x) = sec.get_mut(key) {
    ///     *x += 3.0;
    /// }
    /// assert_eq!(sec[key], 6.5);
    /// ```
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        let key = key.into();
        self.slots
            .get_mut(&key.idx)
            .filter(|slot| slot.version == key.version.get())
            .map(|slot| &mut slot.value)
    }

    /// An iterator visiting all key-value pairs in arbitrary order. The
    /// iterator element type is `(K, &'a V)`.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let mut sec = SparseSecondaryMap::new();
    /// let k0 = sm.insert(0); sec.insert(k0, 10);
    /// let k1 = sm.insert(1); sec.insert(k1, 11);
    /// let k2 = sm.insert(2); sec.insert(k2, 12);
    ///
    /// for (k, v) in sec.iter() {
    ///     println!("key: {:?}, val: {}", k, v);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            inner: self.slots.iter(),
            _k: PhantomData,
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order, with
    /// mutable references to the values. The iterator element type is
    /// `(K, &'a mut V)`.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let mut sec = SparseSecondaryMap::new();
    /// let k0 = sm.insert(1); sec.insert(k0, 10);
    /// let k1 = sm.insert(2); sec.insert(k1, 20);
    /// let k2 = sm.insert(3); sec.insert(k2, 30);
    ///
    /// for (k, v) in sec.iter_mut() {
    ///     if k != k1 {
    ///         *v *= -1;
    ///     }
    /// }
    ///
    /// assert_eq!(sec[k0], -10);
    /// assert_eq!(sec[k1], 20);
    /// assert_eq!(sec[k2], -30);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            inner: self.slots.iter_mut(),
            _k: PhantomData,
        }
    }

    /// An iterator visiting all keys in arbitrary order. The iterator element
    /// type is `K`.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// # use std::collections::HashSet;
    /// let mut sm = SlotMap::new();
    /// let mut sec = SparseSecondaryMap::new();
    /// let k0 = sm.insert(1); sec.insert(k0, 10);
    /// let k1 = sm.insert(2); sec.insert(k1, 20);
    /// let k2 = sm.insert(3); sec.insert(k2, 30);
    /// let keys: HashSet<_> = sec.keys().collect();
    /// let check: HashSet<_> = vec![k0, k1, k2].into_iter().collect();
    /// assert_eq!(keys, check);
    /// ```
    pub fn keys(&self) -> Keys<K, V> {
        Keys { inner: self.iter() }
    }

    /// An iterator visiting all values in arbitrary order. The iterator element
    /// type is `&'a V`.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// # use std::collections::HashSet;
    /// let mut sm = SlotMap::new();
    /// let mut sec = SparseSecondaryMap::new();
    /// let k0 = sm.insert(1); sec.insert(k0, 10);
    /// let k1 = sm.insert(2); sec.insert(k1, 20);
    /// let k2 = sm.insert(3); sec.insert(k2, 30);
    /// let values: HashSet<_> = sec.values().collect();
    /// let check: HashSet<_> = vec![&10, &20, &30].into_iter().collect();
    /// assert_eq!(values, check);
    /// ```
    pub fn values(&self) -> Values<K, V> {
        Values { inner: self.iter() }
    }

    /// An iterator visiting all values mutably in arbitrary order. The iterator
    /// element type is `&'a mut V`.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// # use std::collections::HashSet;
    /// let mut sm = SlotMap::new();
    /// let mut sec = SparseSecondaryMap::new();
    /// sec.insert(sm.insert(1), 10);
    /// sec.insert(sm.insert(2), 20);
    /// sec.insert(sm.insert(3), 30);
    /// sec.values_mut().for_each(|n| { *n *= 3 });
    /// let values: HashSet<_> = sec.into_iter().map(|(_k, v)| v).collect();
    /// let check: HashSet<_> = vec![30, 60, 90].into_iter().collect();
    /// assert_eq!(values, check);
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<K, V> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }
}

impl<K: Key, V> Default for SparseSecondaryMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Key, V> Index<K> for SparseSecondaryMap<K, V> {
    type Output = V;

    fn index(&self, key: K) -> &V {
        match self.get(key) {
            Some(r) => r,
            None => panic!("invalid SparseSecondaryMap key used"),
        }
    }
}

impl<K: Key, V> IndexMut<K> for SparseSecondaryMap<K, V> {
    fn index_mut(&mut self, key: K) -> &mut V {
        match self.get_mut(key) {
            Some(r) => r,
            None => panic!("invalid SparseSecondaryMap key used"),
        }
    }
}

impl<K: Key, V: PartialEq> PartialEq for SparseSecondaryMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter().all(|(key, value)| {
            other
                .get(key)
                .map_or(false, |other_value| *value == *other_value)
        })
    }
}

impl<K: Key, V: Eq> Eq for SparseSecondaryMap<K, V> {}

impl<K: Key, V> FromIterator<(K, V)> for SparseSecondaryMap<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut sec = Self::new();
        sec.extend(iter);
        sec
    }
}

impl<K: Key, V> Extend<(K, V)> for SparseSecondaryMap<K, V> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<'a, K: Key, V: 'a + Copy> Extend<(K, &'a V)> for SparseSecondaryMap<K, V> {
    fn extend<I: IntoIterator<Item = (K, &'a V)>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        for (k, v) in iter {
            self.insert(k, *v);
        }
    }
}

// Iterators.
/// A draining iterator for `SparseSecondaryMap`.
#[derive(Debug)]
pub struct Drain<'a, K: Key + 'a, V: 'a> {
    inner: hash_map::Drain<'a, u32, Slot<V>>,
    _k: PhantomData<fn(K) -> K>,
}

/// An iterator that moves key-value pairs out of a `SparseSecondaryMap`.
#[derive(Debug)]
pub struct IntoIter<K: Key, V> {
    inner: hash_map::IntoIter<u32, Slot<V>>,
    _k: PhantomData<fn(K) -> K>,
}

/// An iterator over the key-value pairs in a `SparseSecondaryMap`.
#[derive(Debug)]
pub struct Iter<'a, K: Key + 'a, V: 'a> {
    inner: hash_map::Iter<'a, u32, Slot<V>>,
    _k: PhantomData<fn(K) -> K>,
}

/// A mutable iterator over the key-value pairs in a `SparseSecondaryMap`.
#[derive(Debug)]
pub struct IterMut<'a, K: Key + 'a, V: 'a> {
    inner: hash_map::IterMut<'a, u32, Slot<V>>,
    _k: PhantomData<fn(K) -> K>,
}

/// An iterator over the keys in a `SparseSecondaryMap`.
#[derive(Debug)]
pub struct Keys<'a, K: Key + 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

/// An iterator over the values in a `SparseSecondaryMap`.
#[derive(Debug)]
pub struct Values<'a, K: Key + 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

/// A mutable iterator over the values in a `SparseSecondaryMap`.
#[derive(Debug)]
pub struct ValuesMut<'a, K: Key + 'a, V: 'a> {
    inner: IterMut<'a, K, V>,
}

impl<'a, K: Key, V> Iterator for Drain<'a, K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        self.inner.next().map(|(idx, slot)| {
            let key = KeyData::new(idx, slot.version).into();
            (key, slot.value)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K: Key, V> Drop for Drain<'a, K, V> {
    fn drop(&mut self) {
        self.for_each(|_drop| {});
    }
}

impl<K: Key, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        self.inner.next().map(|(idx, slot)| {
            let key = KeyData::new(idx, slot.version).into();
            (key, slot.value)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K: Key, V> Iterator for Iter<'a, K, V> {
    type Item = (K, &'a V);

    fn next(&mut self) -> Option<(K, &'a V)> {
        self.inner.next().map(|(&idx, slot)| {
            let key = KeyData::new(idx, slot.version).into();
            (key, &slot.value)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K: Key, V> Iterator for IterMut<'a, K, V> {
    type Item = (K, &'a mut V);

    fn next(&mut self) -> Option<(K, &'a mut V)> {
        self.inner.next().map(|(&idx, slot)| {
            let key = KeyData::new(idx, slot.version).into();
            (key, &mut slot.value)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K: Key, V> Iterator for Keys<'a, K, V> {
    type Item = K;

    fn next(&mut self) -> Option<K> {
        self.inner.next().map(|(key, _)| key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K: Key, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<&'a V> {
        self.inner.next().map(|(_, value)| value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K: Key, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<&'a mut V> {
        self.inner.next().map(|(_, value)| value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K: Key, V> IntoIterator for &'a SparseSecondaryMap<K, V> {
    type Item = (K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K: Key, V> IntoIterator for &'a mut SparseSecondaryMap<K, V> {
    type Item = (K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<K: Key, V> IntoIterator for SparseSecondaryMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.slots.into_iter(),
            _k: PhantomData,
        }
    }
}

impl<'a, K: Key, V> FusedIterator for Iter<'a, K, V> {}
impl<'a, K: Key, V> FusedIterator for IterMut<'a, K, V> {}
impl<'a, K: Key, V> FusedIterator for Keys<'a, K, V> {}
impl<'a, K: Key, V> FusedIterator for Values<'a, K, V> {}
impl<'a, K: Key, V> FusedIterator for ValuesMut<'a, K, V> {}
impl<'a, K: Key, V> FusedIterator for Drain<'a, K, V> {}
impl<K: Key, V> FusedIterator for IntoIter<K, V> {}

impl<'a, K: Key, V> ExactSizeIterator for Iter<'a, K, V> {}
impl<'a, K: Key, V> ExactSizeIterator for IterMut<'a, K, V> {}
impl<'a, K: Key, V> ExactSizeIterator for Keys<'a, K, V> {}
impl<'a, K: Key, V> ExactSizeIterator for Values<'a, K, V> {}
impl<'a, K: Key, V> ExactSizeIterator for ValuesMut<'a, K, V> {}
impl<'a, K: Key, V> ExactSizeIterator for Drain<'a, K, V> {}
impl<K: Key, V> ExactSizeIterator for IntoIter<K, V> {}

// Serialization with serde.
#[cfg(feature = "serde")]
mod serialize {
    use super::*;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use SecondaryMap;

    impl<K: Key, V: Serialize> Serialize for SparseSecondaryMap<K, V> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let mut serde_sec = SecondaryMap::new();
            for (k, v) in self {
                serde_sec.insert(k, v);
            }

            serde_sec.serialize(serializer)
        }
    }

    impl<'de, K: Key, V: Deserialize<'de>> Deserialize<'de> for SparseSecondaryMap<K, V> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            let serde_sec: SecondaryMap<K, V> = Deserialize::deserialize(deserializer)?;
            let mut sec = Self::new();

            for (k, v) in serde_sec {
                sec.insert(k, v);
            }

            Ok(sec)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use *;

    #[cfg(feature = "serde")]
    use serde_json;

    quickcheck! {
        fn qc_secmap_equiv_hashmap(operations: Vec<(u8, u32)>) -> bool {
            let mut hm = HashMap::new();
            let mut hm_keys = Vec::new();
            let mut unique_key = 0u32;
            let mut sm = SlotMap::new();
            let mut sec = SparseSecondaryMap::new();
            let mut sm_keys = Vec::new();

            #[cfg(not(feature = "serde"))]
            let num_ops = 3;
            #[cfg(feature = "serde")]
            let num_ops = 4;

            for (op, val) in operations {
                match op % num_ops {
                    // Insert.
                    0 => {
                        hm.insert(unique_key, val);
                        hm_keys.push(unique_key);
                        unique_key += 1;

                        let k = sm.insert(val);
                        sec.insert(k, val);
                        sm_keys.push(k);
                    }

                    // Delete.
                    1 => {
                        if hm_keys.len() == 0 { continue; }

                        let idx = val as usize % hm_keys.len();
                        sm.remove(sm_keys[idx]);
                        if hm.remove(&hm_keys[idx]) != sec.remove(sm_keys[idx]) {
                            return false;
                        }
                    }

                    // Access.
                    2 => {
                        if hm_keys.len() == 0 { continue; }
                        let idx = val as usize % hm_keys.len();
                        let (hm_key, sm_key) = (&hm_keys[idx], sm_keys[idx]);

                        if hm.contains_key(hm_key) != sec.contains_key(sm_key) ||
                           hm.get(hm_key) != sec.get(sm_key) {
                            return false;
                        }
                    }

                    // Serde round-trip.
                    #[cfg(feature = "serde")]
                    3 => {
                        let ser = serde_json::to_string(&sec).unwrap();
                        sec = serde_json::from_str(&ser).unwrap();
                    }

                    _ => unreachable!(),
                }
            }

            let mut secv: Vec<_> = sec.values().collect();
            let mut hmv: Vec<_> = hm.values().collect();
            secv.sort();
            hmv.sort();
            secv == hmv
        }
    }
}
