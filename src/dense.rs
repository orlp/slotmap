//! Contains the dense slot map implementation.

// There is quite a lot of unsafe code in this implementation. To prevent the
// same explanation over and over again, care must be taken that indices in
// slots and keys from key-value pairs **that are stored inside the slot map**
// are valid. Keys that are received from the user are not trusted (as they
// might have come from a different slot map or malicious serde deseralization).

use std;
use std::iter::FusedIterator;
use std::ops::{Index, IndexMut};

use super::Key;

// A slot, which represents storage for an index and a current version.
// Can be occupied or vacant.
#[derive(Debug, Clone)]
struct Slot {
    // Even = vacant, odd = occupied.
    version: u32,

    // An index when occupied, the next free slot otherwise.
    idx_or_free: u32,
}

/// Dense slot map, storage with stable unique keys.
///
/// See [crate documentation](index.html) for more details.
#[derive(Debug, Clone)]
pub struct DenseSlotMap<T> {
    keys: Vec<Key>,
    values: Vec<T>,
    slots: Vec<Slot>,
    free_head: usize,
}

impl<T> DenseSlotMap<T> {
    /// Construct a new, empty `DenseSlotMap`.
    ///
    /// The slot map will not allocate until values are inserted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm: DenseSlotMap<i32> = DenseSlotMap::new();
    /// ```
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Creates an empty `DenseSlotMap` with the given capacity.
    ///
    /// The slot map will not reallocate until it holds at least `capacity`
    /// elements. If `capacity` is 0, the slot map will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm: DenseSlotMap<i32> = DenseSlotMap::with_capacity(10);
    /// ```
    pub fn with_capacity(capacity: usize) -> DenseSlotMap<T> {
        DenseSlotMap {
            keys: Vec::with_capacity(capacity),
            values: Vec::with_capacity(capacity),
            slots: Vec::with_capacity(capacity),
            free_head: 0,
        }
    }

    /// Returns the number of elements in the slot map.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::with_capacity(10);
    /// sm.insert("len() counts actual elements, not capacity");
    /// let key = sm.insert("removed elements don't count either");
    /// sm.remove(key);
    /// assert_eq!(sm.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.keys.len()
    }

    /// Returns if the slot map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// let key = sm.insert("dummy");
    /// assert_eq!(sm.is_empty(), false);
    /// sm.remove(key);
    /// assert_eq!(sm.is_empty(), true);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    /// Returns the number of elements the `DenseSlotMap` can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let sm: DenseSlotMap<f64> = DenseSlotMap::with_capacity(10);
    /// assert_eq!(sm.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.keys.capacity()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `DenseSlotMap`. The collection may reserve more space to
    /// avoid frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// sm.insert("foo");
    /// sm.reserve(32);
    /// assert!(sm.capacity() >= 33);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.keys.reserve(additional);
        self.values.reserve(additional);
        let needed = (self.len() + additional).saturating_sub(self.slots.len());
        self.slots.reserve(needed);
    }

    /// Returns `true` if the slot map contains `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// let key = sm.insert(42);
    /// assert_eq!(sm.contains_key(key), true);
    /// sm.remove(key);
    /// assert_eq!(sm.contains_key(key), false);
    /// ```
    pub fn contains_key(&self, key: Key) -> bool {
        self.slots
            .get(key.idx as usize)
            .map(|slot| slot.version == key.version)
            .unwrap_or(false)
    }

    /// Inserts a value into the slot map. Returns a unique
    /// [`Key`](struct.Key.html) that can be used to access this value.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the slot map equals
    /// 2<sup>32</sup> - 1.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// let key = sm.insert(42);
    /// assert_eq!(sm[key], 42);
    /// ```
    pub fn insert(&mut self, value: T) -> Key {
        self.insert_with_key(|_| value)
    }

    /// Inserts a value given by `f` into the slot map. The `Key` where the
    /// value will be stored is passed into `f`. This is useful to store values
    /// that contain their own key.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the slot map equals
    /// 2<sup>32</sup> - 1.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// let key = sm.insert_with_key(|k| (k, 20));
    /// assert_eq!(sm[key], (key, 20));
    /// ```
    pub fn insert_with_key<F>(&mut self, f: F) -> Key
    where
        F: FnOnce(Key) -> T,
    {
        if self.len() + 1 == std::u32::MAX as usize {
            panic!("DenseSlotMap number of elements overflow");
        }

        let idx = self.free_head;

        if let Some(slot) = self.slots.get_mut(idx) {
            let occupied_version = slot.version | 1;
            let key = Key {
                idx: idx as u32,
                version: occupied_version,
            };

            // Push value before adjusting slots/freelist in case f panics.
            self.keys.push(key);
            self.values.push(f(key));
            self.free_head = slot.idx_or_free as usize;
            slot.idx_or_free = self.keys.len() as u32 - 1;
            slot.version = occupied_version;

            return key;
        }

        let key = Key {
            idx: idx as u32,
            version: 1,
        };

        // Push value before adjusting slots/freelist in case f panics.
        self.keys.push(key);
        self.values.push(f(key));
        self.slots.push(Slot {
            version: 1,
            idx_or_free: self.keys.len() as u32 - 1,
        });
        self.free_head = self.slots.len();
        key
    }

    // Helper function to add a slot to the freelist. Returns the index that
    // was stored in the slot.
    #[inline(always)]
    fn free_slot(&mut self, slot_idx: usize) -> u32 {
        let slot = &mut self.slots[slot_idx];
        let value_idx = slot.idx_or_free;
        slot.version = slot.version.wrapping_add(1);
        slot.idx_or_free = self.free_head as u32;
        self.free_head = slot_idx;
        value_idx
    }

    // Helper function to remove a value from a slot and make the slot free.
    // Returns the value removed.
    #[inline(always)]
    fn remove_from_slot(&mut self, slot_idx: usize) -> T {
        let value_idx = self.free_slot(slot_idx);

        // Remove values/slot_indices by swapping to end.
        let _ = self.keys.swap_remove(value_idx as usize);
        let value = self.values.swap_remove(value_idx as usize);

        // Did something take our place? Update its slot to new position.
        if let Some(k) = self.keys.get(value_idx as usize) {
            self.slots[k.idx as usize].idx_or_free = value_idx;
        }

        value
    }

    /// Removes a key from the slot map, returning the value at the key if the
    /// key was not previously removed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// let key = sm.insert(42);
    /// assert_eq!(sm.remove(key), Some(42));
    /// assert_eq!(sm.remove(key), None);
    /// ```
    pub fn remove(&mut self, key: Key) -> Option<T> {
        if self.contains_key(key) {
            Some(self.remove_from_slot(key.idx as usize))
        } else {
            None
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all key-value pairs (k, v) such that
    /// `f(k, &mut v)` returns false. This method operates in place and
    /// invalidates any removed keys.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    ///
    /// let k3 = sm.insert(2);
    /// let k1 = sm.insert(0);
    /// let k2 = sm.insert(1);
    ///
    /// sm.retain(|key, val| key == k1 || *val == 1);
    ///
    /// assert!(sm.contains_key(k1));
    /// assert!(sm.contains_key(k2));
    /// assert!(!sm.contains_key(k3));
    ///
    /// assert_eq!(2, sm.len());
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(Key, &mut T) -> bool,
    {
        let mut i = 0;
        while i < self.keys.len() {
            let (should_keep, slot_idx) = {
                let (key, mut value) = (self.keys[i], &mut self.values[i]);
                (f(key, &mut value), key.idx as usize)
            };

            if should_keep {
                i += 1;
            } else {
                // We do not increment i here intentionally. This index has just
                // been replaced with a new value.
                self.remove_from_slot(slot_idx);
            }
        }
    }

    /// Clears the slot map. Keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// for i in 0..10 {
    ///     sm.insert(i);
    /// }
    /// assert_eq!(sm.len(), 10);
    /// sm.clear();
    /// assert_eq!(sm.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.drain();
    }

    /// Clears the slot map, returning all key-value pairs as an iterator. Keeps
    /// the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// let k = sm.insert(0);
    /// let v: Vec<_> = sm.drain().collect();
    /// assert_eq!(sm.len(), 0);
    /// assert_eq!(v, vec![(k, 0)]);
    /// ```
    pub fn drain(&mut self) -> Drain<T> {
        Drain { sm: self }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// let key = sm.insert("bar");
    /// assert_eq!(sm.get(key), Some(&"bar"));
    /// sm.remove(key);
    /// assert_eq!(sm.get(key), None);
    /// ```
    pub fn get(&self, key: Key) -> Option<&T> {
        self.slots
            .get(key.idx as usize)
            .filter(|slot| slot.version == key.version)
            .map(|slot| unsafe {
                // This is safe because we only store valid indices.
                let idx = slot.idx_or_free as usize;
                self.values.get_unchecked(idx)
            })
    }

    /// Returns a reference to the value corresponding to the key without
    /// version or bounds checking.
    ///
    /// # Safety
    ///
    /// This should only be used if `contains_key(key)` is true. Otherwise it is
    /// potentially unsafe.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// let key = sm.insert("bar");
    /// assert_eq!(unsafe { sm.get_unchecked(key) }, &"bar");
    /// sm.remove(key);
    /// // sm.get_unchecked(key) is now dangerous!
    /// ```
    pub unsafe fn get_unchecked(&self, key: Key) -> &T {
        let idx = self.slots.get_unchecked(key.idx as usize).idx_or_free;
        &self.values.get_unchecked(idx as usize)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// let key = sm.insert(3.5);
    /// if let Some(x) = sm.get_mut(key) {
    ///     *x += 3.0;
    /// }
    /// assert_eq!(sm[key], 6.5);
    /// ```
    pub fn get_mut(&mut self, key: Key) -> Option<&mut T> {
        self.slots
            .get(key.idx as usize)
            .filter(|slot| slot.version == key.version)
            .map(|slot| slot.idx_or_free as usize)
            .map(move |idx| unsafe { self.values.get_unchecked_mut(idx) })
    }

    /// Returns a mutable reference to the value corresponding to the key
    /// without version or bounds checking.
    ///
    /// # Safety
    ///
    /// This should only be used if `contains_key(key)` is true. Otherwise it is
    /// potentially unsafe.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// let key = sm.insert("foo");
    /// unsafe { *sm.get_unchecked_mut(key) = "bar" };
    /// assert_eq!(sm[key], "bar");
    /// sm.remove(key);
    /// // sm.get_unchecked_mut(key) is now dangerous!
    /// ```
    pub unsafe fn get_unchecked_mut(&mut self, key: Key) -> &mut T {
        let idx = self.slots.get_unchecked(key.idx as usize).idx_or_free;
        self.values.get_unchecked_mut(idx as usize)
    }

    /// An iterator visiting all key-value pairs in arbitrary order. The
    /// iterator element type is `(Key, &'a T)`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// let k0 = sm.insert(0);
    /// let k1 = sm.insert(1);
    /// let k2 = sm.insert(2);
    ///
    /// let mut it = sm.iter();
    /// assert_eq!(it.next(), Some((k0, &0)));
    /// assert_eq!(it.len(), 2);
    /// assert_eq!(it.next(), Some((k1, &1)));
    /// assert_eq!(it.next(), Some((k2, &2)));
    /// assert_eq!(it.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter::<T> {
            inner_keys: self.keys.iter(),
            inner_values: self.values.iter(),
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order, with
    /// mutable references to the values. The iterator element type is
    /// `(Key, &'a mut T)`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// let k0 = sm.insert(10);
    /// let k1 = sm.insert(20);
    /// let k2 = sm.insert(30);
    ///
    /// for (k, v) in sm.iter_mut() {
    ///     if k != k1 {
    ///         *v *= -1;
    ///     }
    /// }
    ///
    /// assert_eq!(sm.values().collect::<Vec<_>>(), vec![&-10, &20, &-30]);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut::<T> {
            inner_keys: self.keys.iter(),
            inner_values: self.values.iter_mut(),
        }
    }

    /// An iterator visiting all keys in arbitrary order. The iterator element
    /// type is `Key`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// let k0 = sm.insert(10);
    /// let k1 = sm.insert(20);
    /// let k2 = sm.insert(30);
    /// let v: Vec<_> = sm.keys().collect();
    /// assert_eq!(v, vec![k0, k1, k2]);
    /// ```
    pub fn keys(&self) -> Keys {
        Keys {
            inner_keys: self.keys.iter(),
        }
    }

    /// An iterator visiting all values in arbitrary order. The iterator element
    /// type is `&'a T`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// sm.insert(10);
    /// sm.insert(20);
    /// sm.insert(30);
    /// let v: Vec<_> = sm.values().collect();
    /// assert_eq!(v, vec![&10, &20, &30]);
    /// ```
    pub fn values(&self) -> Values<T> {
        Values::<T> {
            inner_values: self.values.iter(),
        }
    }

    /// An iterator visiting all values mutably in arbitrary order. The iterator
    /// element type is `&'a mut T`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = DenseSlotMap::new();
    /// sm.insert(10);
    /// sm.insert(20);
    /// sm.insert(30);
    /// sm.values_mut().for_each(|n| { *n *= 3 });
    /// let v: Vec<_> = sm.into_iter().map(|(_k, v)| v).collect();
    /// assert_eq!(v, vec![30, 60, 90]);
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<T> {
        ValuesMut::<T> {
            inner_values: self.values.iter_mut(),
        }
    }
}

impl<T> Default for DenseSlotMap<T> {
    fn default() -> Self {
        DenseSlotMap::new()
    }
}

impl<T> Index<Key> for DenseSlotMap<T> {
    type Output = T;

    fn index(&self, key: Key) -> &T {
        match self.get(key) {
            Some(r) => r,
            None => panic!("invalid DenseSlotMap key used"),
        }
    }
}

impl<T> IndexMut<Key> for DenseSlotMap<T> {
    fn index_mut(&mut self, key: Key) -> &mut T {
        match self.get_mut(key) {
            Some(r) => r,
            None => panic!("invalid DenseSlotMap key used"),
        }
    }
}

// Iterators.
/// A draining iterator for `DenseSlotMap`.
#[derive(Debug)]
pub struct Drain<'a, T: 'a> {
    sm: &'a mut DenseSlotMap<T>,
}

/// An iterator that moves key-value pairs out of a `DenseSlotMap`.
#[derive(Debug)]
pub struct IntoIter<T> {
    inner_keys: std::vec::IntoIter<Key>,
    inner_values: std::vec::IntoIter<T>,
}

/// An iterator over the key-value pairs in a `DenseSlotMap`.
#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    inner_keys: std::slice::Iter<'a, Key>,
    inner_values: std::slice::Iter<'a, T>,
}

/// A mutable iterator over the key-value pairs in a `DenseSlotMap`.
#[derive(Debug)]
pub struct IterMut<'a, T: 'a> {
    inner_keys: std::slice::Iter<'a, Key>,
    inner_values: std::slice::IterMut<'a, T>,
}

/// An iterator over the keys in a `DenseSlotMap`.
#[derive(Debug)]
pub struct Keys<'a> {
    inner_keys: std::slice::Iter<'a, Key>,
}

/// An iterator over the values in a `DenseSlotMap`.
#[derive(Debug)]
pub struct Values<'a, T: 'a> {
    inner_values: std::slice::Iter<'a, T>,
}

/// A mutable iterator over the values in a `DenseSlotMap`.
#[derive(Debug)]
pub struct ValuesMut<'a, T: 'a> {
    inner_values: std::slice::IterMut<'a, T>,
}

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = (Key, T);

    fn next(&mut self) -> Option<(Key, T)> {
        // We make no iteration order guarantees, so we just repeatedly pop.

        let key = self.sm.keys.pop();
        let value = self.sm.values.pop();

        if let (Some(k), Some(v)) = (key, value) {
            self.sm.free_slot(k.idx as usize);
            Some((k, v))
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.sm.keys.len();
        (len, Some(len))
    }
}

impl<'a, T> Drop for Drain<'a, T> {
    fn drop(&mut self) {
        self.for_each(|_drop| {});
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = (Key, T);

    fn next(&mut self) -> Option<(Key, T)> {

        let key = self.inner_keys.next();
        let value = self.inner_values.next();

        if let (Some(k), Some(v)) = (key, value) {
            Some((k, v))
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner_keys.size_hint()
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (Key, &'a T);

    fn next(&mut self) -> Option<(Key, &'a T)> {
        
        let key = self.inner_keys.next();
        let value = self.inner_values.next();

        if let (Some(k), Some(v)) = (key, value) {
            Some((*k, v))
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner_keys.size_hint()
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (Key, &'a mut T);

    fn next(&mut self) -> Option<(Key, &'a mut T)> {
        
        let key = self.inner_keys.next();
        let value = self.inner_values.next();

        if let (Some(k), Some(v)) = (key, value) {
            Some((*k, v))
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner_keys.size_hint()
    }
}

impl<'a> Iterator for Keys<'a> {
    type Item = Key;

    fn next(&mut self) -> Option<Key> {
        self.inner_keys.next().map(|k| *k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner_keys.size_hint()
    }
}

impl<'a, T> Iterator for Values<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.inner_values.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner_values.size_hint()
    }
}

impl<'a, T> Iterator for ValuesMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        self.inner_values.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner_values.size_hint()
    }
}

impl<'a, T> IntoIterator for &'a DenseSlotMap<T> {
    type Item = (Key, &'a T);
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut DenseSlotMap<T> {
    type Item = (Key, &'a mut T);
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T> IntoIterator for DenseSlotMap<T> {
    type Item = (Key, T);
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner_keys: self.keys.into_iter(),
            inner_values: self.values.into_iter(),
        }
    }
}

impl<'a, T> FusedIterator for Iter<'a, T> {}
impl<'a, T> FusedIterator for IterMut<'a, T> {}
impl<'a>    FusedIterator for Keys<'a> {}
impl<'a, T> FusedIterator for Values<'a, T> {}
impl<'a, T> FusedIterator for ValuesMut<'a, T> {}
impl<'a, T> FusedIterator for Drain<'a, T> {}
impl<T> FusedIterator for IntoIter<T> {}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {}
impl<'a, T> ExactSizeIterator for IterMut<'a, T> {}
impl<'a>    ExactSizeIterator for Keys<'a> {}
impl<'a, T> ExactSizeIterator for Values<'a, T> {}
impl<'a, T> ExactSizeIterator for ValuesMut<'a, T> {}
impl<'a, T> ExactSizeIterator for Drain<'a, T> {}
impl<T> ExactSizeIterator for IntoIter<T> {}

// Serialization with serde.
#[cfg(feature = "serde")]
mod serialize {
    use super::*;
    use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

    #[derive(Serialize, Deserialize)]
    struct SerSlot<T> {
        value: Option<T>,
        version: u32,
    }

    impl<T: Serialize> Serialize for DenseSlotMap<T> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let ser_slots: Vec<_> = self
                .slots
                .iter()
                .map(|slot| SerSlot {
                    value: if slot.version % 2 > 0 {
                        Some(&self.key_values[slot.idx_or_free as usize].value)
                    } else {
                        None
                    },
                    version: slot.version,
                })
                .collect();
            ser_slots.serialize(serializer)
        }
    }

    impl<'de, T: Deserialize<'de>> Deserialize<'de> for DenseSlotMap<T> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            let ser_slots: Vec<SerSlot<T>> = Deserialize::deserialize(deserializer)?;
            if ser_slots.len() >= (1 << 32) - 1 {
                return Err(de::Error::custom(&"too many slots"));
            }

            // Rebuild slots and key_values.
            let mut key_values = Vec::new();
            let mut slots = Vec::new();
            let mut next_free = ser_slots.len();
            for (i, ser_slot) in ser_slots.into_iter().enumerate() {
                if let Some(value) = ser_slot.value {
                    let key = Key {
                        version: ser_slot.version,
                        idx: i as u32,
                    };
                    key_values.push(KeyValue { key, value });
                    slots.push(Slot {
                        version: ser_slot.version,
                        idx_or_free: (key_values.len() - 1) as u32,
                    });
                } else {
                    slots.push(Slot {
                        version: ser_slot.version,
                        idx_or_free: next_free as u32,
                    });
                    next_free = i;
                }
            }

            Ok(DenseSlotMap {
                key_values,
                slots,
                free_head: next_free,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[cfg(feature = "serde")]
    use serde_json;

    #[test]
    fn check_drops() {
        let drops = std::cell::RefCell::new(0usize);
        #[derive(Clone)]
        struct CountDrop<'a>(&'a std::cell::RefCell<usize>);
        impl<'a> Drop for CountDrop<'a> {
            fn drop(&mut self) {
                *self.0.borrow_mut() += 1;
            }
        }

        {
            let mut clone = {
                // Insert 1000 items.
                let mut sm = DenseSlotMap::new();
                let mut sm_keys = Vec::new();
                for _ in 0..1000 {
                    sm_keys.push(sm.insert(CountDrop(&drops)));
                }

                // Remove even keys.
                for i in (0..1000).filter(|i| i % 2 == 0) {
                    sm.remove(sm_keys[i]);
                }

                // Should only have dropped 500 so far.
                assert_eq!(*drops.borrow(), 500);

                // Let's clone ourselves and then die.
                sm.clone()
            };

            // Now all original items should have been dropped exactly once.
            assert_eq!(*drops.borrow(), 1000);

            // Re-use some empty slots.
            for _ in 0..250 {
                clone.insert(CountDrop(&drops));
            }
        }

        // 1000 + 750 drops in total should have happened.
        assert_eq!(*drops.borrow(), 1750);
    }

    quickcheck! {
        fn qc_slotmap_equiv_hashmap(operations: Vec<(u8, u32)>) -> bool {
            let mut hm = HashMap::new();
            let mut hm_keys = Vec::new();
            let mut unique_key = 0u32;
            let mut sm = DenseSlotMap::new();
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

                        sm_keys.push(sm.insert(val));
                    }

                    // Delete.
                    1 => {
                        if hm_keys.len() == 0 { continue; }

                        let idx = val as usize % hm_keys.len();
                        if hm.remove(&hm_keys[idx]) != sm.remove(sm_keys[idx]) {
                            return false;
                        }
                    }

                    // Access.
                    2 => {
                        if hm_keys.len() == 0 { continue; }
                        let idx = val as usize % hm_keys.len();
                        let (hm_key, sm_key) = (&hm_keys[idx], sm_keys[idx]);

                        if hm.contains_key(hm_key) != sm.contains_key(sm_key) ||
                           hm.get(hm_key) != sm.get(sm_key) {
                            return false;
                        }
                    }

                    // Serde round-trip.
                    #[cfg(feature = "serde")]
                    3 => {
                        let ser = serde_json::to_string(&sm).unwrap();
                        sm = serde_json::from_str(&ser).unwrap();
                    }

                    _ => unreachable!(),
                }
            }

            let mut smv: Vec<_> = sm.values().collect();
            let mut hmv: Vec<_> = hm.values().collect();
            smv.sort();
            hmv.sort();
            smv == hmv
        }
    }

    #[cfg(feature = "serde")]
    #[test]
    fn slotmap_serde() {
        let mut sm = DenseSlotMap::new();
        // Self-referential structure.
        let first = sm.insert_with_key(|k| (k, 23i32));
        let second = sm.insert((first, 42));

        // Make some empty slots.
        let empties = vec![sm.insert((first, 0)), sm.insert((first, 0))];
        empties.iter().for_each(|k| {
            sm.remove(*k);
        });

        let third = sm.insert((second, 0));
        sm[first].0 = third;

        let ser = serde_json::to_string(&sm).unwrap();
        let de: DenseSlotMap<(Key, i32)> = serde_json::from_str(&ser).unwrap();
        assert_eq!(de.len(), sm.len());

        let mut smkv: Vec<_> = sm.iter().collect();
        let mut dekv: Vec<_> = de.iter().collect();
        smkv.sort();
        dekv.sort();
        assert_eq!(smkv, dekv);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn slotmap_serde_freelist() {
        let mut sm = DenseSlotMap::new();
        let k0 = sm.insert(5i32);
        let k1 = sm.insert(5i32);
        sm.remove(k0);
        sm.remove(k1);

        let ser = serde_json::to_string(&sm).unwrap();
        let mut de: DenseSlotMap<i32> = serde_json::from_str(&ser).unwrap();

        de.insert(0);
        de.insert(1);
        de.insert(2);
        assert_eq!(de.len(), 3);
    }
}
