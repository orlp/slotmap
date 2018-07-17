//! Contains the slot map implementation.
use std;
use std::iter::{Enumerate, FusedIterator};
use std::mem::ManuallyDrop;
use std::ops::{Index, IndexMut};
use std::{fmt, ptr};

use super::Key;

// A slot, which represents storage for a value and a current version.
// Can be occupied or vacant.
struct Slot<T> {
    // A value when occupied, memory in an unsafe state otherwise.
    value: ManuallyDrop<T>,

    // Even = vacant, odd = occupied.
    version: u32,

    // This could be in an union with value, but that requires unions for types
    // without copy. This isn't available in stable Rust yet.
    next_free: u32,
}

impl<T> Slot<T> {
    // Is this slot occupied?
    #[inline(always)]
    pub fn occupied(&self) -> bool {
        self.version % 2 > 0
    }
}

impl<T> Drop for Slot<T> {
    fn drop(&mut self) {
        if std::mem::needs_drop::<T>() && self.occupied() {
            // This is safe because we checked that we're occupied.
            unsafe {
                ManuallyDrop::drop(&mut self.value);
            }
        }
    }
}

impl<T: Clone> Clone for Slot<T> {
    fn clone(&self) -> Self {
        Self {
            value: if self.occupied() {
                self.value.clone()
            } else {
                unsafe { std::mem::uninitialized() }
            },
            version: self.version,
            next_free: self.next_free,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Slot<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let mut builder = fmt.debug_struct("Slot");
        builder.field("version", &self.version);
        if self.occupied() {
            builder.field("value", &self.value).finish()
        } else {
            builder.field("next_free", &self.next_free).finish()
        }
    }
}

/// Slot map, storage with stable unique keys.
///
/// See [crate documentation](index.html) for more details.
#[derive(Debug, Clone)]
pub struct SlotMap<T> {
    slots: Vec<Slot<T>>,
    free_head: usize,
    num_elems: u32,
}

impl<T> SlotMap<T> {
    /// Construct a new, empty `SlotMap`.
    ///
    /// The slot map will not allocate until values are inserted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm: SlotMap<i32> = SlotMap::new();
    /// ```
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Creates an empty `SlotMap` with the given capacity.
    ///
    /// The slot map will not reallocate until it holds at least `capacity`
    /// elements. If `capacity` is 0, the slot map will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm: SlotMap<i32> = SlotMap::with_capacity(10);
    /// ```
    pub fn with_capacity(capacity: usize) -> SlotMap<T> {
        SlotMap {
            slots: Vec::with_capacity(capacity),
            free_head: 0,
            num_elems: 0,
        }
    }

    /// Returns the number of elements in the slot map.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::with_capacity(10);
    /// sm.insert("len() counts actual elements, not capacity");
    /// let key = sm.insert("removed elements don't count either");
    /// sm.remove(key);
    /// assert_eq!(sm.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.num_elems as usize
    }

    /// Returns if the slot map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert("dummy");
    /// assert_eq!(sm.is_empty(), false);
    /// sm.remove(key);
    /// assert_eq!(sm.is_empty(), true);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.num_elems == 0
    }

    /// Returns the number of elements the `SlotMap` can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let sm: SlotMap<f64> = SlotMap::with_capacity(10);
    /// assert_eq!(sm.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.slots.capacity()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `SlotMap`. The collection may reserve more space to
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
    /// let mut sm = SlotMap::new();
    /// sm.insert("foo");
    /// sm.reserve(32);
    /// assert!(sm.capacity() >= 33);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        let needed = (self.len() + additional).saturating_sub(self.slots.len());
        self.slots.reserve(needed);
    }

    /// Returns `true` if the slot map contains `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert(42);
    /// assert_eq!(sm.contains_key(key), true);
    /// sm.remove(key);
    /// assert_eq!(sm.contains_key(key), false);
    /// ```
    pub fn contains_key(&self, key: Key<T>) -> bool {
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
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert(42);
    /// assert_eq!(sm[key], 42);
    /// ```
    pub fn insert(&mut self, value: T) -> Key<T> {
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
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert_with_key(|k| (k, 20));
    /// assert_eq!(sm[key], (key, 20));
    /// ```
    pub fn insert_with_key<F>(&mut self, f: F) -> Key<T>
    where
        F: FnOnce(Key<T>) -> T,
    {
        // In case f panics, we don't make any changes until we have the value.
        let new_num_elems = self.num_elems + 1;
        if new_num_elems == std::u32::MAX {
            panic!("SlotMap number of elements overflow");
        }

        let idx = self.free_head;

        if let Some(slot) = self.slots.get_mut(idx) {
            let occupied_version = slot.version | 1;
            let key = Key {
                idx: idx as u32,
                version: occupied_version,
                value_type: std::marker::PhantomData,
            };

            // Assign slot.value first in case f panics.
            slot.value = ManuallyDrop::new(f(key));
            slot.version = occupied_version;
            self.free_head = slot.next_free as usize;
            self.num_elems = new_num_elems;
            return key;
        }

        let key = Key {
            idx: idx as u32,
            version: 1,
            value_type: std::marker::PhantomData,
        };

        // Create new slot before adjusting freelist in case f panics.
        self.slots.push(Slot {
            value: ManuallyDrop::new(f(key)),
            version: 1,
            next_free: 0,
        });

        self.free_head = self.slots.len();
        self.num_elems = new_num_elems;

        key
    }

    // Helper function to remove a value from a slot. Safe iff the slot is
    // occupied. Returns the value removed.
    #[inline(always)]
    unsafe fn remove_from_slot(&mut self, idx: usize) -> T {
        // Maintain freelist.
        let slot = self.slots.get_unchecked_mut(idx);
        slot.next_free = self.free_head as u32;
        self.free_head = idx;
        self.num_elems -= 1;

        // Remove value from slot.
        slot.version = slot.version.wrapping_add(1);
        ptr::read(&*slot.value)
    }

    /// Removes a key from the slot map, returning the value at the key if the
    /// key was not previously removed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert(42);
    /// assert_eq!(sm.remove(key), Some(42));
    /// assert_eq!(sm.remove(key), None);
    /// ```
    pub fn remove(&mut self, key: Key<T>) -> Option<T> {
        if self.contains_key(key) {
            // This is safe because we know that the slot is occupied.
            Some(unsafe { self.remove_from_slot(key.idx as usize) })
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
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    ///
    /// let k1 = sm.insert(0);
    /// let k2 = sm.insert(1);
    /// let k3 = sm.insert(2);
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
        F: FnMut(Key<T>, &mut T) -> bool,
    {
        let len = self.slots.len();
        for i in 0..len {
            let should_remove = {
                // This is safe because removing elements does not shrink slots.
                let slot = unsafe { self.slots.get_unchecked_mut(i) };
                let key = Key {
                    idx: i as u32,
                    version: slot.version,
                    value_type: std::marker::PhantomData,
                };

                slot.occupied() && !f(key, &mut slot.value)
            };

            if should_remove {
                // This is safe because we know that the slot was occupied.
                unsafe { self.remove_from_slot(i) };
            }
        }
    }

    /// Clears the slot map. Keeps the allocated memory for reuse.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
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
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let k = sm.insert(0);
    /// let v: Vec<_> = sm.drain().collect();
    /// assert_eq!(sm.len(), 0);
    /// assert_eq!(v, vec![(k, 0)]);
    /// ```
    pub fn drain(&mut self) -> Drain<T> {
        Drain {
            cur: 0,
            num_left: self.len(),
            sm: self,
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert("bar");
    /// assert_eq!(sm.get(key), Some(&"bar"));
    /// sm.remove(key);
    /// assert_eq!(sm.get(key), None);
    /// ```
    pub fn get(&self, key: Key<T>) -> Option<&T> {
        self.slots
            .get(key.idx as usize)
            .filter(|slot| slot.version == key.version)
            .map(|slot| &*slot.value)
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
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert("bar");
    /// assert_eq!(unsafe { sm.get_unchecked(key) }, &"bar");
    /// sm.remove(key);
    /// // sm.get_unchecked(key) is now dangerous!
    /// ```
    pub unsafe fn get_unchecked(&self, key: Key<T>) -> &T {
        &self.slots.get_unchecked(key.idx as usize).value
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert(3.5);
    /// if let Some(x) = sm.get_mut(key) {
    ///     *x += 3.0;
    /// }
    /// assert_eq!(sm[key], 6.5);
    /// ```
    pub fn get_mut(&mut self, key: Key<T>) -> Option<&mut T> {
        self.slots
            .get_mut(key.idx as usize)
            .filter(|slot| slot.version == key.version)
            .map(|slot| &mut *slot.value)
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
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert("foo");
    /// unsafe { *sm.get_unchecked_mut(key) = "bar" };
    /// assert_eq!(sm[key], "bar");
    /// sm.remove(key);
    /// // sm.get_unchecked_mut(key) is now dangerous!
    /// ```
    pub unsafe fn get_unchecked_mut(&mut self, key: Key<T>) -> &mut T {
        &mut self.slots.get_unchecked_mut(key.idx as usize).value
    }

    /// An iterator visiting all key-value pairs in arbitrary order. The
    /// iterator element type is `(Key, &'a T)`.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
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
            slots: self.slots.iter().enumerate(),
            num_left: self.len(),
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order, with
    /// mutable references to the values. The iterator element type is
    /// `(Key, &'a mut T)`.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
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
            num_left: self.len(),
            slots: self.slots.iter_mut().enumerate(),
        }
    }

    /// An iterator visiting all keys in arbitrary order. The iterator element
    /// type is `Key`.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let k0 = sm.insert(10);
    /// let k1 = sm.insert(20);
    /// let k2 = sm.insert(30);
    /// let v: Vec<_> = sm.keys().collect();
    /// assert_eq!(v, vec![k0, k1, k2]);
    /// ```
    pub fn keys(&self) -> Keys<T> {
        Keys::<T> { inner: self.iter() }
    }

    /// An iterator visiting all values in arbitrary order. The iterator element
    /// type is `&'a T`.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// sm.insert(10);
    /// sm.insert(20);
    /// sm.insert(30);
    /// let v: Vec<_> = sm.values().collect();
    /// assert_eq!(v, vec![&10, &20, &30]);
    /// ```
    pub fn values(&self) -> Values<T> {
        Values::<T> { inner: self.iter() }
    }

    /// An iterator visiting all values mutably in arbitrary order. The iterator
    /// element type is `&'a mut T`.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// sm.insert(10);
    /// sm.insert(20);
    /// sm.insert(30);
    /// sm.values_mut().for_each(|n| { *n *= 3 });
    /// let v: Vec<_> = sm.into_iter().map(|(_k, v)| v).collect();
    /// assert_eq!(v, vec![30, 60, 90]);
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<T> {
        ValuesMut::<T> {
            inner: self.iter_mut(),
        }
    }
}

impl<T> Default for SlotMap<T> {
    fn default() -> Self {
        SlotMap::new()
    }
}

impl<T> Index<Key<T>> for SlotMap<T> {
    type Output = T;

    fn index(&self, key: Key<T>) -> &T {
        match self.get(key) {
            Some(r) => r,
            None => panic!("invalid SlotMap key used"),
        }
    }
}

impl<T> IndexMut<Key<T>> for SlotMap<T> {
    fn index_mut(&mut self, key: Key<T>) -> &mut T {
        match self.get_mut(key) {
            Some(r) => r,
            None => panic!("invalid SlotMap key used"),
        }
    }
}

// Iterators.
/// A draining iterator for `SlotMap`.
#[derive(Debug)]
pub struct Drain<'a, T: 'a> {
    num_left: usize,
    sm: &'a mut SlotMap<T>,
    cur: usize,
}

/// An iterator that moves key-value pairs out of a `SlotMap`.
#[derive(Debug)]
pub struct IntoIter<T> {
    num_left: usize,
    slots: Enumerate<std::vec::IntoIter<Slot<T>>>,
}

/// An iterator over the key-value pairs in a `SlotMap`.
#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    num_left: usize,
    slots: Enumerate<std::slice::Iter<'a, Slot<T>>>,
}

/// A mutable iterator over the key-value pairs in a `SlotMap`.
#[derive(Debug)]
pub struct IterMut<'a, T: 'a> {
    num_left: usize,
    slots: Enumerate<std::slice::IterMut<'a, Slot<T>>>,
}

/// An iterator over the keys in a `SlotMap`.
#[derive(Debug)]
pub struct Keys<'a, T: 'a> {
    inner: Iter<'a, T>,
}

/// An iterator over the values in a `SlotMap`.
#[derive(Debug)]
pub struct Values<'a, T: 'a> {
    inner: Iter<'a, T>,
}

/// A mutable iterator over the values in a `SlotMap`.
#[derive(Debug)]
pub struct ValuesMut<'a, T: 'a> {
    inner: IterMut<'a, T>,
}

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = (Key<T>, T);

    fn next(&mut self) -> Option<(Key<T>, T)> {
        let len = self.sm.slots.len();
        while self.cur < len {
            let idx = self.cur;
            self.cur += 1;

            unsafe {
                // This is safe because removing doesn't shrink slots.
                if self.sm.slots.get_unchecked(idx).occupied() {
                    let key = Key {
                        idx: idx as u32,
                        version: self.sm.slots.get_unchecked(idx).version,
                        value_type: std::marker::PhantomData,
                    };

                    self.num_left -= 1;
                    return Some((key, self.sm.remove_from_slot(idx)));
                }
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num_left, Some(self.num_left))
    }
}

impl<'a, T> Drop for Drain<'a, T> {
    fn drop(&mut self) {
        self.for_each(|_drop| {});
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = (Key<T>, T);

    fn next(&mut self) -> Option<(Key<T>, T)> {
        while let Some((idx, mut slot)) = self.slots.next() {
            if slot.occupied() {
                let key = Key {
                    idx: idx as u32,
                    version: slot.version,
                    value_type: std::marker::PhantomData,
                };

                // Prevent dropping after extracting the value.
                slot.version = 0;

                // This is safe because we know the slot was occupied.
                self.num_left -= 1;
                return Some((key, unsafe { ptr::read(&*slot.value) }));
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num_left, Some(self.num_left))
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (Key<T>, &'a T);

    fn next(&mut self) -> Option<(Key<T>, &'a T)> {
        while let Some((idx, slot)) = self.slots.next() {
            if slot.occupied() {
                let key = Key {
                    idx: idx as u32,
                    version: slot.version,
                    value_type: std::marker::PhantomData,
                };

                self.num_left -= 1;
                return Some((key, &slot.value));
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num_left, Some(self.num_left))
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (Key<T>, &'a mut T);

    fn next(&mut self) -> Option<(Key<T>, &'a mut T)> {
        while let Some((idx, slot)) = self.slots.next() {
            if slot.occupied() {
                let key = Key {
                    idx: idx as u32,
                    version: slot.version,
                    value_type: std::marker::PhantomData,
                };

                self.num_left -= 1;
                return Some((key, &mut slot.value));
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num_left, Some(self.num_left))
    }
}

impl<'a, T> Iterator for Keys<'a, T> {
    type Item = Key<T>;

    fn next(&mut self) -> Option<Key<T>> {
        self.inner.next().map(|(key, _)| key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> Iterator for Values<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.inner.next().map(|(_, value)| value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> Iterator for ValuesMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        self.inner.next().map(|(_, value)| value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> IntoIterator for &'a SlotMap<T> {
    type Item = (Key<T>, &'a T);
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut SlotMap<T> {
    type Item = (Key<T>, &'a mut T);
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T> IntoIterator for SlotMap<T> {
    type Item = (Key<T>, T);
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            num_left: self.len(),
            slots: self.slots.into_iter().enumerate(),
        }
    }
}

impl<'a, T> FusedIterator for Iter<'a, T> {}
impl<'a, T> FusedIterator for IterMut<'a, T> {}
impl<'a, T> FusedIterator for Keys<'a, T> {}
impl<'a, T> FusedIterator for Values<'a, T> {}
impl<'a, T> FusedIterator for ValuesMut<'a, T> {}
impl<'a, T> FusedIterator for Drain<'a, T> {}
impl<T> FusedIterator for IntoIter<T> {}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {}
impl<'a, T> ExactSizeIterator for IterMut<'a, T> {}
impl<'a, T> ExactSizeIterator for Keys<'a, T> {}
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
    struct SafeSlot<T> {
        value: Option<T>,
        version: u32,
    }

    impl<T: Serialize> Serialize for Slot<T> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let safe_slot = SafeSlot {
                version: self.version,
                value: if self.occupied() {
                    Some(&*self.value)
                } else {
                    None
                },
            };
            safe_slot.serialize(serializer)
        }
    }

    impl<'de, T> Deserialize<'de> for Slot<T>
    where
        T: Deserialize<'de>,
    {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            let safe_slot: SafeSlot<T> = Deserialize::deserialize(deserializer)?;
            let occupied = safe_slot.version % 2 > 0;
            if occupied ^ safe_slot.value.is_some() {
                return Err(de::Error::custom(&"inconsistent occupation in Slot"));
            }

            Ok(Slot {
                value: match safe_slot.value {
                    Some(value) => ManuallyDrop::new(value),
                    None => unsafe { std::mem::uninitialized() },
                },
                version: safe_slot.version,
                next_free: 0,
            })
        }
    }

    impl<T: Serialize> Serialize for SlotMap<T> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            self.slots.serialize(serializer)
        }
    }

    impl<'de, T: Deserialize<'de>> Deserialize<'de> for SlotMap<T> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            let mut slots: Vec<Slot<T>> = Deserialize::deserialize(deserializer)?;
            if slots.len() >= (1 << 32) - 1 {
                return Err(de::Error::custom(&"too many slots"));
            }

            // We have our slots, rebuild freelist.
            let mut num_elems = 0;
            let mut next_free = slots.len();
            for (i, slot) in slots.iter_mut().enumerate() {
                if slot.occupied() {
                    num_elems += 1;
                } else {
                    slot.next_free = next_free as u32;
                    next_free = i;
                }
            }

            Ok(SlotMap {
                num_elems,
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
                let mut sm = SlotMap::new();
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
            let mut sm = SlotMap::new();
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
        let mut sm = SlotMap::new();
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
        let de: SlotMap<(Key, i32)> = serde_json::from_str(&ser).unwrap();
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
        let mut sm = SlotMap::new();
        let k = sm.insert(5i32);
        sm.remove(k);

        let ser = serde_json::to_string(&sm).unwrap();
        let mut de: SlotMap<i32> = serde_json::from_str(&ser).unwrap();

        de.insert(0);
        de.insert(1);
        de.insert(2);
        assert_eq!(de.len(), 3);
    }
}
