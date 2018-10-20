//! Contains the secondary map implementation.

use std;
use super::{Key, is_older_version};
use std::ops::{Index, IndexMut};
use std::iter::{Enumerate, FusedIterator, FromIterator, Extend};
use std::hint::unreachable_unchecked;

// We could use unions to remove the memory overhead of Option here as well, but
// until non-Copy elements inside unions stabilize it's better to give users at
// least some place to store non-Copy elements.
#[derive(Debug)]
struct Slot<T> {
    version: u32,
    value: Option<T>,
}

impl<T> Slot<T> {
    // Is this slot occupied?
    #[inline(always)]
    pub fn occupied(&self) -> bool {
        self.version % 2 > 0
    }
}

/// Secondary map, associate data with previously stored elements in a slot map.
///
/// A `SecondaryMap` allows you to efficiently store additional information for
/// each element in a slot map. You can have multiple secondary maps per slot
/// map, but not multiple slot maps per secondary map. It is safe but
/// unspecified behavior if you use `Key`s from multiple different slot maps in
/// the same `SecondaryMap`.
///
/// A `SecondaryMap` does not leak memory even if you never remove elements. In
/// return, when you remove a `Key` from the primary slot map, after any insert
/// the space associated with the removed element may be reclaimed. Don't expect
/// the values associated with a removed key to stick around after an insertion
/// has happened!
///
/// Unlike a [`SlotMap`], a `SecondaryMap`s elements do not need to be
/// [`Slottable`]. This means that if you can't or don't want to use nightly
/// Rust you can store that data as secondary properties.
///
/// Finally a note on memory complexity, the `SecondaryMap` can use memory for
/// each slot in the primary slot map, and has to iterate over every slot during
/// iteration, regardless of whether you have inserted an associative value at
/// that key or not. If you have some property that you only expect to set for a
/// minority of keys, use a [`SparseSecondaryMap`], which is backed by a
/// [`HashMap`].
///
/// [`SlotMap`]: ../struct.SlotMap.html
/// [`Slottable`]: ../trait.Slottable.html
/// [`SparseSecondaryMap`]: ../sparse_secondary/struct.SparseSecondaryMap.html
/// [`HashMap`]: https://doc.rust-lang.org/std/collections/struct.HashMap.html
/// 
/// Example usage:
///
/// ```
/// # use slotmap::*;
/// // Nightly Rust needed to store String which is not Copy.
/// let mut players: SlotMap<&'static str> = SlotMap::new();
/// // But not for secondary maps.
/// let mut nicks: SecondaryMap<String> = SecondaryMap::new();
/// let mut health: SecondaryMap<u32> = SecondaryMap::new();
/// let mut ammo: SecondaryMap<u32> = SecondaryMap::new();
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
pub struct SecondaryMap<T> {
    slots: Vec<Slot<T>>,
    num_elems: usize,
}


impl<T> SecondaryMap<T> {
    /// Construct a new, empty `SecondaryMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sec: SecondaryMap<i32> = SecondaryMap::new();
    /// ```
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Creates an empty `SecondaryMap` with the given capacity of slots.
    ///
    /// The secondary map will not reallocate until it holds at least `capacity`
    /// slots. Even inserting a single key-value pair might require as many
    /// slots as the slot map the key comes from, so it's recommended to match
    /// the capacity of a secondary map to its corresponding slot map.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm: SlotMap<i32> = SlotMap::with_capacity(10);
    /// let mut sec: SecondaryMap<i32> = SecondaryMap::with_capacity(sm.capacity());
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            slots: Vec::with_capacity(capacity + 1), // Sentinel.
            num_elems: 0,
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
    /// let mut squared = SecondaryMap::new();
    /// assert_eq!(squared.len(), 0);
    /// squared.insert(k, 16);
    /// assert_eq!(squared.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.num_elems as usize
    }

    /// Returns if the secondary map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sec: SecondaryMap<i32> = SecondaryMap::new();
    /// assert!(sec.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.num_elems == 0
    }

    /// Returns the number of elements the `SecondaryMap` can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sec: SecondaryMap<i32> = SecondaryMap::with_capacity(10);
    /// assert!(sec.capacity() >= 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.slots.capacity() - 1 // Sentinel.
    }

    /// Sets the capacity of the `SecondaryMap` to `new_capacity`, if it is
    /// bigger than the current capacity.
    ///
    /// It is recommended to set the capacity of a `SecondaryMap` to the
    /// capacity of its corresponding slot map before inserting many new
    /// elements to prevent frequent reallocations. The collection may reserve
    /// more space than requested.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sec: SecondaryMap<i32> = SecondaryMap::with_capacity(10);
    /// assert!(sec.capacity() >= 10);
    /// sec.set_capacity(1000);
    /// assert!(sec.capacity() >= 1000);
    /// ```
    pub fn set_capacity(&mut self, new_capacity: usize) {
        let new_capacity = new_capacity + 1; // Sentinel.
        if new_capacity > self.slots.capacity() {
            let needed = new_capacity - self.slots.len();
            self.slots.reserve(needed);
        }
    }

    /// Returns `true` if the secondary map contains `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let k = sm.insert(4);
    /// let mut squared = SecondaryMap::new();
    /// assert!(!squared.contains_key(k));
    /// squared.insert(k, 16);
    /// assert!(squared.contains_key(k));
    /// ```
    pub fn contains_key(&self, key: Key) -> bool {
        self.slots
            .get(key.idx as usize)
            .map(|slot| slot.version == key.version.get())
            .unwrap_or(false)
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
    /// let mut squared = SecondaryMap::new();
    /// assert_eq!(squared.insert(k, 0), None);
    /// assert_eq!(squared.insert(k, 4), Some(0));
    /// // You don't have to use insert if the key is already in the secondary map.
    /// squared[k] *= squared[k];
    /// assert_eq!(squared[k], 16);
    /// ```
    pub fn insert(&mut self, key: Key, value: T) -> Option<T> {
        for _ in self.slots.len()..=key.idx as usize {
            self.slots.push(Slot {
                version: 0,
                value: None,
            });
        }

        let slot = &mut self.slots[key.idx as usize];
        if slot.version == key.version.get() {
            return std::mem::replace(&mut slot.value, Some(value));
        }
        
        if slot.occupied() {
            // Don't replace existing newer values.
            if is_older_version(key.version.get(), slot.version) {
                return None;
            }
        } else {
            self.num_elems += 1;
        }

        *slot = Slot { version: key.version.get(), value: Some(value) };

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
    /// let mut squared = SecondaryMap::new();
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
    pub fn remove(&mut self, key: Key) -> Option<T> {
        if let Some(slot) = self.slots.get_mut(key.idx as usize) {
            if slot.version == key.version.get() {
                // We actually decrement version here, to ensure that if the
                // user re-inserts a value at this key the version does not get
                // denied as outdated.
                slot.version -= 1;
                self.num_elems -= 1;
                return Some(std::mem::replace(&mut slot.value, None).unwrap());
            }
        }

        None
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
    /// let mut sec = SecondaryMap::new();
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
        F: FnMut(Key, &mut T) -> bool,
    {
        let len = self.slots.len();
        for i in 0..len {
            // This is safe because removing elements does not shrink slots.
            let slot = unsafe { self.slots.get_unchecked_mut(i) };
            let should_remove = {
                if let Some(value) = &mut slot.value {
                    let key = Key::new(i as u32, slot.version);
                    !f(key, value)
                } else {
                    false
                }
            };

            if should_remove {
                self.num_elems -= 1;
                slot.version -= 1;
                slot.value = None;
            }
        }
    }

    /// Clears the secondary map. Keeps the allocated memory for reuse.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let mut sec = SecondaryMap::new();
    /// for i in 0..10 {
    ///     sec.insert(sm.insert(i), i);
    /// }
    /// assert_eq!(sec.len(), 10);
    /// sec.clear();
    /// assert_eq!(sec.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.drain();
    }

    /// Clears the secondary map, returning all key-value pairs as an iterator.
    /// Keeps the allocated memory for reuse.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// # use std::iter::FromIterator;
    /// let mut sm = SlotMap::new();
    /// let k = sm.insert(0);
    /// let mut sec = SecondaryMap::new();
    /// sec.insert(k, 1);
    /// let v: Vec<_> = sec.drain().collect();
    /// assert_eq!(sec.len(), 0);
    /// assert_eq!(v, vec![(k, 1)]);
    /// ```
    pub fn drain(&mut self) -> Drain<T> {
        Drain {
            cur: 1,
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
    /// let key = sm.insert("foo");
    /// let mut sec = SecondaryMap::new();
    /// sec.insert(key, "bar");
    /// assert_eq!(sec.get(key), Some(&"bar"));
    /// sec.remove(key);
    /// assert_eq!(sec.get(key), None);
    /// ```
    pub fn get(&self, key: Key) -> Option<&T> {
        self.slots
            .get(key.idx as usize)
            .filter(|slot| slot.version == key.version.get())
            .map(|slot| slot.value.as_ref().unwrap())
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
    /// let key = sm.insert("foo");
    /// let mut sec = SecondaryMap::new();
    /// sec.insert(key, "bar");
    /// assert_eq!(unsafe { sec.get_unchecked(key) }, &"bar");
    /// sec.remove(key);
    /// // sec.get_unchecked(key) is now dangerous!
    /// ```
    pub unsafe fn get_unchecked(&self, key: Key) -> &T {
        if let Some(value) = self.slots.get_unchecked(key.idx as usize).value.as_ref() {
            value
        } else {
            unreachable_unchecked()
        }
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert("test");
    /// let mut sec = SecondaryMap::new();
    /// sec.insert(key, 3.5);
    /// if let Some(x) = sec.get_mut(key) {
    ///     *x += 3.0;
    /// }
    /// assert_eq!(sec[key], 6.5);
    /// ```
    pub fn get_mut(&mut self, key: Key) -> Option<&mut T> {
        self.slots
            .get_mut(key.idx as usize)
            .filter(|slot| slot.version == key.version.get())
            .map(|slot| slot.value.as_mut().unwrap())
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
    /// let mut sec = SecondaryMap::new();
    /// sec.insert(key, "bar");
    /// unsafe { *sec.get_unchecked_mut(key) = "baz" };
    /// assert_eq!(sec[key], "baz");
    /// sec.remove(key);
    /// // sec.get_unchecked_mut(key) is now dangerous!
    /// ```
    pub unsafe fn get_unchecked_mut(&mut self, key: Key) -> &mut T {
        if let Some(value) = self.slots.get_unchecked_mut(key.idx as usize).value.as_mut() {
            value
        } else {
            unreachable_unchecked()
        }
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
    /// let mut sec = SecondaryMap::new();
    /// let k0 = sm.insert(0); sec.insert(k0, 10);
    /// let k1 = sm.insert(1); sec.insert(k1, 11);
    /// let k2 = sm.insert(2); sec.insert(k2, 12);
    ///
    /// let mut it = sec.iter();
    /// assert_eq!(it.next(), Some((k0, &10)));
    /// assert_eq!(it.len(), 2);
    /// assert_eq!(it.next(), Some((k1, &11)));
    /// assert_eq!(it.next(), Some((k2, &12)));
    /// assert_eq!(it.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter {
            num_left: self.num_elems,
            slots: self.slots.iter().enumerate(),
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
    /// # use std::iter::FromIterator;
    /// let mut sm = SlotMap::new();
    /// let mut sec = SecondaryMap::new();
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
    /// assert_eq!(Vec::from_iter(sec.values()), vec![&-10, &20, &-30]);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            num_left: self.num_elems,
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
    /// let mut sec = SecondaryMap::new();
    /// let k0 = sm.insert(1); sec.insert(k0, 10);
    /// let k1 = sm.insert(2); sec.insert(k1, 20);
    /// let k2 = sm.insert(3); sec.insert(k2, 30);
    /// let v: Vec<_> = sec.keys().collect();
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
    /// let mut sec = SecondaryMap::new();
    /// let k0 = sm.insert(1); sec.insert(k0, 10);
    /// let k1 = sm.insert(2); sec.insert(k1, 20);
    /// let k2 = sm.insert(3); sec.insert(k2, 30);
    /// let v: Vec<_> = sec.values().collect();
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
    /// let mut sec = SecondaryMap::new();
    /// sec.insert(sm.insert(1), 10);
    /// sec.insert(sm.insert(2), 20);
    /// sec.insert(sm.insert(3), 30);
    /// sec.values_mut().for_each(|n| { *n *= 3 });
    /// let v: Vec<_> = sec.into_iter().map(|(_k, v)| v).collect();
    /// assert_eq!(v, vec![30, 60, 90]);
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<T> {
        ValuesMut::<T> {
            inner: self.iter_mut(),
        }
    }
}

impl<T> Default for SecondaryMap<T> {
    fn default() -> Self {
        SecondaryMap::new()
    }
}

impl<T> Index<Key> for SecondaryMap<T> {
    type Output = T;

    fn index(&self, key: Key) -> &T {
        match self.get(key) {
            Some(r) => r,
            None => panic!("invalid SecondaryMap key used"),
        }
    }
}

impl<T> IndexMut<Key> for SecondaryMap<T> {
    fn index_mut(&mut self, key: Key) -> &mut T {
        match self.get_mut(key) {
            Some(r) => r,
            None => panic!("invalid SecondaryMap key used"),
        }
    }
}

impl<T: PartialEq> PartialEq for SecondaryMap<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter().all(|(key, value)| {
            other.get(key).map_or(false, |other_value| *value == *other_value)
        })

    }
}

impl<T: Eq> Eq for SecondaryMap<T> {}

impl<T> FromIterator<(Key, T)> for SecondaryMap<T> {
    fn from_iter<I: IntoIterator<Item = (Key, T)>>(iter: I) -> SecondaryMap<T> {
        let mut sec = SecondaryMap::new();
        sec.extend(iter);
        sec
    }
}

impl<T> Extend<(Key, T)> for SecondaryMap<T> {
    fn extend<I: IntoIterator<Item = (Key, T)>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<'a, T: 'a + Copy> Extend<(Key, &'a T)> for SecondaryMap<T> {
    fn extend<I: IntoIterator<Item = (Key, &'a T)>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        for (k, v) in iter {
            self.insert(k, *v);
        }
    }
}

// Iterators.
/// A draining iterator for `SecondaryMap`.
#[derive(Debug)]
pub struct Drain<'a, T: 'a> {
    num_left: usize,
    sm: &'a mut SecondaryMap<T>,
    cur: usize,
}

/// An iterator that moves key-value pairs out of a `SecondaryMap`.
#[derive(Debug)]
pub struct IntoIter<T> {
    num_left: usize,
    slots: Enumerate<std::vec::IntoIter<Slot<T>>>,
}

/// An iterator over the key-value pairs in a `SecondaryMap`.
#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    num_left: usize,
    slots: Enumerate<std::slice::Iter<'a, Slot<T>>>,
}


/// A mutable iterator over the key-value pairs in a `SecondaryMap`.
#[derive(Debug)]
pub struct IterMut<'a, T: 'a> {
    num_left: usize,
    slots: Enumerate<std::slice::IterMut<'a, Slot<T>>>,
}

/// An iterator over the keys in a `SecondaryMap`.
#[derive(Debug)]
pub struct Keys<'a, T: 'a> {
    inner: Iter<'a, T>,
}

/// An iterator over the values in a `SecondaryMap`.
#[derive(Debug)]
pub struct Values<'a, T: 'a> {
    inner: Iter<'a, T>,
}

/// A mutable iterator over the values in a `SecondaryMap`.
#[derive(Debug)]
pub struct ValuesMut<'a, T: 'a> {
    inner: IterMut<'a, T>,
}

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = (Key, T);

    fn next(&mut self) -> Option<(Key, T)> {
        let len = self.sm.slots.len();
        while self.cur < len {
            let idx = self.cur;
            self.cur += 1;

            if let Some(value) = std::mem::replace(&mut self.sm.slots[idx].value, None) {
                let key = Key::new(idx as u32, self.sm.slots[idx].version);
                self.sm.slots[idx].version -= 1;
                self.sm.num_elems -= 1;
                self.num_left -= 1;
                return Some((key, value));
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
    type Item = (Key, T);

    fn next(&mut self) -> Option<(Key, T)> {
        while let Some((idx, mut slot)) = self.slots.next() {
            if let Some(value) = std::mem::replace(&mut slot.value, None) {
                let key = Key::new(idx as u32, slot.version);
                self.num_left -= 1;
                return Some((key, value));
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num_left, Some(self.num_left))
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (Key, &'a T);

    fn next(&mut self) -> Option<(Key, &'a T)> {
        while let Some((idx, slot)) = self.slots.next() {
            if let Some(value) = &slot.value {
                let key = Key::new(idx as u32, slot.version);
                self.num_left -= 1;
                return Some((key, value));
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num_left, Some(self.num_left))
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (Key, &'a mut T);

    fn next(&mut self) -> Option<(Key, &'a mut T)> {
        while let Some((idx, slot)) = self.slots.next() {
            if let Some(value) = &mut slot.value {
                let key = Key::new(idx as u32, slot.version);
                self.num_left -= 1;
                return Some((key, value));
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num_left, Some(self.num_left))
    }
}

impl<'a, T> Iterator for Keys<'a, T> {
    type Item = Key;

    fn next(&mut self) -> Option<Key> {
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

impl<'a, T> IntoIterator for &'a SecondaryMap<T> {
    type Item = (Key, &'a T);
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut SecondaryMap<T> {
    type Item = (Key, &'a mut T);
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T> IntoIterator for SecondaryMap<T> {
    type Item = (Key, T);
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        let len = self.len();
        let mut it = self.slots.into_iter().enumerate();
        it.next(); // Skip sentinel.
        IntoIter {
            num_left: len,
            slots: it,
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
    struct SerdeSlot<T> {
        value: Option<T>,
        version: u32,
    }

    impl<T: Serialize> Serialize for Slot<T> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let serde_slot = SerdeSlot {
                version: self.version,
                value: self.value.as_ref(),
            };
            serde_slot.serialize(serializer)
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
            let serde_slot: SerdeSlot<T> = Deserialize::deserialize(deserializer)?;
            let occupied = serde_slot.version % 2 > 0;
            if occupied ^ serde_slot.value.is_some() {
                return Err(de::Error::custom(&"inconsistent occupation in Slot"));
            }

            Ok(Slot {
                value: serde_slot.value,
                version: serde_slot.version,
            })
        }
    }

    impl<T: Serialize> Serialize for SecondaryMap<T> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            self.slots.serialize(serializer)
        }
    }

    impl<'de, T: Deserialize<'de>> Deserialize<'de> for SecondaryMap<T> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            let mut slots: Vec<Slot<T>> = Deserialize::deserialize(deserializer)?;
            if slots.len() >= (1 << 32) - 1 {
                return Err(de::Error::custom(&"too many slots"));
            }

            // Ensure the first slot exists and is empty for the sentinel.
            if slots.get(0).map_or(true, |slot| slot.version % 2 > 0) {
                return Err(de::Error::custom(&"first slot not empty"));
            }

            slots[0] = Slot { value: None, version: 0 };

            let num_elems = slots.iter().map(|s| s.value.is_some() as usize).sum();

            Ok(SecondaryMap {
                num_elems,
                slots,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use ::*;
    use std::collections::HashMap;

    #[cfg(feature = "serde")]
    use serde_json;

    quickcheck! {
        fn qc_secmap_equiv_hashmap(operations: Vec<(u8, u32)>) -> bool {
            let mut hm = HashMap::new();
            let mut hm_keys = Vec::new();
            let mut unique_key = 0u32;
            let mut sm = SlotMap::new();
            let mut sec = SecondaryMap::new();
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
