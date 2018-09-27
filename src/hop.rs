// Necessary for the union differing on stable/nightly.
#![allow(unused_unsafe)] 

//! Contains the faster iteration, slower insertion/removal slot map
//! implementation.
//!
//! This data structure is essentially the same as a regular `SlotMap`, but
//! maintains extra information when inserting/removing elements that allows it
//! to 'hop over' vacant slots during iteration, making it potentially much
//! faster for iteration.
//!
//! The trade-off is that compared to a regular `SlotMap` insertion/removal is
//! roughly twice as slow. Random indexing has identical performance for both.

use std;
use std::iter::FusedIterator;
use std::mem::ManuallyDrop;
use std::ops::{Index, IndexMut};
use std::{fmt, ptr};

use super::{Key, Slottable};


// Metadata to maintain the freelist.
#[derive(Clone, Copy, Debug)]
struct FreeListEntry {
    next: u32,
    prev: u32,
    other_end: u32,
}

// Storage inside a slot or metadata for the freelist when vacant.
union SlotUnion<T: Slottable> {
    value: ManuallyDrop<T>,
    free: FreeListEntry,
}

// A slot, which represents storage for a value and a current version.
// Can be occupied or vacant.
struct Slot<T: Slottable> {
    u: SlotUnion<T>,
    version: u32, // Even = vacant, odd = occupied.
}

// Safe API to read a slot.
enum SlotContent<'a, T: 'a + Slottable> {
    Occupied(&'a T),
    Vacant(&'a FreeListEntry),
}

enum SlotContentMut<'a, T: 'a + Slottable> {
    OccupiedMut(&'a mut T),
    VacantMut(&'a mut FreeListEntry),
}

use self::SlotContent::{Occupied, Vacant};
use self::SlotContentMut::{OccupiedMut, VacantMut};

impl<T: Slottable> Slot<T> {
    // Is this slot occupied?
    #[inline(always)]
    pub fn occupied(&self) -> bool {
        self.version % 2 > 0
    }

    pub fn get(&self) -> SlotContent<T> {
        unsafe {
            if self.occupied() {
                Occupied(&*self.u.value)
            } else {
                Vacant(&self.u.free)
            }
        }
    }

    pub fn get_mut(&mut self) -> SlotContentMut<T> {
        unsafe {
            if self.occupied() {
                OccupiedMut(&mut *self.u.value)
            } else {
                VacantMut(&mut self.u.free)
            }
        }
    }
}

impl<T: Slottable> Drop for Slot<T> {
    fn drop(&mut self) {
        if std::mem::needs_drop::<T>() && self.occupied() {
            // This is safe because we checked that we're occupied.
            unsafe {
                ManuallyDrop::drop(&mut self.u.value);
            }
        }
    }
}

impl<T: Clone + Slottable> Clone for Slot<T> {
    fn clone(&self) -> Self {
        Self {
            u: match self.get() {
                Occupied(value) => SlotUnion {
                    value: ManuallyDrop::new(value.clone()),
                },
                Vacant(&free) => SlotUnion { free },
            },
            version: self.version,
        }
    }
}

impl<T: fmt::Debug + Slottable> fmt::Debug for Slot<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let mut builder = fmt.debug_struct("Slot");
        builder.field("version", &self.version);
        match self.get() {
            Occupied(value) => builder.field("value", value).finish(),
            Vacant(free) => builder.field("free", free).finish(),
        }
    }
}


/// Hop slot map, storage with stable unique keys.
///
/// See [crate documentation](index.html) for more details.
#[derive(Debug, Clone)]
pub struct HopSlotMap<T: Slottable> {
    slots: Vec<Slot<T>>,
    num_elems: u32,
}

impl<T: Slottable> HopSlotMap<T> {
    /// Construct a new, empty `HopSlotMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm: HopSlotMap<i32> = HopSlotMap::new();
    /// ```
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Creates an empty `HopSlotMap` with the given capacity.
    ///
    /// The slot map will not reallocate until it holds at least `capacity`
    /// elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm: HopSlotMap<i32> = HopSlotMap::with_capacity(10);
    /// ```
    pub fn with_capacity(capacity: usize) -> HopSlotMap<T> {
        // Create slots with sentinel at index 0.
        let mut slots = Vec::with_capacity(capacity + 1);
        slots.push(Slot {
            u: SlotUnion {
                free: FreeListEntry {
                    next: 0,
                    prev: 0,
                    other_end: 0,
                }
            },
            version: 0,
        });

        HopSlotMap { slots, num_elems: 0 }
    }

    /// Returns the number of elements in the slot map.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::with_capacity(10);
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
    /// let mut sm = HopSlotMap::new();
    /// let key = sm.insert("dummy");
    /// assert_eq!(sm.is_empty(), false);
    /// sm.remove(key);
    /// assert_eq!(sm.is_empty(), true);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.num_elems == 0
    }

    /// Returns the number of elements the `HopSlotMap` can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let sm: HopSlotMap<f64> = HopSlotMap::with_capacity(10);
    /// assert_eq!(sm.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize {
        // One slot is reserved for the freelist sentinel.
        self.slots.capacity() - 1
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `HopSlotMap`. The collection may reserve more space to
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
    /// let mut sm = HopSlotMap::new();
    /// sm.insert("foo");
    /// sm.reserve(32);
    /// assert!(sm.capacity() >= 33);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        // One slot is reserved for the freelist sentinel.
        let needed = (self.len() + additional)
            .saturating_sub(self.slots.len() - 1);
        self.slots.reserve(needed);
    }

    /// Returns `true` if the slot map contains `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::new();
    /// let key = sm.insert(42);
    /// assert_eq!(sm.contains_key(key), true);
    /// sm.remove(key);
    /// assert_eq!(sm.contains_key(key), false);
    /// ```
    pub fn contains_key(&self, key: Key) -> bool {
        self.slots
            .get(key.idx as usize)
            .map(|slot| slot.version == key.version.get())
            .unwrap_or(false)
    }

    /// Inserts a value into the slot map. Returns a unique `Key` that can be
    /// used to access this value.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the slot map equals
    /// 2<sup>32</sup> - 2.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::new();
    /// let key = sm.insert(42);
    /// assert_eq!(sm[key], 42);
    /// ```
    pub fn insert(&mut self, value: T) -> Key {
        self.insert_with_key(|_| value)
    }

    // Helper function to make using the freelist painless.
    // For that same ergonomy it uses u32, not usize as index.
    // Safe iff idx is a valid index and the slot at that index is vacant.
    unsafe fn freelist(&mut self, idx: u32) -> &mut FreeListEntry {
        // TODO: unchecked.
        // &mut self.slots[idx as usize].u.free
        &mut self.slots.get_unchecked_mut(idx as usize).u.free
    }


    /// Inserts a value given by `f` into the slot map. The `Key` where the
    /// value will be stored is passed into `f`. This is useful to store values
    /// that contain their own key.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the slot map equals
    /// 2<sup>32</sup> - 2.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::new();
    /// let key = sm.insert_with_key(|k| (k, 20));
    /// assert_eq!(sm[key], (key, 20));
    /// ```
    pub fn insert_with_key<F>(&mut self, f: F) -> Key
    where
        F: FnOnce(Key) -> T,
    {
        // In case f panics, we don't make any changes until we have the value.
        let new_num_elems = self.num_elems + 1;
        if new_num_elems == std::u32::MAX {
            panic!("HopSlotMap number of elements overflow");
        }

        // All unsafe accesses here are safe due to the invariants of the slot
        // map freelist.
        unsafe {
            let head = self.freelist(0).next;

            // We have a contiguous block of vacant slots starting at head.
            // Put our new element at the back slot.
            let front = head;
            let back = self.freelist(front).other_end;
            let slot_idx = back as usize;

            // Freelist is empty.
            if slot_idx == 0 {
                let key = Key::new(self.slots.len() as u32, 1);

                self.slots.push(Slot {
                    u: SlotUnion { value: ManuallyDrop::new(f(key)) },
                    version: 1,
                });
                self.num_elems = new_num_elems;
                return key;
            }

            // Compute value first in case f panics.
            let (key, value, occupied_version);
            {
                let slot = &mut self.slots[slot_idx];
                occupied_version = slot.version | 1;
                key = Key::new(slot_idx as u32, occupied_version);
                value = f(key);
            }

            // Update freelist.
            if front == back {
                // Used last slot in this block, move next one to head.
                let new_head = self.freelist(front).next;
                self.freelist(0).next = new_head;
                self.freelist(new_head).prev = 0;
            } else {
                // Continue using this block, only need to update other_ends.
                let new_back = back - 1;
                self.freelist(new_back).other_end = front;
                self.freelist(front).other_end = new_back;
            }

            // And finally insert the value.
            let slot = &mut self.slots[slot_idx];
            slot.version = occupied_version;
            slot.u.value = ManuallyDrop::new(value);
            self.num_elems = new_num_elems;
            key
        }
    }

    // Helper function to remove a value from a slot. Safe iff the slot is
    // occupied. Returns the value removed.
    #[inline(always)]
    unsafe fn remove_from_slot(&mut self, idx: usize) -> T {
        // Remove value from slot.
        let value = {
            let slot = self.slots.get_unchecked_mut(idx);
            slot.version = slot.version.wrapping_add(1);
            ptr::read(&*slot.u.value)
        };

        // This is safe and can't underflow because of the sentinel element at
        // the start.
        let left_vacant = !self.slots.get_unchecked(idx - 1).occupied();
        let right_vacant = self.slots.get(idx + 1).map_or(false, |s| !s.occupied());

        // Maintain freelist by either appending/prepending this slot to a
        // contiguous block to the left or right, merging the two blocks to the
        // left and right or inserting a new block.
        let i = idx as u32;
        // use std::hint::unreachable_unchecked;

        match (left_vacant, right_vacant) {
            (false, false) => {
                // New block, insert it at the head.
                let old_head = self.freelist(0).next;
                self.freelist(0).next = i;
                self.freelist(old_head).prev = i;
                *self.freelist(i) = FreeListEntry {
                    other_end: i,
                    next: old_head,
                    prev: 0,
                };
            },

            (false, true) => {
                // Prepend to vacant block on right.
                let front_data = *self.freelist(i + 1);
                *self.freelist(i) = front_data;
                self.freelist(front_data.other_end).other_end = i;

                // Since the start of this block moved we must update our
                // neighbours.
                self.freelist(front_data.prev).next = i;
                self.freelist(front_data.next).prev = i;
            },

            (true, false) => {
                // Append to vacant block on left.
                let front = self.freelist(i - 1).other_end;
                self.freelist(i).other_end = front;
                self.freelist(front).other_end = i;
            },

            (true, true) => {
                // We must merge left and right.
                // First snip right out of the freelist.
                let right = *self.freelist(i + 1);
                self.freelist(right.prev).next = right.next;
                self.freelist(right.next).prev = right.prev;

                // Now update endpoints.
                let front = self.freelist(i - 1).other_end;
                let back = right.other_end;
                self.freelist(front).other_end = back;
                self.freelist(back).other_end = front;
            }
        }

        self.num_elems -= 1;

        value
    }

    /// Removes a key from the slot map, returning the value at the key if the
    /// key was not previously removed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::new();
    /// let key = sm.insert(42);
    /// assert_eq!(sm.remove(key), Some(42));
    /// assert_eq!(sm.remove(key), None);
    /// ```
    pub fn remove(&mut self, key: Key) -> Option<T> {
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
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::new();
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
        F: FnMut(Key, &mut T) -> bool,
    {
        let len = self.slots.len();
        let mut i = 0;
        while i < len {
            let should_remove = {
                // This is safe because removing elements does not shrink slots.
                let slot = unsafe { self.slots.get_unchecked_mut(i) };
                let version = slot.version;

                match slot.get_mut() {
                    OccupiedMut(value) => {
                        let key = Key::new(i as u32, version);
                        !f(key, value)
                    },
                    VacantMut(free) => {
                        i = free.other_end as usize;
                        false
                    },
                }
            };

            if should_remove {
                // This is safe because we know that the slot was occupied.
                unsafe { self.remove_from_slot(i) };
            }

            i += 1;
        }
    }

    /// Clears the slot map. Keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::new();
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
    /// Even if the iterator is not (fully) consumed, when it goes out of scope
    /// all remaining elements are cleared.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::new();
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
    /// let mut sm = HopSlotMap::new();
    /// let key = sm.insert("bar");
    /// assert_eq!(sm.get(key), Some(&"bar"));
    /// sm.remove(key);
    /// assert_eq!(sm.get(key), None);
    /// ```
    pub fn get(&self, key: Key) -> Option<&T> {
        // This is safe because we check version first and Key always contains
        // an odd version, thus we are occupied.
        self.slots
            .get(key.idx as usize)
            .filter(|slot| slot.version == key.version.get())
            .map(|slot| unsafe { &*slot.u.value })
    }

    /// Returns a reference to the value corresponding to the key without
    /// version or bounds checking.
    ///
    /// # Safety
    ///
    /// This should only be used if `contains_key(key)` is true. Otherwise it is
    /// dangerous undefined behavior.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::new();
    /// let key = sm.insert("bar");
    /// assert_eq!(unsafe { sm.get_unchecked(key) }, &"bar");
    /// sm.remove(key);
    /// // sm.get_unchecked(key) is now dangerous!
    /// ```
    pub unsafe fn get_unchecked(&self, key: Key) -> &T {
        &self.slots.get_unchecked(key.idx as usize).u.value
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::new();
    /// let key = sm.insert(3.5);
    /// if let Some(x) = sm.get_mut(key) {
    ///     *x += 3.0;
    /// }
    /// assert_eq!(sm[key], 6.5);
    /// ```
    pub fn get_mut(&mut self, key: Key) -> Option<&mut T> {
        // This is safe because we check version first and Key always contains
        // an odd version, thus we are occupied.
        self.slots
            .get_mut(key.idx as usize)
            .filter(|slot| slot.version == key.version.get())
            .map(|slot| unsafe { &mut *slot.u.value })
    }

    /// Returns a mutable reference to the value corresponding to the key
    /// without version or bounds checking.
    ///
    /// # Safety
    ///
    /// This should only be used if `contains_key(key)` is true. Otherwise it is
    /// dangerous undefined behavior.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::new();
    /// let key = sm.insert("foo");
    /// unsafe { *sm.get_unchecked_mut(key) = "bar" };
    /// assert_eq!(sm[key], "bar");
    /// sm.remove(key);
    /// // sm.get_unchecked_mut(key) is now dangerous!
    /// ```
    pub unsafe fn get_unchecked_mut(&mut self, key: Key) -> &mut T {
        &mut self.slots.get_unchecked_mut(key.idx as usize).u.value
    }

    /// An iterator visiting all key-value pairs in arbitrary order. The
    /// iterator element type is `(Key, &'a T)`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::new();
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
            cur: unsafe {
                self.slots.get_unchecked(0).u.free.other_end as usize + 1
            },
            num_left: self.len(),
            slots: &self.slots[..],
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
    /// let mut sm = HopSlotMap::new();
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
            cur: 0,
            num_left: self.len(),
            slots: &mut self.slots[..],
        }
    }

    /// An iterator visiting all keys in arbitrary order. The iterator element
    /// type is `Key`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::new();
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
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::new();
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
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = HopSlotMap::new();
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

impl<T: Slottable> Default for HopSlotMap<T> {
    fn default() -> Self {
        HopSlotMap::new()
    }
}

impl<T: Slottable> Index<Key> for HopSlotMap<T> {
    type Output = T;

    fn index(&self, key: Key) -> &T {
        match self.get(key) {
            Some(r) => r,
            None => panic!("invalid HopSlotMap key used"),
        }
    }
}

impl<T: Slottable> IndexMut<Key> for HopSlotMap<T> {
    fn index_mut(&mut self, key: Key) -> &mut T {
        match self.get_mut(key) {
            Some(r) => r,
            None => panic!("invalid HopSlotMap key used"),
        }
    }
}

// Iterators.
/// A draining iterator for `HopSlotMap`.
#[derive(Debug)]
pub struct Drain<'a, T: 'a + Slottable> {
    cur: usize,
    num_left: usize,
    sm: &'a mut HopSlotMap<T>,
}

/// An iterator that moves key-value pairs out of a `HopSlotMap`.
#[derive(Debug)]
pub struct IntoIter<T: Slottable> {
    cur: usize,
    num_left: usize,
    slots: Vec<Slot<T>>,
}

/// An iterator over the key-value pairs in a `HopSlotMap`.
#[derive(Debug)]
pub struct Iter<'a, T: 'a + Slottable> {
    cur: usize,
    num_left: usize,
    slots: &'a [Slot<T>],
}

/// A mutable iterator over the key-value pairs in a `HopSlotMap`.
#[derive(Debug)]
pub struct IterMut<'a, T: 'a + Slottable> {
    cur: usize,
    num_left: usize,
    slots: &'a mut [Slot<T>],
}

/// An iterator over the keys in a `HopSlotMap`.
#[derive(Debug)]
pub struct Keys<'a, T: 'a + Slottable> {
    inner: Iter<'a, T>,
}

/// An iterator over the values in a `HopSlotMap`.
#[derive(Debug)]
pub struct Values<'a, T: 'a + Slottable> {
    inner: Iter<'a, T>,
}

/// A mutable iterator over the values in a `HopSlotMap`.
#[derive(Debug)]
pub struct ValuesMut<'a, T: 'a + Slottable> {
    inner: IterMut<'a, T>,
}

impl<'a, T: Slottable> Iterator for Drain<'a, T> {
    type Item = (Key, T);

    fn next(&mut self) -> Option<(Key, T)> {
        if self.cur >= self.sm.slots.len() { return None; }

        let (idx, version) = {
            let slot = &self.sm.slots[self.cur];
            match slot.get() {
                Occupied(_) => (self.cur, slot.version),
                Vacant(free) => {
                    // Skip block of contiguous vacant slots.
                    let idx = free.other_end as usize + 1;
                    if idx >= self.sm.slots.len() { return None; }
                    (idx, self.sm.slots[idx].version)
                }
            }
        };

        self.cur = idx + 1;
        self.num_left -= 1;
        Some((Key::new(idx as u32, version), unsafe { self.sm.remove_from_slot(idx) }))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num_left, Some(self.num_left))
    }
}

impl<'a, T: Slottable> Drop for Drain<'a, T> {
    fn drop(&mut self) {
        self.for_each(|_drop| {});
    }
}

impl<T: Slottable> Iterator for IntoIter<T> {
    type Item = (Key, T);

    fn next(&mut self) -> Option<(Key, T)> {
        if self.cur >= self.slots.len() { return None; }

        let idx = match self.slots[self.cur].get() {
            Occupied(_) => self.cur,
            Vacant(free) => {
                // Skip block of contiguous vacant slots.
                let idx = free.other_end as usize + 1;
                if idx >= self.slots.len() { return None; }
                idx
            },
        };

        self.cur = idx + 1;
        self.num_left -= 1;
        let slot = &mut self.slots[idx];
        let key = Key::new(idx as u32, slot.version);
        slot.version = 0; // Prevent dropping after extracting the value.
        Some((key, unsafe { ptr::read(&*slot.u.value) }))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num_left, Some(self.num_left))
    }
}

impl<'a, T: Slottable> Iterator for Iter<'a, T> {
    type Item = (Key, &'a T);

    fn next(&mut self) -> Option<(Key, &'a T)> {
        // All unchecked indices are safe due to the invariants of the freelist
        // and that num_left guarantees there is another element.
        if self.num_left == 0 { return None; }
        self.num_left -= 1;

        let idx = match unsafe { self.slots.get_unchecked(self.cur).get() } {
            Occupied(_) => self.cur,
            Vacant(free) => free.other_end as usize + 1,
        };

        self.cur = idx + 1;
        let slot = unsafe { self.slots.get_unchecked(idx) };
        Some((Key::new(idx as u32, slot.version), unsafe { &*slot.u.value }))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num_left, Some(self.num_left))
    }
}

impl<'a, T: Slottable> Iterator for IterMut<'a, T> {
    type Item = (Key, &'a mut T);

    fn next(&mut self) -> Option<(Key, &'a mut T)> {
        if self.cur >= self.slots.len() { return None; }

        let idx = match self.slots[self.cur].get() {
            Occupied(_) => self.cur,
            Vacant(free) => {
                // Skip block of contiguous vacant slots.
                let idx = free.other_end as usize + 1;
                if idx >= self.slots.len() { return None; }
                idx
            }
        };

        self.cur = idx + 1;
        self.num_left -= 1;

        // Unsafe necessary because Rust can't deduce that we won't return multiple references to
        // the same value.
        let slot = &mut self.slots[idx];
        let version = slot.version;
        let value_ref = unsafe { &mut *(&mut *slot.u.value as *mut T) };
        Some((Key::new(idx as u32, version), value_ref))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num_left, Some(self.num_left))
    }
}

impl<'a, T: Slottable> Iterator for Keys<'a, T> {
    type Item = Key;

    fn next(&mut self) -> Option<Key> {
        self.inner.next().map(|(key, _)| key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T: Slottable> Iterator for Values<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.inner.next().map(|(_, value)| value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T: Slottable> Iterator for ValuesMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        self.inner.next().map(|(_, value)| value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T: Slottable> IntoIterator for &'a HopSlotMap<T> {
    type Item = (Key, &'a T);
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: Slottable> IntoIterator for &'a mut HopSlotMap<T> {
    type Item = (Key, &'a mut T);
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T: Slottable> IntoIterator for HopSlotMap<T> {
    type Item = (Key, T);
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            cur: 0,
            num_left: self.len(),
            slots: self.slots,
        }
    }
}

impl<'a, T: Slottable> FusedIterator for Iter<'a, T> {}
impl<'a, T: Slottable> FusedIterator for IterMut<'a, T> {}
impl<'a, T: Slottable> FusedIterator for Keys<'a, T> {}
impl<'a, T: Slottable> FusedIterator for Values<'a, T> {}
impl<'a, T: Slottable> FusedIterator for ValuesMut<'a, T> {}
impl<'a, T: Slottable> FusedIterator for Drain<'a, T> {}
impl<T: Slottable> FusedIterator for IntoIter<T> {}

impl<'a, T: Slottable> ExactSizeIterator for Iter<'a, T> {}
impl<'a, T: Slottable> ExactSizeIterator for IterMut<'a, T> {}
impl<'a, T: Slottable> ExactSizeIterator for Keys<'a, T> {}
impl<'a, T: Slottable> ExactSizeIterator for Values<'a, T> {}
impl<'a, T: Slottable> ExactSizeIterator for ValuesMut<'a, T> {}
impl<'a, T: Slottable> ExactSizeIterator for Drain<'a, T> {}
impl<T: Slottable> ExactSizeIterator for IntoIter<T> {}

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

    impl<T: Serialize + Slottable> Serialize for Slot<T> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let safe_slot = SerdeSlot {
                version: self.version,
                value: match self.get() {
                    Occupied(value) => Some(value),
                    Vacant(_) => None,
                },
            };
            safe_slot.serialize(serializer)
        }
    }

    impl<'de, T: Slottable> Deserialize<'de> for Slot<T>
    where
        T: Deserialize<'de>,
    {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            let safe_slot: SerdeSlot<T> = Deserialize::deserialize(deserializer)?;
            let occupied = safe_slot.version % 2 > 0;
            if occupied ^ safe_slot.value.is_some() {
                return Err(de::Error::custom(&"inconsistent occupation in Slot"));
            }

            Ok(Slot {
                u: match safe_slot.value {
                    Some(value) => SlotUnion {
                        value: ManuallyDrop::new(value)
                    },
                    None => SlotUnion {
                        free: FreeListEntry { next: 0, prev: 0, other_end: 0 },
                    },
                },
                version: safe_slot.version,
            })
        }
    }

    impl<T: Serialize + Slottable> Serialize for HopSlotMap<T> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            self.slots.serialize(serializer)
        }
    }

    impl<'de, T: Deserialize<'de> + Slottable> Deserialize<'de> for HopSlotMap<T> {
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

            slots[0].u.free = FreeListEntry {
                next: 0,
                prev: 0,
                other_end: 0,
            };

            // We have our slots, rebuild freelist.
            let mut num_elems = 0;
            let mut prev = 0;
            let mut i = 0;
            while i < slots.len() {
                // i is the start of a contiguous block of vacant slots.
                let front = i;
                while i < slots.len() && !slots[i].occupied() {
                    i += 1;
                }
                let back = i - 1;

                // Update freelist.
                unsafe {
                    slots[back].u.free.other_end = front as u32;
                    slots[prev].u.free.next = front as u32;
                    slots[front].u.free = FreeListEntry {
                        next: 0,
                        prev: prev as u32,
                        other_end: back as u32,
                    };
                }

                prev = front;

                // Skip occupied slots.
                while i < slots.len() && slots[i].occupied() {
                    num_elems += 1;
                    i += 1;
                }
            }

            Ok(HopSlotMap {
                num_elems,
                slots,
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

    #[cfg(feature = "unstable")]
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
                let mut sm = HopSlotMap::new();
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
            let mut sm = HopSlotMap::new();
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
        let mut sm = HopSlotMap::new();
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
        let de: HopSlotMap<(Key, i32)> = serde_json::from_str(&ser).unwrap();
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
        let mut sm = HopSlotMap::new();
        let k = sm.insert(5i32);
        sm.remove(k);

        let ser = serde_json::to_string(&sm).unwrap();
        let mut de: HopSlotMap<i32> = serde_json::from_str(&ser).unwrap();

        de.insert(0);
        de.insert(1);
        de.insert(2);
        assert_eq!(de.len(), 3);
    }
}
