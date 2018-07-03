//! Contains the sparse slot map implementation.
use std;
use std::fmt;
use std::iter::FusedIterator;
use std::mem::ManuallyDrop;
use std::ops::{Index, IndexMut};

/// Key used to access stored values in a slot map.
///
/// Do not use a key from one slot map in another. The behavior is safe but
/// non-sensical (and might panic in case of out-of-bounds). Keys implement
/// `Ord` so they can be used in e.g.
/// [`BTreeMap`](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html)
/// but their order is arbitrary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Key {
    idx: u32,
    version: u32,
}

/// Slot map, storage with stable unique keys.
///
/// See [crate documentation](../index.html) for more details.
#[derive(Debug, Clone)]
pub struct SparseSlotMap<T> {
    slots: Vec<Slot<T>>,
    first_free: usize,
    num_elems: u32,
}

struct Slot<T> {
    value: ManuallyDrop<T>,

    // Even = vacant, odd = occupied.
    version: u32,

    // This could be in an union with value, but that requires unstable unions
    // without copy. This isn't available in stable Rust yet.
    next_free: u32,
}

impl<T> Slot<T> {
    fn occupied(&self) -> bool {
        self.version % 2 > 0
    }
}

impl<T> Drop for Slot<T> {
    fn drop(&mut self) {
        if self.occupied() {
            unsafe {
                ManuallyDrop::drop(&mut self.value);
            }
        }
    }
}

impl<T> Clone for Slot<T>
where
    T: Clone,
{
    fn clone(&self) -> Slot<T> {
        Slot::<T> {
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

impl<T> fmt::Debug for Slot<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        if self.occupied() {
            write!(
                fmt,
                "SparseSlotMap {{ version: {}, value: {:?} }}",
                self.version, self.value
            )
        } else {
            write!(
                fmt,
                "SparseSlotMap {{ version: {}, next_free: {:?} }}",
                self.version, self.next_free
            )
        }
    }
}

impl<T> SparseSlotMap<T> {
    /// Construct a new, empty `SparseSlotMap`.
    ///
    /// The slot map will not allocate until values are inserted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm: SparseSlotMap<i32> = SparseSlotMap::new();
    /// ```
    pub fn new() -> SparseSlotMap<T> {
        SparseSlotMap::<T>::with_capacity(0)
    }

    /// Creates an empty `SparseSlotMap` with the given capacity.
    ///
    /// The slot map will not reallocate until it holds at least `capacity`
    /// elements. If `capacity` is 0, the slot map will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm: SparseSlotMap<i32> = SparseSlotMap::with_capacity(10);
    /// ```
    pub fn with_capacity(capacity: usize) -> SparseSlotMap<T> {
        SparseSlotMap {
            slots: Vec::with_capacity(capacity),
            first_free: 0,
            num_elems: 0,
        }
    }

    /// Returns the number of elements in the slot map.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SparseSlotMap::with_capacity(10);
    /// sm.insert("len() counts actual elements, not capacity");
    /// let key = sm.insert("removed elements don't count either");
    /// sm.remove(key);
    /// assert_eq!(sm.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.num_elems as usize
    }

    /// Returns the number of elements the `SparseSlotMap` can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let sm: SparseSlotMap<f64> = SparseSlotMap::with_capacity(10);
    /// assert_eq!(sm.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.slots.capacity()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `SparseSlotMap`. The collection may reserve more space to
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
    /// let mut sm = SparseSlotMap::new();
    /// sm.insert("foo");
    /// sm.reserve(32);
    /// assert!(sm.capacity() >= 33);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.slots.reserve(additional);
    }

    /// Inserts a value into the slot map. Returns a unique
    /// [`Key`](struct.Key.html) that can be used to access this value.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the slot map overflows a `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SparseSlotMap::new();
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
    /// Panics if the number of elements in the slot map overflows a `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SparseSlotMap::new();
    /// let key = sm.insert_with_key(|k| (k, 20));
    /// assert_eq!(sm[key], (key, 20));
    /// ```
    pub fn insert_with_key<F>(&mut self, f: F) -> Key
    where
        F: FnOnce(Key) -> T,
    {
        let new_num_elems = self.num_elems
            .checked_add(1)
            .expect("SparseSlotMap number of elements overflow");

        // Get an unoccupied slot.
        let idx = self.first_free;
        let slot = unsafe {
            if idx >= self.slots.len() {
                self.slots.push(Slot {
                    value: std::mem::uninitialized(),
                    version: 0,
                    next_free: 0,
                });
                self.first_free += 1;
                self.slots.get_unchecked_mut(idx)
            } else {
                let slot = self.slots.get_unchecked_mut(idx);
                self.first_free = slot.next_free as usize;
                slot
            }
        };

        let key = Key {
            idx: idx as u32,
            version: slot.version + 1,
        };

        // Get value to insert and increment version to mark the slot occupied.
        slot.value = ManuallyDrop::new(f(key));
        slot.version += 1;
        self.num_elems = new_num_elems;
        key
    }

    /// Returns `true` if the slot map contains `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SparseSlotMap::new();
    /// let key = sm.insert(42);
    /// assert_eq!(sm.contains(key), true);
    /// sm.remove(key);
    /// assert_eq!(sm.contains(key), false);
    /// ```
    pub fn contains(&self, key: Key) -> bool {
        return self.slots[key.idx as usize].version == key.version;
    }

    /// Removes a key from the slot map, returning the value at the key if the
    /// key was not previously removed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SparseSlotMap::new();
    /// let key = sm.insert(42);
    /// assert_eq!(sm.remove(key), Some(42));
    /// assert_eq!(sm.remove(key), None);
    /// ```
    pub fn remove(&mut self, key: Key) -> Option<T> {
        let slot = &mut self.slots[key.idx as usize];
        if slot.version != key.version {
            return None;
        }

        slot.next_free = self.first_free as u32;
        slot.version = slot.version.wrapping_add(1);
        self.first_free = key.idx as usize;
        self.num_elems -= 1;
        Some(std::mem::replace(&mut *slot.value, unsafe {
            std::mem::uninitialized()
        }))
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SparseSlotMap::new();
    /// let key = sm.insert("bar");
    /// assert_eq!(sm.get(key), Some(&"bar"));
    /// sm.remove(key);
    /// assert_eq!(sm.get(key), None);
    pub fn get(&self, key: Key) -> Option<&T> {
        let slot = &self.slots[key.idx as usize];
        if slot.version == key.version {
            Some(&slot.value)
        } else {
            None
        }
    }

    /// Returns a reference to the value corresponding to the key without
    /// version or bounds checking.
    ///
    /// # Safety
    ///
    /// This should only be used if `contains(key)` is true. Otherwise it is
    /// potentially unsafe.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SparseSlotMap::new();
    /// let key = sm.insert("bar");
    /// assert_eq!(unsafe { sm.get_unchecked(key) }, &"bar");
    /// sm.remove(key);
    /// // sm.get_unchecked(key) is now dangerous!
    pub unsafe fn get_unchecked(&self, key: Key) -> &T {
        &self.slots.get_unchecked(key.idx as usize).value
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SparseSlotMap::new();
    /// let key = sm.insert(3.5);
    /// if let Some(x) = sm.get_mut(key) {
    ///     *x += 3.0;
    /// }
    /// assert_eq!(sm[key], 6.5);
    pub fn get_mut(&mut self, key: Key) -> Option<&mut T> {
        let slot = &mut self.slots[key.idx as usize];
        if slot.version == key.version {
            Some(&mut slot.value)
        } else {
            None
        }
    }

    /// Returns a mutable reference to the value corresponding to the key
    /// without version or bounds checking.
    ///
    /// # Safety
    ///
    /// This should only be used if `contains(key)` is true. Otherwise it is
    /// potentially unsafe.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SparseSlotMap::new();
    /// let key = sm.insert("foo");
    /// unsafe { *sm.get_unchecked_mut(key) = "bar" };
    /// assert_eq!(sm[key], "bar");
    /// sm.remove(key);
    /// // sm.get_unchecked_mut(key) is now dangerous!
    pub unsafe fn get_unchecked_mut(&mut self, key: Key) -> &mut T {
        &mut self.slots.get_unchecked_mut(key.idx as usize).value
    }

    /// An iterator visiting all key-value pairs in arbitrary order. The
    /// iterator element type is `(Key, &'a T)`.
    pub fn iter(&self) -> Iter<T> {
        Iter::<T> {
            slots: self.slots.iter(),
            cur: 0,
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order, with
    /// mutable references to the values. The iterator element type is
    /// `(Key, &'a mut T)`.
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut::<T> {
            slots: self.slots.iter_mut(),
            cur: 0,
        }
    }

    /// An iterator visiting all keys in arbitrary order. The iterator element
    /// type is `Key`.
    pub fn keys(&self) -> Keys<T> {
        Keys::<T> { inner: self.iter() }
    }

    /// An iterator visiting all values in arbitrary order. The iterator element
    /// type is `&'a T`.
    pub fn values(&self) -> Values<T> {
        Values::<T> { inner: self.iter() }
    }

    /// An iterator visiting all values mutably in arbitrary order. The iterator
    /// element type is `&mut 'a T`.
    pub fn values_mut(&mut self) -> ValuesMut<T> {
        ValuesMut::<T> {
            inner: self.iter_mut(),
        }
    }
}

impl<T> Default for SparseSlotMap<T> {
    fn default() -> Self {
        SparseSlotMap::new()
    }
}

impl<T> Index<Key> for SparseSlotMap<T> {
    type Output = T;

    fn index(&self, key: Key) -> &T {
        match self.get(key) {
            Some(r) => r,
            None => panic!("removed SparseSlotMap key used"),
        }
    }
}

impl<T> IndexMut<Key> for SparseSlotMap<T> {
    fn index_mut(&mut self, key: Key) -> &mut T {
        match self.get_mut(key) {
            Some(r) => r,
            None => panic!("removed SparseSlotMap key used"),
        }
    }
}

// Iterators.
/// An iterator over the `(key, value)` pairs in a `SparseSlotMap`.
#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    slots: std::slice::Iter<'a, Slot<T>>,
    cur: usize,
}

/// A mutable iterator over the `(key, value)` pairs in a `SparseSlotMap`.
#[derive(Debug)]
pub struct IterMut<'a, T: 'a> {
    slots: std::slice::IterMut<'a, Slot<T>>,
    cur: usize,
}

/// An iterator over the keys in a `SparseSlotMap`.
#[derive(Debug)]
pub struct Keys<'a, T: 'a> {
    inner: Iter<'a, T>,
}

/// An iterator over the values in a `SparseSlotMap`.
#[derive(Debug)]
pub struct Values<'a, T: 'a> {
    inner: Iter<'a, T>,
}

/// A mutable iterator over the values in a `SparseSlotMap`.
#[derive(Debug)]
pub struct ValuesMut<'a, T: 'a> {
    inner: IterMut<'a, T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (Key, &'a T);

    fn next(&mut self) -> Option<(Key, &'a T)> {
        while let Some(slot) = self.slots.next() {
            let key = Key {
                idx: self.cur as u32,
                version: slot.version,
            };
            self.cur += 1;

            if slot.occupied() {
                return Some((key, &slot.value));
            }
        }

        None
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (Key, &'a mut T);

    fn next(&mut self) -> Option<(Key, &'a mut T)> {
        while let Some(slot) = self.slots.next() {
            let key = Key {
                idx: self.cur as u32,
                version: slot.version,
            };
            self.cur += 1;

            if slot.occupied() {
                return Some((key, &mut slot.value));
            }
        }

        None
    }
}

impl<'a, T> Iterator for Keys<'a, T> {
    type Item = Key;

    fn next(&mut self) -> Option<Key> {
        while let Some((key, _)) = self.inner.next() {
            return Some(key);
        }

        None
    }
}

impl<'a, T> Iterator for Values<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        while let Some((_, value)) = self.inner.next() {
            return Some(value);
        }

        None
    }
}

impl<'a, T> Iterator for ValuesMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        while let Some((_, value)) = self.inner.next() {
            return Some(value);
        }

        None
    }
}

impl<'a, T> FusedIterator for Iter<'a, T> {}
impl<'a, T> FusedIterator for IterMut<'a, T> {}
impl<'a, T> FusedIterator for Keys<'a, T> {}
impl<'a, T> FusedIterator for Values<'a, T> {}
impl<'a, T> FusedIterator for ValuesMut<'a, T> {}
