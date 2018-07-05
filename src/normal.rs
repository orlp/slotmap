//! Contains the slot map implementation.
use std;
use std::iter::FusedIterator;
use std::mem::ManuallyDrop;
use std::ops::{Index, IndexMut};
use std::{fmt, ptr};

use super::Key;

// Little helper function to turn (bool, T) into Option<T>.
fn to_option<T>(b: bool, some: T) -> Option<T> {
    if b {
        Some(some)
    } else {
        None
    }
}

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
/// See [crate documentation](../index.html) for more details.
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
        let needed = self.len() + additional - self.slots.len();
        self.slots.reserve(needed.max(0));
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

    /// Inserts a value into the slot map. Returns a unique
    /// [`Key`](../struct.Key.html) that can be used to access this value.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the slot map overflows a `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
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
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert_with_key(|k| (k, 20));
    /// assert_eq!(sm[key], (key, 20));
    /// ```
    pub fn insert_with_key<F>(&mut self, f: F) -> Key
    where
        F: FnOnce(Key) -> T,
    {
        self.num_elems = self
            .num_elems
            .checked_add(1)
            .expect("SlotMap number of elements overflow");

        let idx = self.free_head;

        let key;
        if idx >= self.slots.len() {
            key = Key {
                idx: idx as u32,
                version: 1,
            };

            self.slots.push(Slot {
                value: ManuallyDrop::new(f(key)),
                version: 1,
                next_free: 0,
            });
            self.free_head = self.slots.len();
        } else {
            // This is safe because we checked that idx < self.slots.len().
            let slot = unsafe { self.slots.get_unchecked_mut(idx) };
            let occupied_version = slot.version | 1;
            key = Key {
                idx: idx as u32,
                version: occupied_version,
            };

            slot.version = occupied_version;
            slot.value = ManuallyDrop::new(f(key));
            self.free_head = slot.next_free as usize;
        }

        key
    }

    /// Returns `true` if the slot map contains `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert(42);
    /// assert_eq!(sm.contains(key), true);
    /// sm.remove(key);
    /// assert_eq!(sm.contains(key), false);
    /// ```
    pub fn contains(&self, key: Key) -> bool {
        self.slots[key.idx as usize].version == key.version
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
    pub fn remove(&mut self, key: Key) -> Option<T> {
        let slot = &mut self.slots[key.idx as usize];
        if slot.version != key.version {
            return None;
        }

        // Maintain freelist.
        slot.next_free = self.free_head as u32;
        self.free_head = key.idx as usize;
        self.num_elems -= 1;

        slot.version = slot.version.wrapping_add(1);
        // This is safe because we know that the slot was occupied. We know this
        // because keys are only ever given out with an odd version and we
        // checked that slot.version == key.version.
        unsafe { Some(ptr::read(&*slot.value)) }
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
    pub fn get(&self, key: Key) -> Option<&T> {
        let slot = &self.slots[key.idx as usize];
        to_option(slot.version == key.version, &slot.value)
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
    /// let mut sm = SlotMap::new();
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
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert(3.5);
    /// if let Some(x) = sm.get_mut(key) {
    ///     *x += 3.0;
    /// }
    /// assert_eq!(sm[key], 6.5);
    pub fn get_mut(&mut self, key: Key) -> Option<&mut T> {
        let slot = &mut self.slots[key.idx as usize];
        to_option(slot.version == key.version, &mut slot.value)
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
    /// let mut sm = SlotMap::new();
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

impl<T> Default for SlotMap<T> {
    fn default() -> Self {
        SlotMap::new()
    }
}

impl<T> Index<Key> for SlotMap<T> {
    type Output = T;

    fn index(&self, key: Key) -> &T {
        match self.get(key) {
            Some(r) => r,
            None => panic!("removed SlotMap key used"),
        }
    }
}

impl<T> IndexMut<Key> for SlotMap<T> {
    fn index_mut(&mut self, key: Key) -> &mut T {
        match self.get_mut(key) {
            Some(r) => r,
            None => panic!("removed SlotMap key used"),
        }
    }
}

// Iterators.
/// An iterator over the `(key, value)` pairs in a `SlotMap`.
#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    slots: std::slice::Iter<'a, Slot<T>>,
    cur: usize,
}

/// A mutable iterator over the `(key, value)` pairs in a `SlotMap`.
#[derive(Debug)]
pub struct IterMut<'a, T: 'a> {
    slots: std::slice::IterMut<'a, Slot<T>>,
    cur: usize,
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

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (Key, &'a T);

    fn next(&mut self) -> Option<(Key, &'a T)> {
        while let Some(slot) = self.slots.next() {
            let idx = self.cur as u32;
            self.cur += 1;

            if slot.occupied() {
                let key = Key {
                    idx,
                    version: slot.version,
                };

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
            let idx = self.cur as u32;
            self.cur += 1;

            if slot.occupied() {
                let key = Key {
                    idx,
                    version: slot.version,
                };

                return Some((key, &mut slot.value));
            }
        }

        None
    }
}

impl<'a, T> Iterator for Keys<'a, T> {
    type Item = Key;

    fn next(&mut self) -> Option<Key> {
        if let Some((key, _)) = self.inner.next() {
            return Some(key);
        }

        None
    }
}

impl<'a, T> Iterator for Values<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        if let Some((_, value)) = self.inner.next() {
            return Some(value);
        }

        None
    }
}

impl<'a, T> Iterator for ValuesMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        if let Some((_, value)) = self.inner.next() {
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
                value: to_option(self.occupied(), &*self.value),
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
            if slots.len() >= 1 << 32 {
                return Err(de::Error::custom(&"too many slots"));
            }

            // We have our slots, rebuild freelist. Find first free slot.
            let first_free = slots
                .iter()
                .position(|s| s.occupied())
                .unwrap_or_else(|| slots.len());

            let mut next_free = first_free;
            let mut num_elems = first_free;
            for (i, slot) in slots.iter_mut().enumerate().skip(first_free) {
                if slot.occupied() {
                    num_elems += 1;
                } else {
                    slot.next_free = next_free as u32;
                    next_free = i;
                }
            }

            Ok(SlotMap {
                slots,
                num_elems: num_elems as u32,
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

            for (op, val) in operations {
                match op % 3 {
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

                        if hm.contains_key(hm_key) != sm.contains(sm_key) ||
                           hm.get(hm_key) != sm.get(sm_key) {
                            return false;
                        }
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

        let mut smkv: Vec<_> = sm.iter().collect();
        let mut dekv: Vec<_> = de.iter().collect();
        smkv.sort();
        dekv.sort();
        assert_eq!(smkv, dekv);
    }
}
