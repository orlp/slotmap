use std;
use std::fmt;
use std::mem::ManuallyDrop;

#[cfg(feature = "serde")]
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

pub struct Slot<T> {
    // A value when occupied, uninitialized memory otherwise.
    pub value: ManuallyDrop<T>,

    // Even = vacant, odd = occupied.
    pub version: u32,

    // This could be in an union with value, but that requires unstable unions
    // without copy. This isn't available in stable Rust yet.
    pub next_free: u32,
}

impl<T> Slot<T> {
    pub fn occupied(&self) -> bool {
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

#[cfg(feature = "serde")]
#[derive(Serialize, Deserialize)]
struct SafeSlot<T> {
    // Used for serializing.
    value: Option<T>,
    version: u32,
}

#[cfg(feature = "serde")]
impl<'a, T> From<SafeSlot<T>> for Slot<T> {
    fn from(safe_slot: SafeSlot<T>) -> Self {
        Slot {
            value: match safe_slot.value {
                Some(value) => ManuallyDrop::new(value),
                None => unsafe { std::mem::uninitialized() },
            },
            version: safe_slot.version,
            next_free: 0,
        }
    }
}

#[cfg(feature = "serde")]
impl<'a, T> From<&'a Slot<T>> for SafeSlot<&'a T> {
    fn from(slot: &'a Slot<T>) -> Self {
        SafeSlot {
            value: match slot.occupied() {
                true => Some(&*slot.value),
                false => None,
            },
            version: slot.version,
        }
    }
}

#[cfg(feature = "serde")]
impl<T> Serialize for Slot<T>
where
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        SafeSlot::from(self).serialize(serializer)
    }
}

#[cfg(feature = "serde")]
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

        Ok(Slot::from(safe_slot))
    }
}
