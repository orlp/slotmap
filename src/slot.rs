use std;
use std::fmt;
use std::mem::ManuallyDrop;

#[cfg(feature = "serde")]
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

// Little helper function to turn (bool, T) into Option<T>.
fn to_option<T>(b: bool, some: T) -> Option<T> {
    match b {
        true => Some(some),
        false => None,
    }
}


// Ensures that version is always odd, so it always refers to an occupied slot
// if it exists, and never to an unoccupied slot.
#[cfg_attr(feature = "serde", derive(Serialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OccupiedVersion(u32);

impl From<u32> for OccupiedVersion {
    fn from(version: u32) -> Self {
        OccupiedVersion(version | 1)
    }
}

impl From<OccupiedVersion> for u32 {
    fn from(version: OccupiedVersion) -> u32 {
        version.0
    }
}


// A slot, which represents storage for a value and a current version.
// Can be occupied or vacant
pub struct Slot<T> {
    // A value when occupied, uninitialized memory otherwise.
    value: ManuallyDrop<T>,

    // Even = vacant, odd = occupied.
    version: u32,

    // This could be in an union with value, but that requires unions for types
    // without copy. This isn't available in stable Rust yet.
    pub next_free: u32,
}

impl<T> Slot<T> {
    pub fn new() -> Self {
        Self {
            value: unsafe { std::mem::uninitialized() },
            version: 0,
            next_free: 0,
        }
    }

    pub fn occupied(&self) -> bool {
        self.version % 2 > 0
    }

    pub fn occupied_version(&self) -> OccupiedVersion {
        self.version.into()
    }

    pub fn has_version(&self, version: OccupiedVersion) -> bool {
        self.version == u32::from(version)
    }

    pub fn value(&self) -> Option<&T> {
        to_option(self.occupied(), &self.value)
    }

    pub fn value_mut(&mut self) -> Option<&mut T> {
        let occupied = self.occupied();
        to_option(occupied, &mut self.value)
    }

    pub fn get_versioned(&self, version: OccupiedVersion) -> Option<&T> {
        let correct_version = self.has_version(version);
        to_option(correct_version, &self.value)
    }

    pub fn get_versioned_mut(&mut self, version: OccupiedVersion) -> Option<&mut T> {
        let correct_version = self.has_version(version);
        to_option(correct_version, &mut self.value)
    }

    pub unsafe fn get_unchecked(&self) -> &T {
        &self.value
    }
    pub unsafe fn get_unchecked_mut(&mut self) -> &mut T {
        &mut self.value
    }

    pub unsafe fn store_value(&mut self, value: T) {
        self.version |= 1;
        self.value = ManuallyDrop::new(value);
    }

    pub unsafe fn remove_value(&mut self) -> T {
        self.version = self.version.wrapping_add(1);
        std::mem::replace(&mut *self.value, std::mem::uninitialized())
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
    fn clone(&self) -> Self {
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
        let mut builder = fmt.debug_struct("Slot");
        builder.field("version", &self.version);
        if self.occupied() {
            builder.field("value", &self.value).finish()
        } else {
            builder.field("next_free", &self.next_free).finish()
        }
    }
}

// Serialization.
#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for OccupiedVersion {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let version: u32 = Deserialize::deserialize(deserializer)?;
        Ok(version.into())
    }
}

#[cfg(feature = "serde")]
#[derive(Serialize, Deserialize)]
struct SafeSlot<T> {
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
            value: slot.value(),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "serde")]
    use serde_json;

    #[test]
    fn occupied_version() {
        let ov: OccupiedVersion = 2.into();
        let v: u32 = ov.into();

        assert_eq!(v, 3);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn slot_serde() {
        let slot = Slot {
            value: ManuallyDrop::new("test"),
            version: 1,
            next_free: 42,
        };

        let ser = serde_json::to_string(&slot).unwrap();
        let de: Slot<&str> = serde_json::from_str(&ser).unwrap();
        assert_eq!(de.value, slot.value);
        assert_eq!(de.version, slot.version);
        assert_eq!(de.next_free, 0); // next_free should not survive serialization.

        // let invalid = serde_json::from_str::<Key>(&r#"{"idx":0,"version":0}"#);
        // assert!(invalid.is_err(), "decoded key with even version");
    }
}
