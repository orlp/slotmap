#![deny(warnings, missing_docs, missing_debug_implementations)]
#![doc(html_root_url = "https://docs.rs/slotmap/0.4.0")]
#![crate_name = "slotmap"]
#![cfg_attr(feature = "unstable", feature(untagged_unions, try_reserve))]

//! # slotmap
//!
//! This library provides a container with persistent unique keys to access
//! stored values, [`SlotMap`]. Upon insertion a key is returned that can be
//! used to later access or remove the values. Insertion, removal and access all
//! take O(1) time with low overhead. Great for storing collections of objects
//! that need stable, safe references but have no clear ownership otherwise,
//! such as game entities or graph nodes.
//!
//! The difference between a [`BTreeMap`] or [`HashMap`] and a slot map is
//! that the slot map generates and returns the key when inserting a value. A
//! key is always unique and will only refer to the value that was inserted.
//! A slot map's main purpose is to simply own things in a safe and efficient
//! manner.
//!
//! You can also create (multiple) secondary maps that can map the keys returned
//! by [`SlotMap`] to other values, to associate arbitrary data with objects
//! stored in slot maps, without hashing required - it's direct indexing under
//! the hood.
//!
//! # Examples
//!
//! ```
//! # use slotmap::*;
//! let mut sm = SlotMap::new();
//! let foo = sm.insert("foo");  // Key generated on insert.
//! let bar = sm.insert("bar");
//! assert_eq!(sm[foo], "foo");
//! assert_eq!(sm[bar], "bar");
//!
//! sm.remove(bar);
//! let reuse = sm.insert("reuse");  // Space from bar reused.
//! assert_eq!(sm.contains_key(bar), false);  // After deletion a key stays invalid.
//!
//! let mut sec = SecondaryMap::new();
//! sec.insert(foo, "noun");  // We provide the key for secondary maps.
//! sec.insert(reuse, "verb");
//!
//! for (key, val) in sm {
//!     println!("{} is a {}", val, sec[key]);
//! }
//! ```
//!
//! # Serialization through [`serde`]
//!
//! Both keys and the slot maps have full (de)seralization support through
//! the [`serde`] library. A key remains valid for a slot map even after one or
//! both have been serialized and deserialized! This makes storing or
//! transferring complicated referential structures and graphs a breeze. Care has
//! been taken such that deserializing keys and slot maps from untrusted sources
//! is safe. If you wish to use these features you must enable the `serde`
//! feature flag for `slotmap` in your `Cargo.toml`.
//!
//! ```text
//! slotmap = { version = "...", features = ["serde"] }
//! ```
//!
//! # Why not [`slab`]?
//!
//! Unlike [`slab`], the keys returned by [`SlotMap`] are versioned. This means
//! that once a key is removed, it stays removed, even if the physical storage
//! inside the slotmap is reused for new elements. The key is a
//! permanently unique<sup>*</sup> reference to the inserted value. Despite
//! supporting versioning, a [`SlotMap`] is not slower than [`slab`], by
//! internally using carefully checked unsafe code. A [`HopSlotMap`]
//! also provides faster iteration than [`slab`] does, and [`DenseSlotMap`] even
//! faster still. Additionally, at the time of writing [`slab`] does not support
//! serialization.
//!
//! # Performance characteristics and implementation details
//!
//! Insertion, access and deletion is all O(1) with low overhead by storing the
//! elements inside a [`Vec`]. Unlike references or indices into a vector,
//! unless you remove a key it is never invalidated. Behind the scenes each
//! slot in the vector is a `(value, version)` tuple. After insertion the
//! returned key also contains a version. Only when the stored version and
//! version in a key match is a key valid. This allows us to reuse space in the
//! vector after deletion without letting removed keys point to spurious new
//! elements. <sup>*</sup>After 2<sup>31</sup> deletions and insertions to the
//! same underlying slot the version wraps around and such a spurious reference
//! could potentially occur. It is incredibly unlikely however, and in all
//! circumstances is the behavior safe. A slot map can hold up to
//! 2<sup>32</sup> - 2 elements at a time.
//!
//! The memory usage for each slot in [`SlotMap`] is `4 + max(sizeof(T), 4)`
//! rounded up to the alignment of `T`. Similarly it is `4 + max(sizeof(T), 12)`
//! for [`HopSlotMap`]. [`DenseSlotMap`] has an overhead of 8 bytes per element
//! and 8 bytes per slot.
//!
//! # Choosing `SlotMap`, `HopSlotMap` or `DenseSlotMap`
//!
//! A [`SlotMap`] can never shrink the size of its underlying storage, because
//! for each storage slot it must remember what the latest stored version was,
//! even if the slot is empty now. This means that iteration can be slow as it
//! must iterate over potentially a lot of empty slots.
//!
//! [`HopSlotMap`] solves this by maintaining more information on
//! insertion/removal, allowing it to iterate only over filled slots by 'hopping
//! over' contiguous blocks of vacant slots. This can give it significantly
//! better iteration speed.  If you expect to iterate over all elements in a
//! [`SlotMap`] a lot, choose [`HopSlotMap`]. The downside is that insertion and
//! removal is roughly twice as slow. Random access is the same speed for both.
//!
//! [`DenseSlotMap`] goes even further and stores all elements on a contiguous
//! block of memory. It uses two indirects per random access; the slots contain
//! indices used to access the contiguous memory. This means random access is
//! slower than both [`SlotMap`] and [`HopSlotMap`], but iteration is
//! significantly faster. Finally, there is no trait requirement on the value
//! type of a [`DenseSlotMap`], see [`Slottable`] for more details.
//!
//! # Choosing `SecondaryMap` or `SparseSecondaryMap`
//!
//! You want to associate extra data with objects stored in a slot map, so you
//! use (multiple) secondary maps to map keys to that data.
//!
//! A [`SecondaryMap`] is simply a [`Vec`] of slots like slot map is, and
//! essentially provides all the same guarantees as [`SlotMap`] does for its
//! operations (with the exception that you provide the keys as produced by the
//! primary slot map). This does mean that even if you associate data to only
//! a single element from the primary slot map, you could need and have to
//! initialize as much memory as the original.
//!
//! A [`SparseSecondaryMap`] is like a [`HashMap`] from keys to objects, however
//! it automatically removes outdated keys for slots that had their space
//! reused. You should use this variant if you expect to store some associated
//! data for only a small portion of the primary slot map.
//!
//! # Custom key types
//!
//! If you have multiple slot maps it's an error to use the key of one slot map
//! on another slot map. The result is safe, but unspecified, and can not be
//! detected at runtime, so it can lead to a hard to find bug.
//!
//! To prevent this, slot maps allow you to specify what the type is of the key
//! they return, as long as that type implements the [`Key`] trait. To aid with
//! this, the [`new_key_type!`] macro is provided that builds such a type for
//! you. The resulting type is exactly like [`DefaultKey`]. So instead of simply
//! using `SlotMap<DefaultKey, Player>` you would use:
//!
//! ```
//! # use slotmap::*;
//! # #[derive(Copy, Clone)]
//! # struct Player;
//! new_key_type! { struct PlayerKey; }
//! let sm: SlotMap<PlayerKey, Player> = SlotMap::with_key();
//! ```
//!
//! [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
//! [`BTreeMap`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
//! [`HashMap`]: https://doc.rust-lang.org/std/collections/struct.HashMap.html
//! [`SlotMap`]: struct.SlotMap.html
//! [`HopSlotMap`]: hop/struct.HopSlotMap.html
//! [`DenseSlotMap`]: dense/struct.DenseSlotMap.html
//! [`SecondaryMap`]: secondary/struct.SecondaryMap.html
//! [`SparseSecondaryMap`]: sparse_secondary/struct.SparseSecondaryMap.html
//! [`Slottable`]: trait.Slottable.html
//! [`Key`]: trait.Key.html
//! [`new_key_type!`]: macro.new_key_type.html
//! [`serde`]: https://github.com/serde-rs/serde
//! [`slab`]: https://github.com/carllerche/slab
//! [`DefaultKey`]: struct.DefaultKey.html

#[cfg(feature = "serde")]
extern crate serde;

// So our macros can refer to these.
#[cfg(feature = "serde")]
#[doc(hidden)]
pub mod __impl {
    pub use serde::{Deserialize, Deserializer, Serialize, Serializer};
}

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

#[cfg(test)]
extern crate serde_json;

pub(crate) mod normal;
pub use crate::normal::*;

pub mod dense;
pub use crate::dense::DenseSlotMap;

pub mod hop;
pub use crate::hop::HopSlotMap;

pub mod secondary;
pub use crate::secondary::SecondaryMap;

pub mod sparse_secondary;
pub use crate::sparse_secondary::SparseSecondaryMap;

use std::fmt::{self, Debug, Formatter};
use std::num::NonZeroU32;

/// A trait for items that can go in a [`SlotMap`] or [`HopSlotMap`]. Due to
/// current stable Rust restrictions a type must be [`Copy`] to be placed in one
/// of those slot maps. This restriction does not apply to [`DenseSlotMap`],
/// [`SecondaryMap`] or [`SparseSecondaryMap`]. It also does not apply if you
/// use nightly Rust and enable the `unstable` feature for `slotmap` by editing
/// your `Cargo.toml`:
///
/// ```text
/// slotmap = { version = "...", features = ["unstable"] }
/// ```
///
/// This trait should already be automatically implemented for any type that is
/// slottable.
///
/// [`Copy`]: https://doc.rust-lang.org/std/marker/trait.Copy.html
/// [`SecondaryMap`]: secondary/struct.SecondaryMap.html
/// [`SparseSecondaryMap`]: sparse_secondary/struct.SparseSecondaryMap.html
/// [`SlotMap`]: struct.SlotMap.html
/// [`HopSlotMap`]: hop/struct.HopSlotMap.html
/// [`DenseSlotMap`]: dense/struct.DenseSlotMap.html
#[cfg(not(feature = "unstable"))]
pub trait Slottable: Copy {}

/// A trait for items that can go in a [`SlotMap`] or [`HopSlotMap`]. Due to
/// current stable Rust restrictions a type must be [`Copy`] to be placed in one
/// of those slot maps. This restriction does not apply to [`DenseSlotMap`],
/// [`SecondaryMap`] or [`SparseSecondaryMap`]. It also does not apply if you
/// use nightly Rust and enable the `unstable` feature for `slotmap` by editing
/// your `Cargo.toml`:
///
/// ```text
/// slotmap = { version = "...", features = ["unstable"] }
/// ```
///
/// This trait should already be automatically implemented for any type that is
/// slottable.
///
/// [`Copy`]: https://doc.rust-lang.org/std/marker/trait.Copy.html
/// [`SecondaryMap`]: secondary/struct.SecondaryMap.html
/// [`SparseSecondaryMap`]: sparse_secondary/struct.SparseSecondaryMap.html
/// [`SlotMap`]: struct.SlotMap.html
/// [`HopSlotMap`]: hop/struct.HopSlotMap.html
/// [`DenseSlotMap`]: dense/struct.DenseSlotMap.html
#[cfg(feature = "unstable")]
pub trait Slottable {}

#[cfg(not(feature = "unstable"))]
impl<T: Copy> Slottable for T {}

#[cfg(feature = "unstable")]
impl<T> Slottable for T {}

/// The actual data stored in a [`Key`].
///
/// This implements `Ord` so keys can be stored in e.g. [`BTreeMap`], but the
/// order of keys is unspecified.
///
/// [`Key`]: trait.Key.html
/// [`BTreeMap`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KeyData {
    idx: u32,
    version: NonZeroU32,
}

impl KeyData {
    fn new(idx: u32, version: u32) -> Self {
        Self {
            idx,
            version: NonZeroU32::new(version).expect("KeyData constructed with zero version"),
        }
    }

    fn null() -> Self {
        Self::new(std::u32::MAX, 1)
    }

    fn is_null(self) -> bool {
        self.idx == std::u32::MAX
    }

    /// Returns the key data as a 64-bit integer. No guarantees about its value
    /// are made other than that passing it to `from_ffi` will return a key
    /// equal to the original.
    ///
    /// With this you can easily pass slot map keys as opaque handles to foreign
    /// code. After you get them back you can confidently use them in your slot
    /// map without worrying about unsafe behavior as you would with passing and
    /// receiving back references or pointers.
    ///
    /// This is not a substitute for proper serialization, use [`serde`] for
    /// that. If you are not doing FFI, you almost surely do not need this
    /// function.
    ///
    /// [`serde`]: index.html#serialization-through-serde
    pub fn as_ffi(self) -> u64 {
        (u64::from(self.version.get()) << 32) | u64::from(self.idx)
    }

    /// Iff `value` is a value received from `k.as_ffi()`, returns a key equal
    /// to `k`. Otherwise the behavior is safe but unspecified.
    pub fn from_ffi(value: u64) -> Self {
        let idx = value & 0xffff_ffff;
        let version = (value >> 32) | 1; // Ensure version is odd.
        Self::new(idx as u32, version as u32)
    }
}

impl Debug for KeyData {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}v{}", self.idx, self.version.get())
    }
}

impl Default for KeyData {
    fn default() -> Self {
        Self::null()
    }
}

/// Key used to access stored values in a slot map.
///
/// Do not use a key from one slot map in another. The behavior is safe but
/// non-sensical (and might panic in case of out-of-bounds).
///
/// To prevent this, it is suggested to have a unique key type for each slot
/// map. The easiest way to do this is through [`new_key_type!`], which
/// makes a new type identical to [`DefaultKey`], just with a different name.
///
/// [`new_key_type!`]: macro.new_key_type.html
/// [`DefaultKey`]: struct.DefaultKey.html
pub trait Key: From<KeyData> + Into<KeyData> + Clone {
    /// Creates a new key that is always invalid and distinct from any non-null
    /// key. A null key can only be created through this method (or default
    /// initialization of keys made with [`new_key_type!`], which calls this
    /// method).
    ///
    /// A null key is always invalid, but an invalid key (that is, a key that
    /// has been removed from the slot map) does not become a null key. A null
    /// is safe to use with any safe method of any slot map instance.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// let mut sm = SlotMap::new();
    /// let k = sm.insert(42);
    /// let nk = DefaultKey::null();
    /// assert!(nk.is_null());
    /// assert!(k != nk);
    /// assert_eq!(sm.get(nk), None);
    /// ```
    ///
    /// [`new_key_type!`]: macro.new_key_type.html
    fn null() -> Self {
        KeyData::null().into()
    }

    /// Checks if a key is null. There is only a single null key, that is
    /// `a.is_null() && b.is_null()` implies `a == b`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slotmap::*;
    /// new_key_type! { struct MyKey; }
    /// let a = MyKey::null();
    /// let b = MyKey::default();
    /// assert_eq!(a, b);
    /// assert!(a.is_null());
    /// ```
    fn is_null(self) -> bool {
        self.into().is_null()
    }
}

/// A helper macro to conveniently create new key types. If you use a new key
/// type for each slot map you create you can entirely prevent using the wrong
/// key on the wrong slot map.
///
/// The type constructed by this macro is identical to [`DefaultKey`], just with
/// a different name.
///
/// [`DefaultKey`]: struct.DefaultKey.html
///
/// # Examples
///
/// ```
/// # extern crate slotmap;
/// # use slotmap::*;
/// new_key_type! {
///     struct EntityKey;
///
///     /// Key for the Player slot map.
///     pub struct PlayerKey;
/// }
///
/// fn main() {
///     let mut players = SlotMap::with_key();
///     let mut entities: SlotMap<EntityKey, (f64, f64)> = SlotMap::with_key();
///     let bob: PlayerKey = players.insert("bobby");
///     // Now this is a type error because entities.get expects an EntityKey:
///     // entities.get(bob);
/// }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! new_key_type {
    ( $(#[$outer:meta])* $vis:vis struct $name:ident; $($rest:tt)* ) => {
        $(#[$outer])*
        #[derive(Copy, Clone, Default,
                 Eq, PartialEq, Ord, PartialOrd,
                 Hash, Debug)]
        #[repr(transparent)]
        $vis struct $name($crate::KeyData);

        impl From<$crate::KeyData> for $name {
            fn from(k: $crate::KeyData) -> Self {
                $name(k)
            }
        }

        impl From<$name> for $crate::KeyData {
            fn from(k: $name) -> Self {
                k.0
            }
        }

        impl $crate::Key for $name { }

        $crate::__serialize_key!($name);

        $crate::new_key_type!($($rest)*);
    };

    () => {}
}

#[cfg(feature = "serde")]
#[doc(hidden)]
#[macro_export]
macro_rules! __serialize_key {
    ( $name:ty ) => {
        impl $crate::__impl::Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: $crate::__impl::Serializer,
            {
                $crate::KeyData::from(*self).serialize(serializer)
            }
        }

        impl<'de> $crate::__impl::Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: $crate::__impl::Deserializer<'de>,
            {
                let key_data: $crate::KeyData =
                    $crate::__impl::Deserialize::deserialize(deserializer)?;
                Ok(key_data.into())
            }
        }
    };
}

#[cfg(not(feature = "serde"))]
#[doc(hidden)]
#[macro_export]
macro_rules! __serialize_key {
    ( $name:ty ) => {};
}

new_key_type! {
    /// The default slot map key type.
    pub struct DefaultKey;
}

// Returns if a is an older version than b, taking into account wrapping of
// versions.
fn is_older_version(a: u32, b: u32) -> bool {
    let diff = a.wrapping_sub(b);
    diff >= (1 << 31)
}

// Serialization with serde.
#[cfg(feature = "serde")]
mod serialize {
    use super::*;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    #[derive(Serialize, Deserialize)]
    pub struct SerKey {
        idx: u32,
        version: u32,
    }

    impl Serialize for KeyData {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let ser_key = SerKey {
                idx: self.idx,
                version: self.version.get(),
            };
            ser_key.serialize(serializer)
        }
    }

    impl<'de> Deserialize<'de> for KeyData {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            let mut ser_key: SerKey = Deserialize::deserialize(deserializer)?;

            // Ensure a.is_null() && b.is_null() implies a == b.
            if ser_key.idx == std::u32::MAX {
                ser_key.version = 1;
            }

            ser_key.version |= 1; // Ensure version is odd.
            Ok(Self::new(ser_key.idx, ser_key.version))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_is_older_version() {
        let is_older = |a, b| is_older_version(a, b);
        assert!(!is_older(42, 42));
        assert!(is_older(0, 1));
        assert!(is_older(0, 1 << 31));
        assert!(!is_older(0, (1 << 31) + 1));
        assert!(is_older((-1i32) as u32, 0));
    }

    #[cfg(feature = "serde")]
    #[test]
    fn key_serde() {
        // Check round-trip through serde.
        let mut sm = SlotMap::new();
        let k = sm.insert(42);
        let ser = serde_json::to_string(&k).unwrap();
        let de: DefaultKey = serde_json::from_str(&ser).unwrap();
        assert_eq!(k, de);

        // Even if a malicious entity sends up even (unoccupied) versions in the
        // key, we make the version point to the occupied version.
        let malicious: KeyData = serde_json::from_str(&r#"{"idx":0,"version":4}"#).unwrap();
        assert_eq!(malicious.version.get(), 5);
    }
}
