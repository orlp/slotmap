#![deny(warnings, missing_docs, missing_debug_implementations)]
#![doc(html_root_url = "https://docs.rs/slotmap/0.1.0")]
#![crate_name = "slotmap"]

//! # slotmap
//!
//! This library provides two containers with persistent unique keys to access
//! stored values, [`SlotMap`] and [`DenseSlotMap`]. Upon insertion a key
//! is returned that can be used to later access or remove the values.
//! Insertion, deletion and access all take O(1) time with low overhead. Great
//! for storing collections of objects that need stable, safe references but
//! have no clear ownership otherwise, such as game entities or graph nodes.
//!
//! The difference between a [`BTreeMap`] or [`HashMap`] and a slot map is
//! that the slot map generates and returns the key when inserting a value. A
//! key is always unique and will only refer to the value that was inserted.
//! A slot map's main purpose is to simply own things in a safe and efficient
//! manner.
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
//! let reused = sm.insert("reuse");  // Space from bar reused.
//! assert_eq!(sm.contains_key(bar), false);  // After deletion a key stays invalid.
//! ```
//!
//! # Serialization through [`serde`]
//!
//! Both [`Key`] and the slot maps have full (de)seralization support through
//! the [`serde`] library. A key remains valid for a slot map even after one or
//! both have been serialized and deserialized! This makes storing or
//! transferring complicated referential structures and graphs a breeze. Care has
//! been taken such that deserializing keys and slot maps from untrusted sources
//! is safe.
//!
//! # Why not [`slab`]?
//!
//! Unlike [`slab`], the keys returned by the slots maps are versioned. This
//! means that once a key is removed, it stays removed, even if the physical
//! storage inside the slotmap is re-used for new elements. A [`DenseSlotMap`]
//! also provides faster iteration than [`slab`] does. Additionally, at the time
//! of writing [`slab`] does not support serialization.
//!
//! # Choosing `SlotMap` or `DenseSlotMap`
//!
//! The overhead on access with a [`Key`] in a [`SlotMap`] compared to
//! storing your elements in a [`Vec`] is a mere equality check.  However, as
//! there can be 'holes' in the underlying representation of a [`SlotMap`]
//! iteration can be inefficient when many slots are unoccupied (a slot gets
//! unoccupied when an element is removed, and gets filled back up on
//! insertion). If you often require fast iteration over all values, we also
//! provide a [`DenseSlotMap`]. It trades random access performance for fast
//! iteration over values by storing the actual values contiguously and using an
//! extra array access to translate a key into a value index.
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
//! elements. After 2<sup>31</sup> deletions and insertions to the same
//! underlying slot the version wraps around and such a spurious reference
//! could potentially occur. It is incredibly unlikely however, and in all
//! circumstances is the behavior safe. A slot map can hold up to 2<sup>32</sup>
//! elements at a time.
//!
//! A slot map never shrinks - it couldn't even if it wanted to. It needs to
//! remember for each slot what the latest version is as to not generate
//! duplicate keys. The overhead for each element in [`SlotMap`] is 8 bytes. In
//! [`DenseSlotMap`] it is 12 bytes.
//!
//! [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
//! [`BTreeMap`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
//! [`HashMap`]: https://doc.rust-lang.org/std/collections/struct.HashMap.html
//! [`Key`]: struct.Key.html
//! [`SlotMap`]: struct.SlotMap.html
//! [`DenseSlotMap`]: dense/struct.DenseSlotMap.html
//! [`serde`]: https://github.com/serde-rs/serde
//! [`slab`]: https://github.com/carllerche/slab

#[cfg(feature = "serde")]
#[macro_use]
extern crate serde;

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

#[cfg(test)]
extern crate serde_json;

#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer};

pub(crate) mod normal;
pub use normal::*;

// pub mod dense;
// pub use dense::DenseSlotMap;

/// Key used to access stored values in a slot map.
///
/// Do not use a key from one slot map in another. The behavior is safe but
/// non-sensical (and might panic in case of out-of-bounds). Keys implement
/// `Ord` so they can be used in e.g.
/// [`BTreeMap`](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html)
/// but their order is arbitrary.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Key {
    idx: u32,

    #[cfg_attr(feature = "serde", serde(deserialize_with = "deserialize_key_version"))]
    version: u32,
}


#[cfg(feature = "serde")]
fn deserialize_key_version<'de, D>(deserializer: D) -> Result<u32, D::Error>
where
    D: Deserializer<'de>,
{
    let version: u32 = Deserialize::deserialize(deserializer)?;
    Ok(version | 1) // Ensure version is odd.
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "serde")]
    use super::*;

    #[cfg(feature = "serde")]
    #[test]
    fn key_serde() {
        // Check round-trip through serde.
        let mut sm = SlotMap::new();
        let k = sm.insert(42);
        let ser = serde_json::to_string(&k).unwrap();
        let de: Key = serde_json::from_str(&ser).unwrap();
        assert_eq!(k, de);

        // Even if a malicious entity sends up even (unoccupied) versions in the
        // key, we make the version point to the occupied version.
        let malicious = serde_json::from_str::<Key>(&r#"{"idx":0,"version":4}"#).unwrap();
        assert_eq!(u32::from(malicious.version), 5);
    }
}
