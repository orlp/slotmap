#![deny(warnings, missing_docs, missing_debug_implementations)]
#![crate_name = "slotmap"]

//! # slotmap
//!
//! This library provides two containers with persistent unique keys to access
//! stored values, [`SparseSlotMap`] and [`DenseSlotMap`]. Upon insertion a key
//! is returned that can be used to later access or remove the values. Great for
//! storing collections of objects that need stable, safe references but have no
//! clear ownership otherwise, such as game entities or graph nodes.
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
//! let mut sm = SparseSlotMap::new();
//! let foo = sm.insert("foo");
//! let bar = sm.insert("bar");
//! assert_eq!(sm[foo], "foo");
//! assert_eq!(sm[bar], "bar");
//!
//! sm.remove(bar);
//! let reused = sm.insert("reuse");  // Space from bar reused.
//! assert_eq!(sm.contains(bar), false);  // After deletion a key stays invalid.
//! ```
//! 
//! # Choosing sparse or dense
//!
//! The overhead on access with a [`sparse::Key`] in a [`SparseSlotMap`]
//! compared to storing your elements in a [`Vec`] is a mere equality check.
//! However, as there can be 'holes' in the underlying representation of a
//! [`SparseSlotMap`] iteration can be inefficient when many slots are
//! unoccupied. If you often require fast iteration over all values, we also
//! provide a [`DenseSlotMap`]. It trades access performance for fast iteration
//! over values by storing the actual values contiguously and using an extra
//! array access to translate a key into a value index. Iteration over keys or
//! key-value pairs is the same speed for both containers. If you must have fast
//! key or key-value iteration store the [`dense::Key`] of itself inside your
//! value and use the fast value iteration of [`DenseSlotMap`].
//!
//! # Implementation
//!
//! Insertion, access and deletion is all O(1) with low overhead by storing the
//! elements inside a [`Vec`]. Unlike references or indices into a vector,
//! unless you remove a key it is never invalidated. Behind the scenes each
//! slot in the vector is a `(value, version)` tuple. After insertion the
//! returned key also contains a version. Only when the stored version and
//! version in a key match is a key valid. This allows us to reuse space in the
//! vector after deletion without letting deleted keys point to spurious new
//! elements. After 2<sup>31</sup> deletions and insertions to the same
//! underlying slot the version wraps around and such a spurious reference
//! could potentially occur. It is incredibly unlikely however, and in all
//! circumstances is the behavior safe. A slot map can hold up to 2<sup>32</sup>
//! elements at a time.
//!
//! [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
//! [`BTreeMap`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
//! [`HashMap`]: https://doc.rust-lang.org/std/collections/struct.HashMap.html
//! [`sparse::Key`]: sparse/struct.Key.html
//! [`dense::Key`]: dense/struct.Key.html
//! [`SparseSlotMap`]: sparse/struct.SparseSlotMap.html
//! [`DenseSlotMap`]: dense/struct.DenseSlotMap.html

pub mod sparse;
pub use sparse::SparseSlotMap;

///// A dense slotmap, for faster iteration but slower individual access compared
///// to [SparseSlotMap](struct.SparseSlotMap.html).
/////
///// Not implemented yet.
//#[derive(Debug)]
//pub struct DenseSlotMap;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
