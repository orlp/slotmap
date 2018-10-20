# slotmap

A Rust library providing two containers with persistent unique keys to access
stored values, `SlotMap` and `HopSlotMap`. Upon insertion a key is returned that
can be used to later access or remove the values. Insertion, deletion and access
all take O(1) time with low overhead. Great for storing collections of objects
that need stable, safe references but have no clear ownership otherwise, such as
game entities or graph nodes. Please refer to the
[**the documentation**](https://docs.rs/slotmap) for more information.

To start using `slotmap` add the following to your `Cargo.toml`:

```toml
[dependencies]
slotmap = "0.2.1"
```

# Example

A short example:

```rust
use slotmap::SlotMap;

let mut sm = SlotMap::new();
let foo = sm.insert("foo");  // Key generated on insert.
let bar = sm.insert("bar");
assert_eq!(sm[foo], "foo");
assert_eq!(sm[bar], "bar");

sm.remove(bar);
let reused = sm.insert("reuse");  // Space from bar reused.
assert_eq!(sm.contains_key(bar), false);  // After deletion a key stays invalid.
```

# License

`slotmap` is released under the Zlib license, a permissive license. It is
OSI and FSF approved and GPL compatible.
