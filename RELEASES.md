Version 0.4.3
=============

 - Made Key trait unsafe, as it was erroneously safe to implement.


Version 0.4.2
=============

 - Backport of fix made in 1.0.5.


Version 0.4.1
=============

 - Backport of fix made in 1.0.4.


Version 0.4.0
=============

 - Codebase moved to 2018 Edition.

 - Reintroduce `DenseSlotMap` - an overzealous removal in 0.3.0.
 
 - Added support for `try_reserve`.

 - Added support for custom hashers in `SparseSecondaryMap`.

 - `SparseSecondaryMap` and `SecondaryMap` can now be cloned.

 - Keys have a more terse debug output.

 - Fixed a bug that caused an overflowing left shift on 32-bit targets.


Version 0.3.0
=============

 - Massive rework, with a focus on secondary maps and custom keys to prevent
   cross-slotmap key usage.

 - Removed `DenseSlotMap` in favour of `HopSlotMap` as the latter performs
   better when secondary maps are in use.
   
 - Unfortunately due to the redesign the first slot in a slot map must now
   always be empty. This means some deserializations of slot maps serialized
   with a version before 0.3.0 can fail.

 - Added `SecondaryMap` and `SparseSecondaryMap`, which allows you to associate
   extra data with keys given by a slot map. 

 - Added `DefaultKey`, custom key types, and support for them on all slot maps
   and secondary maps. You must now always specify the key type you're using
   with a slot map, so `SlotMap<i32>` would be `SlotMap<DefaultKey, i32>`. It is
   recommended to make a custom key type with `new_key_type!` for any slot map
   you create, as this entirely prevents using the wrong key on the wrong slot
   map.

 - `KeyData` now has `as_ffi` and `from_ffi` functions that convert the data
   that makes up a key to/from an `u64`. This allows you to use slot map keys
   as opaque handles in FFI code.


Version 0.2.1
=============

 - Fixed a potential uninitialized memory vulnerability. No uninitialized memory
   was read or used directly, but Rust's assumptions could lead to it. Yanked
   all previous versions as they were all vulnerable.

 - Made a `Key` member non-zero so that `Option<Key>` is optimized.


Version 0.2.0
=============
Start of version history.
