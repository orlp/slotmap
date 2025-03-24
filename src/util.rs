use crate::Key;
use core::fmt;
use core::hint::unreachable_unchecked;

/// Internal stable replacement for !.
#[derive(Debug)]
pub enum Never {}

/// Returns if a is an older version than b, taking into account wrapping of
/// versions.
pub fn is_older_version(a: u32, b: u32) -> bool {
    let diff = a.wrapping_sub(b);
    diff >= (1 << 31)
}

/// An unwrapper that checks on debug, doesn't check on release.
/// UB if unwrapped on release mode when unwrap would panic.
pub trait UnwrapUnchecked<T> {
    // Extra underscore because unwrap_unchecked is planned to be added to the stdlib.
    unsafe fn unwrap_unchecked_(self) -> T;
}

impl<T> UnwrapUnchecked<T> for Option<T> {
    unsafe fn unwrap_unchecked_(self) -> T {
        if cfg!(debug_assertions) {
            self.unwrap()
        } else {
            match self {
                Some(x) => x,
                None => unreachable_unchecked(),
            }
        }
    }
}

impl<T, E: fmt::Debug> UnwrapUnchecked<T> for Result<T, E> {
    unsafe fn unwrap_unchecked_(self) -> T {
        if cfg!(debug_assertions) {
            self.unwrap()
        } else {
            match self {
                Ok(x) => x,
                Err(_) => unreachable_unchecked(),
            }
        }
    }
}

/// Debug format a slot map.
/// Keys are formatted without the name of the wrapper struct
/// (`1v2` instead of `MyKey(1v2)`).
pub fn debug_fmt_entries<I, K, V>(entries: I, f: &mut fmt::Formatter) -> fmt::Result
where
    I: IntoIterator<Item = (K, V)>,
    K: Key,
    V: fmt::Debug
{
    let entries = entries.into_iter().map(|(k, v)| (k.data(), v));
    f.debug_map().entries(entries).finish()
}
