use core::fmt::Debug;

/// Internal stable replacement for !.
#[derive(Debug)]
pub enum Never {}

/// Returns if a is an older version than b, taking into account wrapping of
/// versions.
pub fn is_older_version(a: u32, b: u32) -> bool {
    let diff = a.wrapping_sub(b);
    diff >= (1 << 31)
}

pub struct PanicOnDrop(pub &'static str);
impl Drop for PanicOnDrop {
    fn drop(&mut self) {
        panic!("{}", self.0);
    }
}
