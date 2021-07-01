use libfuzzer_sys::arbitrary::{self, Arbitrary};

#[derive(Arbitrary, Debug)]
pub struct Target {
    pub ctor: Constructor,
    pub ops: Vec<Op>,
}

#[derive(Arbitrary, Debug)]
pub enum Constructor {
    New,
    WithCapacity(u8),
}

#[derive(Arbitrary, Debug)]
pub enum Op {
    Reserve(u8),
    Insert,
    InsertWithKey,
    Remove(usize),
    Retain(Vec<bool>),
    Clear,
    Drain,
}
