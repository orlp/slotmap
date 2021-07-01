#![no_main]
use libfuzzer_sys::arbitrary::{self, Arbitrary};
use libfuzzer_sys::fuzz_target;

use slotmap::HopSlotMap;

#[derive(Arbitrary, Debug)]
struct Target {
    ctor: Constructor,
    ops: Vec<Op>,
}

#[derive(Arbitrary, Debug)]
enum Constructor {
    New,
    WithCapacity(u8),
}

#[derive(Arbitrary, Debug)]
enum Op {
    Reserve(u8),
    Insert,
    InsertWithKey,
    Remove(usize),
    Retain(Vec<bool>),
    Clear,
    Drain,
}

fuzz_target!(|data: Target| {
    let mut map = match data.ctor {
        Constructor::New => HopSlotMap::new(),
        Constructor::WithCapacity(n) => HopSlotMap::with_capacity(n as usize),
    };

    let mut keys = Vec::new();

    for op in data.ops {
        match op {
            Op::Reserve(n) => map.reserve(n as usize),
            Op::Insert => keys.push(map.insert(())),
            Op::InsertWithKey => keys.push(map.insert_with_key(|_| ())),
            Op::Remove(k) => {
                if let Some(k) = keys.get(k) {
                    map.remove(*k);
                } else {
                    return;
                }
            }
            Op::Retain(s) => {
                let mut i = s.into_iter();
                map.retain(|_k, _v| i.next().unwrap_or(false));
            }
            Op::Clear => map.clear(),
            Op::Drain => {
                map.drain();
            }
        }
    }
});