#![no_main]
use libfuzzer_sys::fuzz_target;

use slotmap::DenseSlotMap;

mod target;
use target::{Constructor, Op, Target};

fuzz_target!(|data: Target| {
    let mut map = match data.ctor {
        Constructor::New => DenseSlotMap::new(),
        Constructor::WithCapacity(n) => DenseSlotMap::with_capacity(n as usize),
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
