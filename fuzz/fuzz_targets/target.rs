use libfuzzer_sys::arbitrary::{self, Arbitrary};

#[derive(Arbitrary, Debug)]
pub struct Target {
    pub ctor: Constructor,
    pub ops: Vec<Op>,
    pub dtor: Destructor,
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
    Drain(usize),
    IterMut(usize),
    GetDisjointMut([usize; 4]),
}

#[derive(Arbitrary, Debug)]
pub enum Destructor {
    LetDrop,
    IntoIter(usize),
}

#[macro_export]
macro_rules! fuzz_slotmap {
    ($target:expr, $map:ty) => {
        use std::convert::TryInto;
        use $crate::target::{Constructor, Destructor, Op};

        let mut map = match $target.ctor {
            Constructor::New => <$map>::new(),
            Constructor::WithCapacity(n) => <$map>::with_capacity(n as usize),
        };

        let mut keys = Vec::new();

        for op in $target.ops {
            match op {
                Op::Reserve(n) => map.reserve(n as usize),
                Op::Insert => keys.push(map.insert(0)),
                Op::InsertWithKey => keys.push(map.insert_with_key(|_| 0)),
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
                Op::Drain(ct) => {
                    let mut i = map.drain();
                    for _ in 0..ct {
                        if i.next().is_none() {
                            break;
                        }
                    }
                }
                Op::IterMut(ct) => {
                    let mut iter = map.iter_mut();
                    for _ in 0..ct {
                        if let Some((_k, v)) = iter.next() {
                            *v += 1;
                        } else {
                            break;
                        }
                    }
                }
                Op::GetDisjointMut(items) => {
                    let mut disjoint_keys = Vec::new();
                    for &item in &items {
                        if let Some(k) = keys.get(item) {
                            disjoint_keys.push(*k);
                        } else {
                            return;
                        }
                    }

                    let result: [slotmap::DefaultKey; 4] = disjoint_keys.try_into().unwrap();

                    if let Some(idxs) = map.get_disjoint_mut(result) {
                        for item in idxs {
                            *item += 1;
                        }
                    }
                }
            }
        }

        match $target.dtor {
            Destructor::LetDrop => {
                drop(map);
            }
            Destructor::IntoIter(ct) => {
                let mut iter = map.into_iter();

                for _ in 0..ct {
                    if iter.next().is_none() {
                        break;
                    }
                }
            }
        }
    };
}
