#![no_main]
use libfuzzer_sys::fuzz_target;

mod target;

fuzz_target!(|data: target::Target| {
    fuzz_slotmap!(data, slotmap::SlotMap::<slotmap::DefaultKey, u32>);
});
