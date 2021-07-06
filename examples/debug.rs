use slotmap::SlotMap;

slotmap::new_key_type! { struct CustomKey; }

fn main() {
    let mut x: SlotMap<CustomKey, &'_ str> = SlotMap::with_key();
    let k0 = x.insert("a");
    x.insert("b");
    x.insert("c");
    dbg!(&x);

    x.remove(k0);

    x.insert("later");

    dbg!(x);
}
