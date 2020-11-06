#[rustversion::not(nightly)]
fn main() {}

#[rustversion::nightly]
fn main() {
    println!("cargo:rustc-cfg=nightly");
}
