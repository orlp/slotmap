fn main() {
    if !version_check::is_min_version("1.49.0").unwrap_or(true) {
        println!("cargo:warning=slotmap requires rustc => 1.49.0");
    }

    if version_check::is_feature_flaggable() == Some(true) {
        println!("cargo:rustc-cfg=nightly");
    }
}
