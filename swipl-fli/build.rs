use std::env;
use std::path::PathBuf;

use swipl_info::*;

fn main() {
    let info = get_swipl_info();
    println!("cargo:rustc-link-lib={}", info.lib_name);
    println!("cargo:rustc-link-search={}", info.lib_dir);
    println!("cargo:rerun-if-changed=c/wrapper.h");
    println!("cargo:rerun-if-env-changed=SWIPL");

    let mut bindings = bindgen::Builder::default();
    if cfg!(feature = "gmp") {
        bindings = bindings.header_contents("include_gmp", "#include <gmp.h>\n");
    }

    let bindings = bindings
        .header("c/wrapper.h")
        .clang_arg(format!("-I{}", info.header_dir))
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        .generate()
        .unwrap();

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .unwrap();
}
