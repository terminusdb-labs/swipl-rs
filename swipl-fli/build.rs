use std::env;
use std::path::PathBuf;

use swipl_info::*;

fn main() {
    let info = get_swipl_info();
    if cfg!(target_os = "windows") {
        println!("cargo:rustc-link-lib=libswipl");
        println!("cargo:rustc-link-search={}/bin", info.swi_home);
    } else {
        println!("cargo:rustc-link-lib=swipl");
        println!(
            "cargo:rustc-link-search={}/{}",
            info.swi_home, info.pack_so_dir
        );
    }

    println!("cargo:rerun-if-changed=c/wrapper.h");
    let bindings = bindgen::Builder::default()
        .header("c/wrapper.h")
        .clang_arg(format!("-I{}/include", info.swi_home))
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        .generate()
        .unwrap();

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .unwrap();
}
