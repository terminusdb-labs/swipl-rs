use std::env;
use std::path::PathBuf;

use swipl_info::*;

fn main() {
    let info = get_swipl_info();
    if cfg!(target_os = "windows") {
        if cfg!(feature = "static") {
            println!("cargo:rustc-link-lib=static=libswipl_static");
        } else {
            println!("cargo:rustc-link-lib=dylib=libswipl");
        }
        println!("cargo:rustc-link-search={}/bin", info.swi_home);
    } else {
        if cfg!(feature = "static") {
            println!("cargo:rustc-link-search=/usr/lib/x86_64-linux-gnu/");
            println!("cargo:rustc-link-lib=static=gmp");
            println!("cargo:rustc-link-lib=static=curses");
            println!("cargo:rustc-link-lib=static=tinfo");
            println!("cargo:rustc-link-lib=static=z");
            println!("cargo:rustc-link-lib=static=swipl_static");
        } else {
            println!("cargo:rustc-link-lib=dylib=swipl");
        }
        println!(
            "cargo:rustc-link-search={}/{}",
            info.swi_home, info.pack_so_dir
        );
    }

    println!("cargo:rerun-if-changed=c/wrapper.h");
    println!("cargo:rerun-if-env-changed=SWIPL");
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
