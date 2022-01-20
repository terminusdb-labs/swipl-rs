//! A helper crate to retrieve information about the installed swipl environment.
#![doc(html_root_url = "https://terminusdb-labs.github.io/swipl-rs/swipl_info/")]

use regex::*;
use std::env;
use std::process::Command;

/// Struct containing information about a SWI-Prolog installation
#[derive(Debug)]
pub struct SwiplInfo {
    /// The SWI-Prolog version as an integer
    pub version: u32,
    /// The main directory where SWI-Prolog is located
    pub swi_home: String,
    /// The directory subpath where dynamic libraries live
    pub pack_so_dir: String,
    /// The cflags that swipl advises should be used in module compiles
    pub cflags: String,
    /// The ldflags that swipl advises should be used in module compiles
    pub ldflags: String,
    /// The current architecture
    pub arch: String,
    /// The swipl lib name on this platform
    pub lib_name: String,
    /// The directory with the dynamic libraries
    pub lib_dir: String,
    /// The directory with the header files
    pub header_dir: String,
}

/// Retrieve information about the installed swipl environment.
///
/// This will check the SWIPL environment variable for a path to the
/// swipl binary. If this environment variable is not set, it'll
/// attempt to find swipl by assuming it is on the PATH. When found,
/// some prolog is run to extract this information using the
/// `prolog_pack` library, and returned as a `SwiplInfo`.
///
/// If swipl is not found, this function panics.
pub fn get_swipl_info() -> SwiplInfo {
    // by retrieving SWIPL from env, this should work within swipl
    // build environments, as these set this environment variable
    // appropriately.
    let swipl_path = env::var("SWIPL").unwrap_or_else(|_| "swipl".to_string());

    // let's first retrieve a version number
    let output = Command::new(&swipl_path)
        .arg("-g")
        .arg("current_prolog_flag(version, Version), writeq(Version)")
        .arg("-g")
        .arg("halt")
        .output()
        .unwrap();

    if !output.status.success() {
        panic!("Error retrieving version number using swipl: {:?}", output);
    }

    let version: u32 = String::from_utf8_lossy(&output.stdout).parse().unwrap();

    let build_env_command: &str;
    if version >= 80504 {
        // build_environment predicate moved and is now called somewhat differently
        build_env_command = "use_module(library(build/tools)), build_tools:build_environment(Env, []), memberchk('SWIHOME'=Swihome, Env), memberchk('PACKSODIR'=Packsodir, Env), memberchk('CFLAGS'=Cflags, Env), memberchk('LDSOFLAGS'=Ldflags, Env), format('~s~n~s~n~s~n~s~n', [Swihome, Packsodir, Cflags, Ldflags])";
    } else {
        build_env_command = "use_module(library(prolog_pack)), prolog_pack:build_environment(Env), memberchk('SWIHOME'=Swihome, Env), memberchk('PACKSODIR'=Packsodir, Env), memberchk('CFLAGS'=Cflags, Env), memberchk('LDSOFLAGS'=Ldflags, Env), format('~s~n~s~n~s~n~s~n', [Swihome, Packsodir, Cflags, Ldflags])";
    }

    let output = Command::new(&swipl_path)
        .arg("-g")
        .arg(build_env_command)
        .arg("-g")
        .arg("halt")
        .output()
        .unwrap();

    if !output.status.success() {
        panic!(
            "Error retrieving build environment using swipl: {:?}",
            output
        );
    }

    let runtime_output = Command::new(&swipl_path)
        .arg("--dump-runtime-variables")
        .output()
        .unwrap();

    let runtime_output = String::from_utf8_lossy(&runtime_output.stdout);

    let plarch_regex = Regex::new(r#"PLARCH="([^"]*)""#).unwrap();
    let pllibdir_regex = Regex::new(r#"PLLIBDIR="([^"]*)""#).unwrap();

    let arch = plarch_regex.captures(&runtime_output).unwrap()[1].to_string();
    let lib_dir = pllibdir_regex.captures(&runtime_output).unwrap()[1].to_string();

    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut lines = stdout.lines();
    let swi_home = lines.next().unwrap().to_owned();
    let pack_so_dir = lines.next().unwrap().to_owned();
    let cflags = lines.next().unwrap().to_owned();
    let ldflags = lines.next().unwrap().to_owned();

    let lib_name;
    if cfg!(target_os = "windows") {
        lib_name = "libswipl".to_string();
    } else {
        lib_name = "swipl".to_string();
    }

    let header_dir = format!("{}/include", swi_home);

    SwiplInfo {
        version,
        swi_home,
        pack_so_dir,
        cflags,
        ldflags,
        arch,
        lib_name,
        lib_dir,
        header_dir,
    }
}
