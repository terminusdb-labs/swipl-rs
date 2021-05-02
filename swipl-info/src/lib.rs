use std::env;
use std::process::Command;

#[derive(Debug)]
pub struct SwiplInfo {
    pub swi_home: String,
    pub pack_so_dir: String,
    pub cflags: String,
    pub ldflags: String,
}

pub fn get_swipl_info() -> SwiplInfo {
    // by retrieving SWIPL from env, this should work within swipl
    // build environments, as these set this environment variable
    // appropriately.
    let swipl_path = env::var("SWIPL").unwrap_or_else(|_| "swipl".to_string());

    let output = Command::new(swipl_path)
        .arg("-g")
        .arg("use_module(library(prolog_pack)), prolog_pack:build_environment(Env), memberchk('SWIHOME'=Swihome, Env), memberchk('PACKSODIR'=Packsodir, Env), memberchk('CFLAGS'=Cflags, Env), memberchk('LDSOFLAGS'=Ldflags, Env), format('~s~n~s~n~s~n~s~n', [Swihome, Packsodir, Cflags, Ldflags])")
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

    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut lines = stdout.lines();
    let swi_home = lines.next().unwrap().to_owned();
    let pack_so_dir = lines.next().unwrap().to_owned();
    let cflags = lines.next().unwrap().to_owned();
    let ldflags = lines.next().unwrap().to_owned();

    SwiplInfo {
        swi_home,
        pack_so_dir,
        cflags,
        ldflags,
    }
}
