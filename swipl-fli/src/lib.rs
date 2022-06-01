//! Generated low-level bindings to the SWI-Prolog fli.
#![doc(html_root_url = "https://terminusdb-labs.github.io/swipl-rs/swipl_fli/")]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
// TODO any function that uses u128 should be excluded
#![allow(improper_ctypes)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

// we define some extra constants which inexplicably didn't make it into the header
pub const SH_ERRORS: i32 = 0x01;
pub const SH_ALIAS: i32 = 0x02;
pub const SH_UNLOCKED: i32 = 0x04;
pub const SH_OUTPUT: i32 = 0x08;
pub const SH_INPUT: i32 = 0x10;
pub const SH_NOPAIR: i32 = 0x20;
