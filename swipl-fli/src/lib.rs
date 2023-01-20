//! Generated low-level bindings to the SWI-Prolog fli.
#![doc(html_root_url = "https://terminusdb-labs.github.io/swipl-rs/swipl_fli/")]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
// TODO any function that uses u128 should be excluded
#![allow(improper_ctypes)]
#![allow(clippy::useless_transmute)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

// we define some extra constants which inexplicably didn't make it into the header
pub const SH_ERRORS: i32 = 0x01;
pub const SH_ALIAS: i32 = 0x02;
pub const SH_UNLOCKED: i32 = 0x04;
pub const SH_OUTPUT: i32 = 0x08;
pub const SH_INPUT: i32 = 0x10;
pub const SH_NOPAIR: i32 = 0x20;

pub const SIO_FBUF: u32 = 1 << 0; /* full buffering */
pub const SIO_LBUF: u32 = 1 << 1; /* line buffering */
pub const SIO_NBUF: u32 = 1 << 2; /* no buffering */
pub const SIO_FEOF: u32 = 1 << 3; /* end-of-file */
pub const SIO_FERR: u32 = 1 << 4; /* error ocurred */
pub const SIO_USERBUF: u32 = 1 << 5; /* buffer is from user */
pub const SIO_INPUT: u32 = 1 << 6; /* input stream */
pub const SIO_OUTPUT: u32 = 1 << 7; /* output stream */
pub const SIO_NOLINENO: u32 = 1 << 8; /* line no. info is void */
pub const SIO_NOLINEPOS: u32 = 1 << 9; /* line pos is void */
pub const SIO_STATIC: u32 = 1 << 10; /* Stream in static memory */
pub const SIO_RECORDPOS: u32 = 1 << 11; /* Maintain position */
pub const SIO_FILE: u32 = 1 << 12; /* Stream refers to an OS file */
pub const SIO_NOERROR: u32 = 1 << 13; /* Ignore write errors */
pub const SIO_NOFEOF: u32 = 1 << 14; /* don't set SIO_FEOF flag */
pub const SIO_TEXT: u32 = 1 << 15; /* text-mode operation */
pub const SIO_FEOF2: u32 = 1 << 16; /* attempt to read past eof */
pub const SIO_FEOF2ERR: u32 = 1 << 17; /* Sfpasteof() */
pub const SIO_NOCLOSE: u32 = 1 << 18; /* Do not close on abort */
pub const SIO_APPEND: u32 = 1 << 19; /* opened in append-mode */
pub const SIO_UPDATE: u32 = 1 << 20; /* opened in update-mode */
pub const SIO_ISATTY: u32 = 1 << 21; /* Stream is a tty */
pub const SIO_CLOSING: u32 = 1 << 22; /* We are closing the stream */
pub const SIO_TIMEOUT: u32 = 1 << 23; /* We had a timeout */
pub const SIO_NOMUTEX: u32 = 1 << 24; /* Do not allow multi-thread access */
pub const SIO_ADVLOCK: u32 = 1 << 25; /* File locked with advisory lock */
pub const SIO_WARN: u32 = 1 << 26; /* Pending warning */
pub const SIO_RAW: u32 = 1 << 27; /* TTY Stream is in raw mode */
pub const SIO_REPXML: u32 = 1 << 28; /* Bad char --> XML entity */
pub const SIO_REPPL: u32 = 1 << 29; /* Bad char --> Prolog \hex\ */
pub const SIO_BOM: u32 = 1 << 30; /* BOM was detected/written */
pub const SIO_REPPLU: u32 = 1 << 31; /* Bad char --> Prolog \uXXXX */
