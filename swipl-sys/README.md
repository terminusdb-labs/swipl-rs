# swipl-sys - low-level bindings for SWI-Prolog's foreign language interface
This crate provides low-level bindings for SWI-Prolog's foreign language interface. The bindings are generated using [bindgen](https://rust-lang.github.io/rust-bindgen/). SWI-Prolog's header files and shared library are discovered by using the `swipl` binary found either on `PATH` or in the `SWIPL` environment variable.

# Runtime library discovery
Unless SWI-Prolog's dynamic library is automatically discoverable by your operating system, running anything that depends on this crate, including unit tests, will fail with an error saying that the shared library cannot be found. Unfortunately, it does not seem to be possible to embed the library's location at compile time in a portable way.

In order to make things run, you'll have to add the shared library's directory to the library load path. On linux, this can be done by setting the environment `LD_LIBRARY_PATH`. For example,

```
LD_LIBRARY_PATH=/home/matthijs/.swivm/lib/x86_64-linux/ cargo test
```

This is pretty cumbersome. To help out, consider installing [cargo-swipl](https://github.com/matko/swipl-rs/tree/master/cargo-swipl). With cargo-swipl, the above turns into this:

```
cargo swipl test
```

For a more permanent solution, consider using a tool like `chrpath` to embed the library's location in your binary. Alternatively, you can let SWI-Prolog handle the building of standalone binaries, by loading your native library in a swipl process and performing a [`qsave`](https://www.swi-prolog.org/pldoc/doc/_SWI_/library/qsave.pl).
