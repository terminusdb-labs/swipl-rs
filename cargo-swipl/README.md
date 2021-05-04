# cargo-swipl - a helper tool for working with swipl-rs
cargo-swipl is a tool to make working with crates that depend on swipl-rs easier.

swipl-rs dependent crates will be linked against the SWI-Prolog system specified in the `SWIPL` variable, or if that's not specified, the version of SWI-Prolog that is found on the path. However, at run time, if SWI-Prolog's shared library is not discoverable, the resulting binary will fail to start. 

cargo-swipl provides a wrapper around `cargo run` and `cargo test`, namely `cargo swipl run` and `cargo swipl test`, which sets up your environment so that the required dependencies will be discovered. They take all the arguments that their respective cargo commands would take, and will return with the same status code.

## Examples
Run the main binary:
```bash
cargo swipl run
```

Run the tests:
```bash
cargo swipl test
```

Explicitely specify the SWI-Prolog version to run with:
```bash
SWIPL=~/.swivm/versions/v8.2.4/bin/swipl cargo swipl run
```
