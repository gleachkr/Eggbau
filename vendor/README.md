# Vendored dependencies

`vendor/egglog` is a git submodule for eggbau's patched egglog pin.

Until the proof API lands upstream, eggbau keeps a tiny local patch in
`vendor/egglog-eggbau-proof-api.patch`. The `vendor/egglog-eggbau` wrapper
crate applies the same patch after the submodule has been initialized:

```sh
git submodule update --init --recursive
CARGO_HOME="$PWD/.cargo_home" cargo build --all-targets --all-features
```

If `vendor/egglog` is still an empty gitlink checkout, Cargo can fail while
resolving path dependencies before the wrapper build script runs. Initialize
the submodule first in that case.

The patch exposes a narrow read-only proof reconstruction API used by eggbau's
proof extraction code.
