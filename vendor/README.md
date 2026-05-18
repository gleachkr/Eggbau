# Vendored dependencies

`vendor/egglog` is a git submodule for eggbau's patched egglog pin.

Until the egglog patch is pushed to a public fork and the submodule pointer is
updated to that commit, apply the local proof API patch after initializing the
submodule:

```sh
git submodule update --init --recursive
git -C vendor/egglog apply ../egglog-eggbau-proof-api.patch
```

The patch exposes a narrow read-only proof reconstruction API used by eggbau's
stage-0 proof API spike.
