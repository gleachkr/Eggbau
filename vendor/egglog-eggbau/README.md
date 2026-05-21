# egglog wrapper for eggbau

This is a local Cargo wrapper around the `vendor/egglog` submodule. It keeps
Eggbau from depending directly on the submodule package, so the wrapper build
script can apply the proof API edits before Rust compiles the egglog sources.
Keep those edits in sync with `../egglog-eggbau-proof-api.patch`.

The wrapper should go away once upstream egglog exposes the proof API that
Eggbau needs.
