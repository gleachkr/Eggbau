{
  inputs = {
    nixpkgs.url = "nixpkgs";
    utils.url = "github:numtide/flake-utils";
    aufbau.url = "github:gleachkr/Aufbau";
    mm0.url = "github:gleachkr/mm0";
  };

  outputs =
    {
      self,
      nixpkgs,
      aufbau,
      mm0,
      utils,
    }:
    utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        aufbau-tools = aufbau.outputs.packages.${system}.default;
        mm0-c = mm0.packages.${system}.mm0-c;
        mm0-rs = mm0.packages.${system}.mm0-rs;
      in
      {
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            # MM0/Aufbau end-to-end proof pipeline.
            aufbau-tools
            mm0-c
            mm0-rs
            zig
            zls

            # Eggbau is planned as a Rust crate and CLI.
            cargo
            clippy
            rust-analyzer
            rustc
            rustfmt

            # Egglog proof-search target.
            egglog

            # Rust project maintenance and validation.
            cargo-deny
            cargo-insta
            cargo-llvm-cov
            cargo-nextest
            pkg-config

            # General development, formatting, and repository hygiene.
            fd
            jq
            just
            nixfmt
            ripgrep
            taplo
          ];
        };
      }
    );
}
