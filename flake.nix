{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
    effectful-microlens = {
      url = "git+https://codeberg.org/eownerdead/effectful-microlens";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-parts.follows = "flake-parts";
      };
    };
    hs-bindgen = {
      url = "github:eownerdead/hs-bindgen/llvm-c-raw";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-parts.follows = "flake-parts";
      };
    };
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } (
      { lib, ... }:
      {
        systems = [
          "x86_64-linux"
        ];
        imports = [
          inputs.haskell-flake.flakeModule
        ];

        perSystem =
          {
            pkgs,
            inputs',
            system,
            lib,
            ...
          }:
          {
            formatter = pkgs.nixfmt-rfc-style;

            haskellProjects.default = {
              imports = [
                inputs.hs-bindgen.haskellFlakeProjectModules.output
              ];
              devShell = {
                tools = hpkgs: {
                  inherit (pkgs) nixfmt-rfc-style;
                  inherit (hpkgs) hs-bindgen;
                };
                mkShellArgs = {
                  nativeBuildInputs = with pkgs.llvmPackages; [
                    libllvm
                    clang
                  ];
                  BINDGEN_EXTRA_CLANG_ARGS =
                    lib.readFile "${pkgs.clang}/nix-support/libc-cflags"
                    + lib.readFile "${pkgs.clang}/nix-support/cc-cflags";
                };
              };
              packages = {
                haskell-stack-trace-plugin.source = pkgs.fetchFromGitHub {
                  owner = "waddlaw";
                  repo = "haskell-stack-trace-plugin";
                  rev = "cd80eb034c32b28e98ab69d0e94f90577162c024";
                  hash = "sha256-scfk2gaY/sjyr8RRmb0Sk0iBqCZmxrC+FluznfqvxM8=";
                };
              };
              settings = {
                effectful-microlens.custom =
                  _: inputs'.effectful-microlens.packages.effectful-microlens;
                haskell-stack-trace-plugin.check = false;

                # HACK: https://github.com/srid/haskell-flake/issues/198#issuecomment-2824602736
                LLVM.custom = _: pkgs.llvmPackages.llvm;
                LTO.custom = _: pkgs.llvmPackages.llvm;
                Remarks.custom = _: pkgs.llvmPackages.llvm;
              };
            };
          };
      }
    );
}
