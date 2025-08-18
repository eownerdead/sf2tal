{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
    flake-parts.url = "github:hercules-ci/flake-parts";
    effectful-microlens = {
      url = "git+https://codeberg.org/eownerdead/effectful-microlens";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-parts.follows = "flake-parts";
      };
    };
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
        "x86_64-darwin"
      ];

      perSystem =
        {
          self',
          inputs',
          system,
          pkgs,
          ...
        }:
        {
          formatter = pkgs.nixfmt-rfc-style;

          packages.sf2tal = pkgs.haskellPackages.developPackage {
            root = ./.;
            overrides = self: super: {
              effectful-microlens = inputs'.effectful-microlens.packages.effectful-microlens;
              haskell-stack-trace-plugin = super.developPackage {
                root = pkgs.fetchFromGitHub {
                  owner = "waddlaw";
                  repo = "haskell-stack-trace-plugin";
                  rev = "cd80eb034c32b28e98ab69d0e94f90577162c024";
                  hash = "sha256-scfk2gaY/sjyr8RRmb0Sk0iBqCZmxrC+FluznfqvxM8=";
                };
                modifier = drv: pkgs.haskell.lib.dontCheck drv;
              };
            };
          };

          devShells.default = pkgs.haskellPackages.shellFor {
            packages = hpkgs: [
              self'.packages.sf2tal
            ];
            nativeBuildInputs = with pkgs; [
              nixfmt-rfc-style
              cabal-install
              hlint
              haskellPackages.fourmolu
              llvmPackages_16.libllvm
            ];
          };
        };
    };
}
