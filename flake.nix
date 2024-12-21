{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
    utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      utils,
    }:
    utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      rec {
        formatter = pkgs.nixfmt-rfc-style;

        packages.sf2tal = pkgs.haskellPackages.developPackage {
          root = ./.;
          returnShellEnv = true;
          withHoogle = false;
        };

        devShells.default = packages.sf2tal.overrideAttrs (old: {
          nativeBuildInputs =
            old.nativeBuildInputs
            ++ (with pkgs; [
              editorconfig-checker
              nixfmt-rfc-style
              cabal-install
              hlint
              haskellPackages.fourmolu
            ]);
        });
      }
    );
}
