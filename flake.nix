{
  description = "Haskell 'pdp' library";

  inputs = {
    nixpkgs.url =
      "github:NixOS/nixpkgs/43297919d746de7b71fc83dba95272b2991ba20f";
    flake-parts.url = "github:hercules-ci/flake-parts";
    hs_kind = {
      url = "github:k0001/hs-kind";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-parts.follows = "flake-parts";
    };
  };

  outputs = inputs@{ ... }:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } {
      flake.overlays.default = inputs.nixpkgs.lib.composeManyExtensions [
        inputs.hs_kind.overlays.default
        (final: prev:
          let
            hsLib = prev.haskell.lib;
            hsClean = drv:
              hsLib.overrideCabal drv
              (old: { src = prev.lib.sources.cleanSource old.src; });
          in {
            haskell = prev.haskell // {
              packageOverrides = prev.lib.composeExtensions
                (prev.haskell.packageOverrides or (_: _: { }))
                (hself: hsuper: { pdp = hself.callPackage ./pdp { }; });
            };
          })
      ];
      systems = [ "x86_64-linux" ];
      perSystem = { config, system, pkgs, ... }: {
        _module.args.pkgs = import inputs.nixpkgs {
          inherit system;
          overlays = [ inputs.self.overlays.default ];
        };
        packages = {
          default = pkgs.releaseTools.aggregate {
            name = "every output from this flake";
            constituents = [
              config.devShells.ghc96
              config.packages.pdp__ghc96
              config.packages.pdp__ghc96.doc
              config.packages.pdp__ghc96__sdist
              config.packages.pdp__ghc96__sdistDoc
            ];
          };

          pdp__ghc96 = pkgs.haskell.packages.ghc96.pdp;
          pdp__ghc96__sdist =
            pkgs.haskell.packages.ghc96.cabalSdist { src = ./pdp; };
          pdp__ghc96__sdistDoc =
            pkgs.haskell.lib.documentationTarball config.packages.pdp__ghc96;
        };
        devShells = let
          mkShellFor = ghc:
            ghc.shellFor {
              packages = p: [ p.pdp ];
              withHoogle = false;
              nativeBuildInputs =
                [ pkgs.cabal-install pkgs.cabal2nix pkgs.ghcid ];
            };
        in {
          default = config.devShells.ghc96;
          ghc96 = mkShellFor pkgs.haskell.packages.ghc96;
        };
      };
    };
}
