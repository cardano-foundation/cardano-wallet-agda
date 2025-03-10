# Nix flake based on Cardano base
# https://github.com/input-output-hk/cardano-base/blob/master/flake.nix
{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    nixpkgs.follows = "haskellNix/nixpkgs-unstable";

    haskellNix.url = "github:input-output-hk/haskell.nix";
    # We need the latest nixpkgs in order to get Agda 2.6.4
    # haskellNix.nixpkgs-unstable.follows = "nixpkgs";
    iohkNix.url = "github:input-output-hk/iohk-nix";
    iohkNix.inputs.nixpkgs.follows = "nixpkgs";

    CHaP.url = "github:intersectmbo/cardano-haskell-packages?ref=repo";
    CHaP.flake = false;

    flake-utils.url = "github:hamishmack/flake-utils/hkm/nested-hydraJobs";

    agda2hs.url =
      "github:agda/agda2hs?ref=7e24278eeee63fbe3775fabb204ea382c3d688bb";
    #    agda-tools.url = "github:HeinrichApfelmus/agda-notes?dir=nix/agda-hs-tools";
  };

  outputs =
    inputs@{ self, haskellNix, iohkNix, CHaP, flake-utils, nixpkgs, ... }:
    let
      profiling = false;
      supportedSystems =
        [ "x86_64-linux" "x86_64-darwin" "aarch64-linux" "aarch64-darwin" ];
      perSystem = system:
        let
          # setup our nixpkgs with the haskell.nix overlays, and the iohk-nix
          # overlays...
          pkgs = import nixpkgs {
            overlays = [ haskellNix.overlay ]
              ++ builtins.attrValues iohkNix.overlays;
            inherit system;
            inherit (haskellNix) config;
          };
          agda2hs = inputs.agda2hs.lib.${system}.withPackages
            ([ inputs.agda2hs.packages.${system}.agda2hs-lib ]);
          indexState = "2024-08-20T21:35:22Z";
          shell = { pkgs, ... }: {
            tools = {
              cabal = { index-state = indexState; };
              cabal-fmt = { index-state = indexState; };
              haskell-language-server = { index-state = indexState; };
              hoogle = { index-state = indexState; };
            };
            withHoogle = true;
            buildInputs = [
              pkgs.just
              pkgs.gitAndTools.git
              pkgs.haskellPackages.fourmolu
              pkgs.haskellPackages.ghcid
              pkgs.haskellPackages.hlint
              pkgs.haskellPackages.stylish-haskell
              agda2hs
            ];
            shellHook = ''
              export AGDA_DIR=${agda2hs.outPath}
              export AGDA2HS_LIB=${
                inputs.agda2hs.packages.${system}.agda2hs-lib
              }/agda2hs.agda-lib
            '';
          };

          mkProject = ctx@{ lib, pkgs, ... }: {
            name = "cardano-deposit-wallet-pure";
            compiler-nix-name = "ghc966";
            src = ./.;
            shell = shell { inherit pkgs; };
            inputMap = { "https://chap.intersectmbo.org/" = CHaP; };
          };
          project = pkgs.haskell-nix.cabalProject' mkProject;
          packages = {
            inherit project;
            cardano-deposit-wallet-pure =
              project.hsPkgs.cardano-deposit-wallet-pure.components.lib.cardano-deposit-wallet-pure;
            cardano-wallet-read =
              project.hsPkgs.cardano-wallet-read.components.lib.cardano-wallet-read;
          };

        in {
          inherit packages;
          devShell = project.shell;
        };

    in flake-utils.lib.eachSystem supportedSystems perSystem;

  nixConfig = {
    extra-substituters = [ "https://cache.iog.io" ];
    extra-trusted-public-keys =
      [ "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=" ];
    allow-import-from-derivation = true;
  };
}
