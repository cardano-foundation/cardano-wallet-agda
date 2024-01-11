# Nix flake based on Cardano base
# https://github.com/input-output-hk/cardano-base/blob/master/flake.nix
{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    nixpkgs.follows = "haskellNix/nixpkgs-unstable";

    haskellNix.url = "github:input-output-hk/haskell.nix";
    # We need the latest nixpkgs in order to get Agda 2.6.4
    # haskellNix.inputs.nixpkgs-unstable.follows = "nixpkgs";
    iohkNix.url = "github:input-output-hk/iohk-nix";
    iohkNix.inputs.nixpkgs.follows = "nixpkgs";

    CHaP.url = "github:intersectmbo/cardano-haskell-packages?ref=repo";
    CHaP.flake = false;

    flake-utils.url = "github:hamishmack/flake-utils/hkm/nested-hydraJobs";

    agda-tools.url = "github:HeinrichApfelmus/agda-notes?dir=nix/agda-hs-tools";
  };

  outputs = inputs:
    let
      profiling = false;
      supportedSystems = [
        "x86_64-linux"
        "x86_64-darwin"
        # not supported on ci.iog.io right now
        #"aarch64-linux"
        "aarch64-darwin"
       ]; in
    inputs.flake-utils.lib.eachSystem supportedSystems (system:
      let
        # setup our nixpkgs with the haskell.nix overlays, and the iohk-nix
        # overlays...
        nixpkgs = import inputs.nixpkgs {
          overlays = [inputs.haskellNix.overlay]
            ++ builtins.attrValues inputs.iohkNix.overlays;
          inherit system;
          inherit (inputs.haskellNix) config;
        };

        indexState = "2024-03-15T17:07:52Z";

        # ... and construct a flake from the cabal.project file.
        # We use cabalProject' to ensure we don't build the plan for
        # all systems.
        flake = (nixpkgs.haskell-nix.cabalProject' rec {
          src = ./.;
          name = "customer-deposit-wallet-pure";
          compiler-nix-name = "ghc964";

          inputMap = { "https://chap.intersectmbo.org/" = inputs.CHaP; };

          # tools we want in our shell
          shell.tools = {
            cabal = {
              version = "3.10.2.1";
              index-state = indexState;
            };
            fourmolu = "0.14.1.0";
          };
          shell.withHoogle = true;

          shell.buildInputs = [
            nixpkgs.just
            nixpkgs.gitAndTools.git
            nixpkgs.haskellPackages.ghcid
            nixpkgs.haskellPackages.hlint

            inputs.agda-tools.packages.${system}.agda
            inputs.agda-tools.packages.${system}.agda2hs
          ];

          shell.shellHook = ''
            export AGDA_DIR=${inputs.agda-tools.packages.${system}.agda-dir.outPath}
          '';
        }).flake (
          # we also want cross compilation to windows.
          nixpkgs.lib.optionalAttrs (system == "x86_64-linux") {
          crossPlatforms = p: [p.mingwW64];
        });
      in flake
    );

  nixConfig = {
    extra-substituters = [
      "https://cache.iog.io"
    ];
    extra-trusted-public-keys = [
      "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="
    ];
    allow-import-from-derivation = true;
  };
}
