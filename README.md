
🚧 WORK IN PROGRESS 🚧

## Overview

This repository contains prototypes of wallet implementations for the Cardano blockchain that are formally verified using [Agda][] and [agda2hs][].

  [agda]: https://github.com/agda/agda
  [agda2hs]: https://github.com/agda/agda2hs

## Contents

This repository is strucured as follows:

* `flake.nix` — Nix flake for a development shell with relevant Haskell and Agda tools in scope.
* `lib/customer-deposit-wallet-pure/` — specification and implementation of a pure Deposit Wallet. The Agda source code in `agda/` is transpiled to Haskell using the `generate-haskell.sh` script.

## QuickStart

Prerequisites:

* [Nix package manager][nix].

How to build:

```console
nix develop
cd lib/customer-deposit-wallet-pure
./generate-haskell.sh
cd ../..
cabal build customer-deposit-wallet-pure
```

How to run tests:

* There are no unit tests in this repository — only compiler-checked proofs. 😏

How to run:

* N/A. This project is a [Haskell package][hackage]. For an exectuable wallet, see the [cardano-wallet][] project.

## Contributors

See [CONTRIBUTING.md](CONTRIBUTING.md).

## Roadmap

* Completion of implementation.
* Completion of proofs.


  [cardano-wallet]: https://github.com/cardano-foundation/cardano-wallet
  [hackage]: https://hackage.haskell.org
  [nix]: https://nixos.org/download/
