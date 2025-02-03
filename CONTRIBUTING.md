If you find a bug or you'd like to propose a feature, please feel free to raise an issue on our [issue tracker](https://github.com/cardano-foundation/cardano-wallet-agda/issues).

Please note we have a [code of conduct](CODE_OF_CONDUCT.md), please follow it in all your interactions with the project.

# Development

## Editor integration and local libraries

This repository contains several `.agda-lib` libraries. In order to develop these libraries interactively in an editor such as VSCode, you need to generate a custom `libraries` file that brings them into scope for `agda2hs`. The following command will do that:

      nix develop
      just agda2hs-libraries

(This command is implied when developing non-interactively.)

In order to make the custom `libraries` available in VSCode, I recommend the following `.envrc` file for use with the [direenv extension][direnv]:

    # cat .envrc
    use flake
    export AGDA2HS_FLAGS="--library-file ${PWD}/agda2hs-libraries"

and put `${AGDA2HS_FLAGS}` in the settings for the `agda-mode` extension.

  [direnv]: https://github.com/direnv/direnv-vscode

Sorry for the fuss — `agda2hs` currently does not have a good story for developing multiple local libraries.

## Branches

We use [trunk-based development][trunk]: We merge features and improvements into the `main` branch frequently. If a large feature takes more than one pull request to develop, and is therefore incomplete, we hide it behind a feature flag. The `main` branch should be kept in a state where all checks pass, so that we can release it at any time.

  [trunk]: https://martinfowler.com/articles/branching-patterns.html#Trunk-basedDevelopment

## Continuous Integration (CI)

We use [continuous integration][ci]: Checking proofs, building artifacts, and testing artifacts is done automatically before changes are admitted to the `main` branch.

We use [Buildkite][] for automation.
Our Buildkite pipeline is defined in [.buildkite/pipeline.yml](.buildkite/pipeline.yml). The build environment is provisioned using the [Nix package manager][nix]. The relevant build steps are grouped in the [`justfile`][just] under the `ci-` prefix.

  [ci]: https://www.goodreads.com/book/show/17255186-the-phoenix-project
  [nix]: https://nixos.org/download/
  [buildkite]: https://buildkite.com/cardano-foundation/cardano-wallet-agda/
  [just]: https://github.com/casey/just
