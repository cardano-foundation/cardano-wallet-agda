default:
    just --list

clean:
    find . -name "*.agdai" -type f -delete

agda2hs-libraries:
    ./scripts/agda2hs-libraries.sh

haskell:
    just agda2hs-libraries
    cd lib/customer-deposit-wallet-pure/ && ./generate-haskell.sh

build:
    cabal build -O -j all

build0:
    cabal build -v0 -O0 -j all

doc:
    cabal haddock -v0 -O0 -j all

test:
    cabal test -v0 -O0 -j all

ci-check-agda:
    just agda2hs-libraries
    ./scripts/check-agda.sh lib/containers
    ./scripts/check-agda.sh lib/cardano-wallet-read

ci-build-agda:
    just haskell && git diff --exit-code

ci-build-hs:
    cabal update && cabal build -v0 -j all -frelease

ci-check:
    # We do not rebuild the .hs files,
    # as the ci-build step fails if they are not up-to-date.
    cabal test -v0 -O0 -j all

format-read:
  ( cd lib/cardano-wallet-read && \
    stylish-haskell -v --config ../../.stylish-haskell.yaml --inplace $(git ls-files -- '*.hs') \
  )