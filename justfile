default:
    just --list

clean:
    find . -name "*.agdai" -type f -delete

haskell:
    cd lib/customer-deposit-wallet-pure/ && ./generate-haskell.sh

build:
    cabal build -v0 -O -j all

build0:
    cabal build -v0 -O0 -j all

ci-build:
    just haskell && git diff --exit-code && just build0

ci-check:
    # We do not rebuild the .hs files,
    # as the ci-build step fails if they are not up-to-date.
    cabal test -v0 -O0 -j all
