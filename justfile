default:
    just --list

clean:
    find . -name "*.agdai" -type f -delete

haskell:
    cd lib/customer-deposit-wallet-pure/ && ./generate-haskell.sh

build0:
    cabal build -v0 -O0 -j all

ci:
    just haskell && git diff --exit-code && just build0
