default:
    just --list

haskell:
    cd lib/customer-deposit-wallet-pure/ && ./generate-haskell.sh

build0:
    cabal build -v0 -O0 -j all

clean:
    find . -name "*.agdai" -type f -delete
