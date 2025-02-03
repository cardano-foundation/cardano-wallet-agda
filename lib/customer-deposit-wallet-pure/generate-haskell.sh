#!/bin/sh
ROOT=Everything.agda 
agda2hs \
    --local-interfaces \
    --no-default-libraries \
    --library-file ../../agda2hs-libraries \
    --config agda2hs-rewrites.yaml \
    -o ./haskell/ \
    ./agda/${ROOT} \
    && find ./haskell/ -type f -name '*.hs' -exec cabal run agda2hs-fixer -- {} + \
    && fourmolu -i ./haskell/

# agda \
#     --no-default-libraries \
#     ./agda/${ROOT}
