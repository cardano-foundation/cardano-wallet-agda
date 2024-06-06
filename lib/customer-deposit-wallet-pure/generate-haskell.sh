#!/bin/sh
ROOT=Everything.agda 
agda2hs \
    --local-interfaces \
    --no-default-libraries \
    --config agda2hs-rewrites.yaml \
    -o ./haskell/ \
    ./agda/${ROOT} \
    && fourmolu -i ./haskell/

# agda \
#     --no-default-libraries \
#     ./agda/${ROOT}
