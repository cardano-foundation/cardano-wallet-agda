#!/bin/sh
ROOT=Cardano/Wallet/Deposit/Pure.agda 
agda2hs \
    --local-interfaces \
    --no-default-libraries \
    --config agda2hs-rewrites.yaml \
    -o ./haskell/ \
    ./agda/${ROOT}

# agda \
#     --no-default-libraries \
#     ./agda/${ROOT}
