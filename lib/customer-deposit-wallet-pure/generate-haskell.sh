#!/bin/sh
agda2hs \
    --no-default-libraries \
    -o ./src/haskell/ \
    ./src/agda/Language/FineTypes.agda
# agda2hs -v agda2hs.compile:7 ./src/agda/Language/FineTypes.agda -o ./src/haskell/
