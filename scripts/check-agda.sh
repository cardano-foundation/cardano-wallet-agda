#!/usr/bin/env bash
set -euo pipefail

# This script checks the `Everything*.agda` file
# in the directory "$1/agda".

ROOT_DIR="$PWD"
DIR="$1"

echo "Type checking $DIR."

cd "$DIR" && agda2hs \
    --local-interfaces \
    --no-default-libraries \
    --library-file "$ROOT_DIR/agda2hs-libraries" \
    --disable-backend \
    ./agda/Everything*.agda \
