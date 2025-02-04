#!/usr/bin/env bash
set -euo pipefail

# This script generates the `agda2hs-libraries` file
# which brings both the current global libraries
# and the local libraries in this repository into scope.

# We should do: cat the known libraries file in the local one
#AGDA2HS_LIB=/nix/store/xxxx-libraries
#cat $AGDA2HS_LIB > agda2hs-libraries

# We do: list the one global library that we know we depend on
cat <<EOF > agda2hs-libraries
$AGDA2HS_LIB
EOF

# Add local libraries
cat <<EOF >> agda2hs-libraries
$PWD/lib/containers/containers.agda-lib
$PWD/lib/cardano-wallet-read/cardano-wallet-read.agda-lib
$PWD/lib/customer-deposit-wallet-pure/customer-deposit-wallet-pure.agda-lib
EOF
