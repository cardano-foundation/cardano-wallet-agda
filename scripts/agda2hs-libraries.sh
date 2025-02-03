#!/usr/bin/env bash

# We should do: cat the known libraries file in the local one
#AGDA2HS_LIB=/nix/store/xxxx-libraries
#cat $AGDA2HS_LIB > agda2hs-libraries

# We do: list the one global library that we know we depend on
cat <<EOF > agda2hs-libraries
$AGDA2HS_LIB
EOF

# Add local libraries
cat <<EOF >> agda2hs-libraries
$PWD/lib/customer-deposit-wallet-pure/customer-deposit-wallet-pure.agda-lib
EOF
