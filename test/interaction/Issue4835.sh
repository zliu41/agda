#!/usr/bin/env bash

AGDA=$1

$AGDA --interaction --ignore-interfaces <<EOF
IOTCM "Issue4835/ModA.agda" None Indirect (Cmd_load "Issue4835/ModA.agda" [])
IOTCM "Issue4835/ModB.agda" None Indirect (Cmd_load "Issue4835/ModB.agda" [])
EOF

echo
runhaskell Issue4835/Count.hs
