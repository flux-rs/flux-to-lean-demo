#!/bin/bash

cargo flux
cp -r LeanUserProofs/* lean_proofs/LeanProofs/User/
cd lean_proofs
lake build
cd ..
cargo flux

