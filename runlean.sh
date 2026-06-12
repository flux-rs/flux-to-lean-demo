#!/bin/bash

cargo flux
cp -r LeanUserProofs/User LeanUserProofs/Lib lean_proofs/LeanProofs/ 2>/dev/null || true
if [ -f LeanUserProofs/lakefile.toml ]; then
  cp LeanUserProofs/lakefile.toml lean_proofs/lakefile.toml
fi
cd lean_proofs
lake update
lake build
cd ..
cargo flux
