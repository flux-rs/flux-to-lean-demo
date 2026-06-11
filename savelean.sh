#!/usr/bin/env bash
# savelean.sh — persist hand-written Lean proofs from the working project back
# into the source-of-truth `LeanUserProofs/`.
#
# This is the INVERSE of the `cp -r LeanUserProofs/* lean_proofs/LeanProofs/`
# step inside runlean.sh. Run it by hand after you've edited/fixed proofs in
# lean_proofs/LeanProofs/User/ so the next `runlean.sh` picks up the latest work.
# It is intentionally NOT called from runlean.sh.
#
# It mirrors ONLY the hand-written dirs (User/, Lib/) — never the Flux-generated
# tree (Flux/, Basic.lean), which `cargo flux` regenerates from src/*.rs.
#
# Typical loop:
#   ./runlean.sh     # cargo flux -> VCs; copy saved proofs in; lake build; recheck
#   #   ... edit / fix proofs in lean_proofs/LeanProofs/User/ ...
#   ./savelean.sh    # push edits back into LeanUserProofs/  (then git commit)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SRC="$ROOT/lean_proofs/LeanProofs"
DST="$ROOT/LeanUserProofs"

if [[ ! -d "$SRC" ]]; then
  echo "error: '$SRC' not found — run ./runlean.sh first." >&2
  exit 1
fi

for d in User Lib; do
  if [[ -d "$SRC/$d" ]]; then
    n=$(find "$SRC/$d" -name '*.lean' | wc -l | tr -d ' ')
    echo "saving $d/  ($n .lean files)  ->  LeanUserProofs/$d/"
    rm -rf "${DST:?}/$d"
    cp -r "$SRC/$d" "$DST/$d"
  fi
done

echo
echo "Saved working proofs into LeanUserProofs/. Review & commit the source-of-truth:"
echo "  git status LeanUserProofs/"
echo "  git add LeanUserProofs/ && git commit -m 'update proofs'"
