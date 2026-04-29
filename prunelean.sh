#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 /path/to/lean_dir"
  exit 1
fi

LEAN_DIR="$(realpath "$1")"

if [[ ! -d "$LEAN_DIR" ]]; then
  echo "Error: '$LEAN_DIR' is not a directory"
  exit 1
fi

cd "$LEAN_DIR"

# 1. Clean & rebuild to ensure only truly needed files are compiled
lake clean
lake build

# 2. Collect all .lean source files in the project
all_lean=$(find . -name "*.lean" \
  -not -path "./.lake/*" |
  sed 's|^\./||' | sort)

echo "=== Collected .lean source files ==="
echo "$all_lean"

# 3. Derive required .lean files from .olean artifacts in .lake/build
required_lean=$(find .lake/build -name "*.olean" |
  sed 's|\.lake/build/lib/||' |
  sed 's|^lean/||' |
  sed 's|\.olean$|.lean|' |
  sort)

echo "=== Required .lean source files ==="
echo "$required_lean"

# 4. Find unreferenced files
unreferenced=$(comm -23 \
  <(echo "$all_lean") \
  <(echo "$required_lean"))

echo "=== Files NOT required by lake build ==="
echo "$unreferenced"

# 5. Delete them (uncomment when you're confident)
# echo "$unreferenced" | xargs rm -f
