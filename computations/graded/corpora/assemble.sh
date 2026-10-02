#!/usr/bin/env bash
# Rebuild the packed certificate corpora from their committed parts, and check every file
# against its recorded SHA-256 (see README.md in this directory).
#
#   computations/graded/corpora/assemble.sh          # every corpus directory (3.99, ...)
#   computations/graded/corpora/assemble.sh 3.99     # one corpus directory
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
if [ $# -gt 0 ]; then
  dirs=("$@")
else
  dirs=()
  for d in "$here"/*/; do dirs+=("$(basename "$d")"); done
fi
for d in "${dirs[@]}"; do
  cd "$here/$d"
  echo "== $d"
  sha256sum -c --quiet SHA256SUMS.parts          # the committed parts are intact
  for first in *.part-00; do
    [ -e "$first" ] || continue
    f="${first%.part-00}"
    cat "$f".part-?? > "$f.tmp"                   # parts in suffix order: 00, 01, ...
    mv "$f.tmp" "$f"
  done
  sha256sum -c SHA256SUMS                         # the rebuilt files are the recorded ones
done
