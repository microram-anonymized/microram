#!/usr/bin/env bash
# Fetch EnigMap (odslib/EnigMap, USENIX Security 2023) at its pinned commit for
# the eviction comparator's `enigmap` arm (benchmarks/oram/
# cpu_tree_eviction_comparator_benchmark.cpp), used unpatched. Kept apart from
# fetch.sh so the baseline workers' embedded fetch record does not change.
#
#   benchmarks/baselines/fetch_enigmap.sh [DESTINATION]   (default third_party/enigmap)
#
# Then configure the main build with -DMICRORAM_ENIGMAP_DIR=<DESTINATION>.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
DEST="${1:-$ROOT/third_party/enigmap}"
URL="https://github.com/odslib/EnigMap"
COMMIT="4d0bfdb9fc2039029959092796f4d869ee7172ee"
# sha256 over `sha256sum` lines of every file, sorted by path (fetch.sh's tree hash).
TREE_SHA256="43a4e297f519d5a1a01ffcc2d827294f7fcbcee6aea8f9414c53e4311997cbe7"

fail() { echo "fetch_enigmap.sh: $*" >&2; exit 1; }
tree_sha256() {
  (cd "$1" && find . -path ./.git -prune -o -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum) |
    sha256sum | cut -d' ' -f1
}

mkdir -p "$(dirname "$DEST")"
WORK="$(mktemp -d "$(dirname "$DEST")/.fetch-enigmap-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT
git init -q "$WORK/enigmap"
git -C "$WORK/enigmap" fetch -q --depth 1 "$URL" "$COMMIT"
git -C "$WORK/enigmap" -c advice.detachedHead=false checkout -q FETCH_HEAD
[ "$(git -C "$WORK/enigmap" rev-parse HEAD)" = "$COMMIT" ] || fail "commit mismatch"
rm -rf "$WORK/enigmap/.git"
got="$(tree_sha256 "$WORK/enigmap")"
[ "$got" = "$TREE_SHA256" ] || fail "tree: expected $TREE_SHA256, got $got"
rm -rf "$DEST"
mv "$WORK/enigmap" "$DEST"
echo "EnigMap $COMMIT in $DEST"
