#!/usr/bin/env bash
# Regenerate the hierarchy-replay fixture battery (`hierarchy-replay/0`,
# HIERARCHY_REPLAY_SCHEMA.md) under lean/.lake/oracle/hierarchy/ (gitignored).
#
#   oracle/gen_hierarchy_fixtures.sh [--asserts] [--no-selected] [-j N]
#
# Builds the dumper first (build_hierarchy_dump.sh).  Every fixture runs with
# --sync-check and --view (the adversary's view of the arena and the
# synchronous engine, every access; for the batch fixtures every AccessBatch
# lane, chunk by chunk).  The four selected runs (j_selected_*) allocate the
# 2^22-bucket top (about 15 GB each with the synchronous engine) and take about
# 30 s each; --no-selected skips them.  -j N runs N dumpers at once (default 8).
# Exit status: nonzero if any dumper run exits nonzero.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean="$(cd "$here/.." && pwd)"
asserts=""
selected=1
jobs=8
while [ $# -gt 0 ]; do
  case "$1" in
    --asserts) asserts="--asserts" ;;
    --no-selected) selected=0 ;;
    -j) shift; jobs="$1" ;;
    *) echo "usage: $0 [--asserts] [--no-selected] [-j N]" >&2; exit 2 ;;
  esac
  shift
done
bin="$("$here/build_hierarchy_dump.sh" $asserts | tail -1)"
out="${HIERARCHY_FIXTURES:-$lean/.lake/oracle/hierarchy}"
mkdir -p "$out"
options=(--dumper "$bin" --out "$out" -j "$jobs")
if [ "$selected" = 0 ]; then options+=(--no-selected); fi
exec python3 -I "$here/hierarchy_fixture_manifest.py" "${options[@]}"
