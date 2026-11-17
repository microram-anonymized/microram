#!/usr/bin/env bash
# Build the top-finish dumper (fdtop.cpp) outside CMake.
# Generated files stay in ORACLE_TOP_WORK (default: lean/.lake/oracle/fixtures-top).
# Pass --asserts to enable the engine's assertions (binary fdtop_assert).
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean="$(cd "$here/../.." && pwd)"
repo="$(cd "$lean/.." && pwd)"
work="${ORACLE_TOP_WORK:-$lean/.lake/oracle/fixtures-top}"
mkdir -p "$work"
case "${1:-}" in
  "") flags=(-O2 -DNDEBUG); binary=fdtop ;;
  --asserts) flags=(-O1 -UNDEBUG); binary=fdtop_assert ;;
  *) echo "usage: $0 [--asserts]" >&2; exit 2 ;;
esac
"${CXX:-/usr/bin/c++}" "${flags[@]}" -std=c++17 -march=native -mno-avx512vp2intersect \
  -Wno-stringop-overread -Wno-stringop-overflow -I"$repo/include" -I"$repo" \
  "$here/fdtop.cpp" -o "$work/$binary" -pthread
echo "built $work/$binary"
