#!/usr/bin/env bash
# Build the general-digit (radix) merge dumper (fd3.cpp) outside CMake.
# Generated files stay in ORACLE_RADIX_WORK (default: lean/.lake/oracle/fixtures-radix).
# Pass --asserts to enable the engine's assertions (binary fd3_assert).
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean="$(cd "$here/../.." && pwd)"
repo="$(cd "$lean/.." && pwd)"
work="${ORACLE_RADIX_WORK:-$lean/.lake/oracle/fixtures-radix}"
mkdir -p "$work"
case "${1:-}" in
  "") flags=(-O2 -DNDEBUG); binary=fd3 ;;
  --asserts) flags=(-O1 -UNDEBUG); binary=fd3_assert ;;
  *) echo "usage: $0 [--asserts]" >&2; exit 2 ;;
esac
"${CXX:-/usr/bin/c++}" "${flags[@]}" -std=c++17 -march=native -mno-avx512vp2intersect \
  -Wno-stringop-overread -Wno-stringop-overflow -I"$repo/include" -I"$repo" \
  "$here/fd3.cpp" -o "$work/$binary" -pthread
echo "built $work/$binary"
