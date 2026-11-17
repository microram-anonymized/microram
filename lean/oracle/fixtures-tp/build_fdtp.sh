#!/usr/bin/env bash
# Build the top-preparation / initialization dumper outside CMake.
# Generated files stay in ORACLE_TP_WORK (default: lean/.lake/oracle/fixtures-tp).
# Pass --asserts to enable the engine's assertions.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean="$(cd "$here/../.." && pwd)"
repo="$(cd "$lean/.." && pwd)"
work="${ORACLE_TP_WORK:-$lean/.lake/oracle/fixtures-tp}"
mkdir -p "$work"
case "${1:-}" in
  "") flags=(-O2 -DNDEBUG); binary=fdtp ;;
  --asserts) flags=(-O1 -UNDEBUG); binary=fdtp_assert ;;
  *) echo "usage: $0 [--asserts]" >&2; exit 2 ;;
esac
"${CXX:-/usr/bin/c++}" "${flags[@]}" -std=c++17 -march=native -mno-avx512vp2intersect \
  -Wno-stringop-overread -Wno-stringop-overflow -I"$repo/include" -I"$repo" \
  "$here/fdtp.cpp" -o "$work/$binary" -pthread
