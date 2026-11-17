#!/usr/bin/env bash
# Build the hierarchy-replay dumper (oracle/hierarchy_dump.cpp) outside CMake
# into lean/.lake/oracle-build/.  Pass --asserts for the engine's assertions
# (-O1 -UNDEBUG, binary hierarchy_dump_assert).
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean="$(cd "$here/.." && pwd)"
repo="$(cd "$lean/.." && pwd)"
work="${ORACLE_BUILD:-$lean/.lake/oracle-build}"
mkdir -p "$work"
# VP2INTERSECT is compiled out unless ORACLE_VP2INTERSECT=1 (then -march=native
# decides: on a VP2INTERSECT host the engine's native and segment paths run).
isa=(-mno-avx512vp2intersect)
[[ "${ORACLE_VP2INTERSECT:-0}" == 1 ]] && isa=()
case "${1:-}" in
  "") flags=(-O2 -DNDEBUG); binary=hierarchy_dump ;;
  --asserts) flags=(-O1 -UNDEBUG); binary=hierarchy_dump_assert ;;
  *) echo "usage: $0 [--asserts]" >&2; exit 2 ;;
esac
"${CXX:-/usr/bin/c++}" "${flags[@]}" -std=c++17 -march=native "${isa[@]}" \
  -Wno-stringop-overread -Wno-stringop-overflow -I"$repo/include" -I"$repo" \
  "$here/hierarchy_dump.cpp" -o "$work/$binary" -pthread
echo "$work/$binary"
