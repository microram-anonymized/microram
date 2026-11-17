#!/usr/bin/env bash
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
"${CXX:-/usr/bin/c++}" -O2 -UNDEBUG -std=c++17 -march=native "${isa[@]}" \
  -Wno-stringop-overread -Wno-stringop-overflow -I"$repo/include" -I"$repo" \
  "$here/api_native_dump.cpp" -o "$work/api_native_dump" -pthread
printf '%s\n' "$work/api_native_dump"
