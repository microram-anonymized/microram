#!/usr/bin/env bash
# Compile oracle/fixture_dump.cpp into ../.lake/oracle-build/fixture_dump
# (gitignored).  Skips the compile when the binary is newer than the source and
# every header it could include (pass --force to rebuild regardless).
#
# Usage: oracle/build_dumper.sh [--force] [--asserts]
#   --asserts   build with -UNDEBUG (engine asserts on; slower, stricter)
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean="$(cd "$here/.." && pwd)"
repo="$(cd "$lean/.." && pwd)"
out_dir="$lean/.lake/oracle-build"
out="$out_dir/fixture_dump"

force=0
ndebug=(-DNDEBUG)
for a in "$@"; do
  case "$a" in
    --force) force=1 ;;
    --asserts) ndebug=(-UNDEBUG); force=1 ;;
    *) echo "build_dumper.sh: unknown option $a" >&2; exit 2 ;;
  esac
done

mkdir -p "$out_dir"
if [ "$force" = 0 ] && [ -x "$out" ]; then
  # Stale if the source, or any engine / test-support header, is newer.
  newer="$(find "$here/fixture_dump.cpp" "$repo/src" "$repo/include" \
                "$repo/tests/oram/cpu_byteslice_level_arena_test_support.hpp" \
                "$repo/tests/oram/cpu_byteslice_test_support.hpp" \
                "$repo/tests/oram/cpu_byteslice_rebuild_test_support.hpp" \
                \( -name '*.cpp' -o -name '*.hpp' -o -name '*.h' \) \
                -newer "$out" -print -quit 2>/dev/null || true)"
  if [ -z "$newer" ]; then
    echo "fixture_dump: up to date ($out)"
    exit 0
  fi
fi

echo "fixture_dump: compiling -> $out"
cd "$here"
/usr/bin/c++ -O2 "${ndebug[@]}" -std=c++17 -march=native \
  -mno-avx512vp2intersect -Wno-stringop-overread -Wno-stringop-overflow \
  -I"$repo/include" -I"$repo" fixture_dump.cpp -o "$out" -pthread
echo "fixture_dump: built $out"
