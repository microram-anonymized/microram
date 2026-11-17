#!/bin/bash
# Compiler launcher that builds for another CPU than this one: every
# -march=native becomes -march=$CENSUS_MARCH (default graniterapids).  The
# binaries need not run here; instruction_census.py only disassembles them.
#
#   CENSUS_MARCH=graniterapids cmake -S . -B build-gnr -DCMAKE_CXX_FLAGS=-g1 \
#       -DCPU_BYTESLICE_ORAM_BUILD=all \
#       -DCMAKE_CXX_COMPILER_LAUNCHER=$PWD/tests/timing/march_launcher.sh
#
# The variable is read at compile time, so export it for the build too.
march="${CENSUS_MARCH:-graniterapids}"
args=()
for a in "$@"; do
  if [ "$a" = "-march=native" ]; then a="-march=$march"; fi
  args+=("$a")
done
exec "${args[@]}"
