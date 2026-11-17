#!/usr/bin/env bash
# SONIC's own oblivious map, PMChain, run by SONIC's own driver (README.md in
# this directory, "SONIC's batched map"). It builds SONIC's demo, `sonic_demo`,
# from the fetched artifact as a top-level project (Clang, Release, its
# applications and AVX-512 primitives on), then runs its PMChain experiment
# with the data-tree settings of our SONIC batch rows (Par8: Z=16, S=16, R=3,
# eviction batch 2, 8 access workers, 8 eviction threads), 16-byte blocks and
# 5% writes, and prints the experiment's online throughput.
#
#   benchmarks/baselines/run_sonic_pmchain.sh [N] [BATCH] [BATCHES]
#
# Defaults: N = 1048576 (2^20), BATCH = 64, BATCHES = 256, the paper's run
# (145 requests/s on the AMD SEV-SNP machine). BATCH must be a multiple of 64,
# PMChain's position-map bucket. Each batch scans the whole position map, so a
# batch takes time linear in N: the default run takes about two minutes.
#
# Environment:
#   SONIC_DIR       SONIC's source tree (default third_party/baselines/sonic/sonic, from fetch.sh)
#   BUILD_DIR       build directory (default build-sonic-apps)
#   JOBS            build parallelism (default: every CPU)
#   ACCESS_WORKERS  -W (default 8)
#   EVICT_THREADS   --evict-threads (default 8)
#   TIMEOUT         seconds before the experiment is stopped (default 7200)
#   SKIP_BUILD=1    reuse an existing BUILD_DIR/bin/sonic_demo
#
# The full log goes to BUILD_DIR/pmchain-N<N>-m<BATCH>-b<BATCHES>.log; the last
# line printed is `online_requests_per_second=<value>`.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
N="${1:-1048576}"
BATCH="${2:-64}"
BATCHES="${3:-256}"
SONIC_DIR="${SONIC_DIR:-$ROOT/third_party/baselines/sonic/sonic}"
BUILD_DIR="${BUILD_DIR:-$ROOT/build-sonic-apps}"
JOBS="${JOBS:-$(nproc)}"
ACCESS_WORKERS="${ACCESS_WORKERS:-8}"
EVICT_THREADS="${EVICT_THREADS:-8}"
TIMEOUT="${TIMEOUT:-7200}"

fail() { echo "run_sonic_pmchain.sh: $*" >&2; exit 1; }
for value in "$N" "$BATCH" "$BATCHES" "$ACCESS_WORKERS" "$EVICT_THREADS" "$TIMEOUT"; do
  [[ "$value" =~ ^[1-9][0-9]*$ ]] || fail "expected a positive integer, got '$value'"
done
(( BATCH % 64 == 0 )) || fail "BATCH must be a multiple of 64 (PMChain's position-map bucket)"
(( BATCH <= N )) || fail "BATCH must not exceed N"
[ -f "$SONIC_DIR/CMakeLists.txt" ] || fail "no SONIC tree at $SONIC_DIR; run benchmarks/baselines/fetch.sh"

DEMO="$BUILD_DIR/bin/sonic_demo"
if [ "${SKIP_BUILD:-0}" != 1 ]; then
  echo "== building sonic_demo in $BUILD_DIR"
  mkdir -p "$BUILD_DIR"
  BUILD_LOG="$BUILD_DIR/build-sonic-demo.log"
  { CC="${CC:-clang}" CXX="${CXX:-clang++}" cmake -S "$SONIC_DIR" -B "$BUILD_DIR" -G Ninja \
        -DCMAKE_BUILD_TYPE=Release -DSONIC_BUILD_APPLICATIONS=ON -DSONIC_ENABLE_AVX512=ON &&
      cmake --build "$BUILD_DIR" -j "$JOBS" --target sonic_demo_native; } > "$BUILD_LOG" 2>&1 ||
    { tail -20 "$BUILD_LOG" >&2; fail "build failed (log $BUILD_LOG)"; }
  grep -E "CMAKE_CXX_COMPILER:|CMAKE_BUILD_TYPE:|SONIC_ENABLE_AVX512:|SONIC_BUILD_APPLICATIONS:" "$BUILD_DIR/CMakeCache.txt" || true
fi
[ -x "$DEMO" ] || fail "no $DEMO"
echo "sonic_demo sha256 $(sha256sum "$DEMO" | cut -d' ' -f1)"

LOG="$BUILD_DIR/pmchain-N$N-m$BATCH-b$BATCHES.log"
CMD=("$DEMO" pmchain experiment -N "$N" -m "$BATCH" -B 16 -Z 16 -S 16 -R 3 --evict-batch 2
     -W "$ACCESS_WORKERS" --evict-threads "$EVICT_THREADS" --batches "$BATCHES" --write-ratio 0.05)
echo "== ${CMD[*]}"
TIMER=()
[ -x /usr/bin/time ] && TIMER=(/usr/bin/time -v)
status=0
${TIMER[@]+"${TIMER[@]}"} timeout "$TIMEOUT" "${CMD[@]}" > "$LOG" 2>&1 || status=$?
grep -E "pmchain config|shape:|total_time:|throughput:|latency/batch:|pmchain experiment ok|Maximum resident|Elapsed" "$LOG" || true
[ "$status" = 0 ] || { tail -20 "$LOG" >&2; fail "the experiment exited with status $status (log $LOG)"; }
grep -q "pmchain experiment ok" "$LOG" || fail "no 'pmchain experiment ok' line (log $LOG)"
online="$(sed -n 's/.*throughput:.* online=\([0-9.]*\).*/\1/p' "$LOG" | tail -1)"
[ -n "$online" ] || fail "no online throughput in $LOG"
echo "log $LOG"
echo "online_requests_per_second=$online"
