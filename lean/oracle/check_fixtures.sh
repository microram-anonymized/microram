#!/usr/bin/env bash
# Differential test of the Lean model against the engine over fixture directories.
#
#   oracle/check_fixtures.sh <dir>...
#   ORACLE_ARGS=--sep oracle/check_fixtures.sh <dir>...   (the general-digit model)
#   ORACLE_JOBS=16 oracle/check_fixtures.sh <dir>...      (16 oracle processes)
#
# Runs `oracle` (default mode: model vs engine) on every *.json under each
# directory (recursively), except the generators' non-fixture files
# (manifest.json, summary.json, results.json; their count is printed), in
# one process per directory chunk, then prints the
# counts of O1 (engine output), O1 (model output), O2, O3 and scatter pass/fail, the
# failing-test-kind agreement, and the list of mismatching fixtures. Top-finish
# fixtures (top-finish-fixture/0) whose inputs break TopShape on purpose report
# O1 as "premise"; O2 and O3 still apply to them.
# Exit status 0 iff every directory exists and holds at least one fixture,
# every fixture agrees and no fixture is malformed.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean="$(cd "$here/.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
[ $# -ge 1 ] || { echo "usage: $0 <dir>..." >&2; exit 2; }
(cd "$lean" && lake build oracle >/dev/null 2>&1) || { echo "FAIL: lake build oracle"; exit 1; }
bin="$lean/.lake/build/bin/oracle"
status=0
for d in "$@"; do
  [ -d "$d" ] || { echo "FAIL: $d is not a directory"; status=1; continue; }
  out="$(mktemp)"
  # Non-fixture JSON written by the generators: manifest.json (d = 2, top,
  # top preparation), summary.json (top preparation), results.json (radix).
  find "$d" -name '*.json' ! -name manifest.json ! -name summary.json \
    ! -name results.json | sort > "$out.list"
  skipped="$(find "$d" \( -name manifest.json -o -name summary.json \
    -o -name results.json \) | wc -l)"
  [ "$skipped" -gt 0 ] && echo "($d: skipping $skipped non-fixture JSON file(s))"
  if [ ! -s "$out.list" ]; then
    echo "FAIL: no fixtures under $d"; status=1; rm -f "$out" "$out".*; continue
  fi
  : > "$out"
  # chunks keep the command line short; ORACLE_JOBS > 1 runs that many
  # chunks of 20 at a time (the order of the output lines does not matter)
  jobs_n="${ORACLE_JOBS:-1}"
  if [ "$jobs_n" -gt 1 ]; then per=20; else per=200; fi
  split -l "$per" "$out.list" "$out.chunk."
  printf '%s\n' "$out".chunk.* | xargs -P "$jobs_n" -I{} sh -c \
    'xargs -a "$1" "$2" $3 > "$1.res" 2> "$1.err"; echo $? > "$1.rc"' \
    sh {} "$bin" "${ORACLE_ARGS:-}"
  for c in "$out".chunk.*; do
    case "$c" in *.res|*.err|*.rc) continue ;; esac
    cat "$c.res" >> "$out" 2>/dev/null
    rc="$(cat "$c.rc" 2>/dev/null || echo 2)"
    [ "$rc" -ge 2 ] && status=1
  done
  python3 - "$d" "$out" "$(wc -l < "$out.list")" <<'PY' || status=1
import json, sys, collections
d, path, expected = sys.argv[1], sys.argv[2], int(sys.argv[3])
c = collections.Counter(); bad = []
kinds = collections.Counter()
n = 0
for line in open(path):
    line = line.strip()
    if not line: continue
    n += 1
    try: r = json.loads(line)
    except Exception: bad.append(("<unparsable>", line[:100])); continue
    f = r.get("file", "?")
    ok = True
    if r.get("o1") == "malformed": c["malformed"] += 1; ok = False
    for k in ("o1", "o1_model", "o2", "o3", "scatter", "comparison", "snapshots"):
        if k in r: c[(k, r[k])] += 1
        if r.get(k) == "fail": ok = False
    if "kind" in r:
        c[("kind", r["kind"])] += 1
        if r["kind"] != "match": ok = False
    if not ok: bad.append((f, {k: r.get(k) for k in ("o1","o1_model","o2","o3","scatter","comparison","snapshots","kind","engine_kind","model_kind","diff_count")}))
print(f"== {d}: {n} fixtures ==")
for k in ("o1", "o1_model", "o2", "o3", "scatter", "comparison", "snapshots"):
    if k == "scatter" and not any(c[(k, v)] for v in ("pass", "fail", "skipped")): continue
    vals = ", ".join(f"{v}={c[(k,v)]}" for v in ("pass","fail","skipped","premise") if c[(k,v)])
    if vals: print(f"  {k}: " + vals)
if c[("kind","match")] or c[("kind","mismatch")]:
    print(f"  failing-test kind: match={c[('kind','match')]} mismatch={c[('kind','mismatch')]}")
if c["malformed"]: print(f"  malformed={c['malformed']}")
print(f"  mismatching fixtures: {len(bad)}")
if n != expected:
    print(f"  FAIL: {n} result lines for {expected} fixtures")
    bad.append(("<count>", n))
for f, info in bad[:50]: print("    ", f, info)
sys.exit(1 if bad else 0)
PY
  rm -f "$out" "$out".*
done
exit $status
