#!/usr/bin/env bash
# Oracle round trip: C++ engine -> JSON fixture -> Lean checker.
#
#   oracle/roundtrip.sh
#
# 1. builds the C++ dumper (if stale) and `lake build oracle`;
# 2. dumps the real d = 2 fixture to .lake/oracle/fixture_d2.json and runs
#    `lake exe oracle` on it (must pass O1);
# 3. dumps a capacity-FAILURE fixture (fixture_d2_fail.json) and checks the
#    oracle reports the engine verdict and skips O1;
# 4. runs mutation tests on copies of the real fixture -- every one MUST make
#    the oracle fail (exit 1) -- plus an unmodified control (must pass) and a
#    truncated file (must be rejected as malformed, exit 2).
#
# Exit status is nonzero if the real fixture fails, the failure fixture is not
# reported as such, or any mutation is accepted.
#
# Environment: DUMP_ARGS (extra dumper arguments for the real fixture).
set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean="$(cd "$here/.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
dumper="$lean/.lake/oracle-build/fixture_dump"
work="$lean/.lake/oracle"
fixture="$work/fixture_d2.json"
fail_fixture="$work/fixture_d2_fail.json"
mut_dir="$work/mutants"
mkdir -p "$work"
rm -rf "$mut_dir"
mkdir -p "$mut_dir"

now() { date +%s.%N; }
elapsed() { awk -v a="$1" -v b="$2" 'BEGIN { printf "%.1fs", b - a }'; }
status=0

echo "== build =="
t0=$(now)
"$here/build_dumper.sh" || { echo "FAIL: dumper build"; exit 1; }
t1=$(now)
if ! build_out="$(cd "$lean" && lake build oracle 2>&1)"; then
  echo "$build_out"; echo "FAIL: lake build oracle"; exit 1
fi
echo "$build_out" | tail -1
t2=$(now)
echo "dumper: $(elapsed "$t0" "$t1")   lake build oracle: $(elapsed "$t1" "$t2")"

oracle() { (cd "$lean" && lake exe oracle "$@"); }
# The mutants go through the built executable directly: `lake exe` start-up
# costs about a second per call.
oracle_bin="$lean/.lake/build/bin/oracle"
oracle_fast() { if [ -x "$oracle_bin" ]; then "$oracle_bin" "$@"; else oracle "$@"; fi; }

echo
echo "== real fixture =="
# shellcheck disable=SC2086
"$dumper" "$fixture" ${DUMP_ARGS:-} || { echo "FAIL: dumper self-check"; exit 1; }
out="$(oracle "$fixture")"; code=$?
echo "oracle: $out (exit $code)"
if [ "$code" != 0 ] || ! grep -q '"o1":"pass"' <<<"$out"; then
  echo "FAIL: the real fixture does not pass O1"
  status=1
fi
if ! grep -q '"tier":[1-9]' <<<"$out"; then
  echo "FAIL: the real fixture has an empty tier (nothing was shed)"
  status=1
fi

echo
echo "== failure fixture (capacity failure) =="
"$dumper" "$fail_fixture" --forced-older 128 || { echo "FAIL: dumper (failure fixture)"; status=1; }
fout="$(oracle "$fail_fixture")"; fcode=$?
echo "oracle: $fout (exit $fcode)"
if [ "$fcode" != 0 ] || ! grep -q '"o1":"skipped"' <<<"$fout" \
   || ! grep -q '"engine":"failure"' <<<"$fout"; then
  echo "FAIL: the failure fixture is not reported as an engine failure"
  status=1
fi

echo
echo "== mutation tests =="
python3 - "$fixture" "$mut_dir" <<'PY'
import copy, json, sys
src, out = sys.argv[1], sys.argv[2]
fx = json.load(open(src))
manifest = []

def emit(label, mutated, expect, what):
    with open(f"{out}/{label}.json", "w") as f:
        json.dump(mutated, f)
    manifest.append(f"{label}\t{out}/{label}.json\t{expect}\t{what}")

o = fx["outputs"]
nb = fx["geometry"]["out_buckets"]
cap = fx["geometry"]["bucket_capacity"]

emit("control", copy.deepcopy(fx), 0, "unmodified copy (must pass)")

# (a) move one output main record to a different bucket.
m = copy.deepcopy(fx)
rec = m["outputs"]["main"][0]
new_b = (rec["bucket"] + 1) % nb
used = {r["lane"] for r in m["outputs"]["main"] if r["bucket"] == new_b}
rec["lane"] = min(set(range(cap)) - used)
old_b = rec["bucket"]; rec["bucket"] = new_b
emit("a_move_main", m, 1, f"move main record {rec['key']} from bucket {old_b} to {new_b}")

# (b) delete one output tier record (else one main record).
m = copy.deepcopy(fx)
which = "tier" if m["outputs"]["tier"] else "main"
gone = m["outputs"][which].pop(0)
emit("b_delete", m, 1, f"delete {which} record {gone['key']}")

# (c) replace a winner's value by the losing A version, for a key in A and B.
def index(recs):
    return {r["key"]: r for r in recs}
a = index(fx["inputs"]["A_main"] + fx["inputs"]["A_tier"])
b = index(fx["inputs"]["B_main"] + fx["inputs"]["B_tier"])
m = copy.deepcopy(fx)
both = [k for k in b if k in a]
outs = index(m["outputs"]["main"] + m["outputs"]["tier"])
if both:
    k = both[0]
    outs[k]["value"] = a[k]["value"]
    outs[k]["tombstone"] = a[k]["tombstone"]
    what = f"winner {k} replaced by its losing A version"
else:
    r = m["outputs"]["main"][0]
    v = bytearray.fromhex(r["value"]); v[1] ^= 1; r["value"] = v.hex()
    what = "flipped a value byte (no key in both A and B)"
emit("c_loser_value", m, 1, what)

# Extras: each is a different clause of the spec.
def free_lane(recs, bucket):
    used = {r["lane"] for r in recs if r["bucket"] == bucket}
    return min(set(range(cap)) - used)

m = copy.deepcopy(fx)
r = m["outputs"]["main"][-1]
r["tombstone"] = not r["tombstone"]
emit("d_flip_tombstone", m, 1, f"flip tombstone flag of {r['key']}")

m = copy.deepcopy(fx)
w = m["words"][0]
w["word"] = "%016x" % (int(w["word"], 16) ^ 1)
emit("e_word_home", m, 1, f"flip bit 0 of the word of key {w['key']} (moves its home)")

m = copy.deepcopy(fx)
main = m["outputs"]["main"]
r = main[-1]
main.append(dict(r, lane=free_lane(main, r["bucket"])))
emit("f_duplicate", m, 1, f"output key {r['key']} stored twice in its home bucket")

m = copy.deepcopy(fx)
r = m["inputs"]["B_main"][0]
m["inputs"]["B_main"].append(dict(r, lane=free_lane(m["inputs"]["B_main"], r["bucket"])))
emit("g_input_dup", m, 1, f"B key {r['key']} repeated in B_main (input structure)")

if fx["outputs"]["tier"]:
    m = copy.deepcopy(fx)
    t = m["outputs"]["tier"].pop(0)
    home = int(next(w["word"] for w in m["words"] if w["key"] == t["key"]), 16) & (nb - 1)
    wrong = (home + 1) % nb
    m["outputs"]["main"].append(dict(t, bucket=wrong, lane=free_lane(m["outputs"]["main"], wrong)))
    emit("h_tier_to_main", m, 1, f"tier record {t['key']} (home {home}) moved into main bucket {wrong}")

open(f"{out}/manifest.tsv", "w").write("\n".join(manifest) + "\n")

# A truncated file must be malformed input, not a verdict.
text = open(src).read()
open(f"{out}/truncated.json", "w").write(text[: len(text) // 2])
with open(f"{out}/manifest.tsv", "a") as f:
    f.write(f"truncated\t{out}/truncated.json\t2\tfile cut in half (malformed, exit 2)\n")
PY

pass=0; bad=0
printf '%-18s %-9s %-9s %s\n' "mutation" "expected" "got" "detail"
while IFS=$'\t' read -r label file expect what; do
  [ -z "$label" ] && continue
  mout="$(oracle_fast "$file" 2>/dev/null)"; mcode=$?
  ok=yes
  [ "$mcode" = "$expect" ] || ok=no
  if [ "$ok" = yes ]; then pass=$((pass+1)); else bad=$((bad+1)); status=1; fi
  printf '%-18s %-9s %-9s %s\n' "$label" "exit $expect" "exit $mcode" "$what [$( [ "$ok" = yes ] && echo ok || echo WRONG )]"
  if [ "$ok" = no ] || [ -n "${VERBOSE:-}" ]; then echo "    $mout" | cut -c1-300; fi
done < "$mut_dir/manifest.tsv"

echo
echo "== summary =="
echo "real fixture: $out"
echo "failure fixture: $fout" | cut -c1-200
echo "mutations as expected: $pass, wrong: $bad"
if [ "$status" = 0 ]; then echo "ROUNDTRIP OK"; else echo "ROUNDTRIP FAILED"; fi
exit "$status"
