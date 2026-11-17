#!/usr/bin/env bash
# Mutation tests of the top-finish oracle (TopDiff.lean): every mutated copy of
# a successful top fixture must be rejected (exit 1), and the unmodified copy
# must pass (exit 0).
#
#   oracle/top_mutations.sh [<fixture.json>]
#
# The default fixture is the first successful one under
# $ORACLE_TOP_WORK/fx/ (default .lake/oracle/fixtures-top/fx/, the generator's
# output) that has a two-page tier and records on its
# second page. The mutations move output records to invalid or wrong
# coordinates (lane 64, a page past the tier, a doubly occupied position, two
# swapped tier records), corrupt an output value, drop a tier record, and move
# input R and B-tier records outside their pages.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean="$(cd "$here/.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
(cd "$lean" && lake build oracle >/dev/null)
bin="$lean/.lake/build/bin/oracle"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

python3 - "$lean" "$tmp" "${1:-}" <<'PY'
import copy, glob, json, os, sys
lean, tmp, given = sys.argv[1], sys.argv[2], sys.argv[3]

def ok(f):
    o = f['outputs']
    return (o['verdict'] == 'success' and f['geometry']['out_tier_pages'] >= 2
            and any(r['page'] == 1 for r in o['tier']) and len(o['tier']) >= 2
            and f['inputs']['R'] and f['inputs']['B_tier'])

if given:
    src = json.load(open(given))
    if not ok(src):
        sys.exit(f'{given}: need a success with a second tier page, R and a B tier')
else:
    work = os.environ.get('ORACLE_TOP_WORK', os.path.join(lean, '.lake/oracle/fixtures-top'))
    files = sorted(glob.glob(os.path.join(work, 'fx/f*.json')))
    src = next((f for f in map(lambda p: json.load(open(p)), files) if ok(f)), None)
    if src is None:
        sys.exit('no suitable top fixture found; pass one explicitly')

def write(name, fn):
    f = copy.deepcopy(src)
    fn(f)
    json.dump(f, open(os.path.join(tmp, name + '.json'), 'w'))

def first_page1(f):
    return next(r for r in f['outputs']['tier'] if r['page'] == 1)

def alias(f):              # (1, 0)-style record moved to (0, 64): same flattened index
    r = first_page1(f); r['page'] -= 1; r['lane'] += f['geometry']['bucket_capacity']
def tier_page_out(f):
    f['outputs']['tier'][-1]['page'] = f['geometry']['out_tier_pages']
def tier_dup(f):
    t = f['outputs']['tier']; t[1]['page'], t[1]['lane'] = t[0]['page'], t[0]['lane']
def tier_swap(f):
    t = f['outputs']['tier']
    (t[0]['page'], t[0]['lane']), (t[1]['page'], t[1]['lane']) = \
        (t[1]['page'], t[1]['lane']), (t[0]['page'], t[0]['lane'])
def tier_drop(f):
    f['outputs']['tier'].pop()
def main_lane_out(f):
    f['outputs']['main'][0]['lane'] = f['geometry']['bucket_capacity']
def main_value(f):
    r = f['outputs']['main'][0]; r['value'] = ('0' if r['value'][0] != '0' else '1') + r['value'][1:]
def input_r_lane(f):
    f['inputs']['R'][0]['lane'] = f['geometry']['bucket_capacity']
def input_btier_page(f):
    f['inputs']['B_tier'][0]['page'] = f['geometry']['b_tier_pages']

for name, fn in [('alias', alias), ('tier_page_out', tier_page_out), ('tier_dup', tier_dup),
                 ('tier_swap', tier_swap), ('tier_drop', tier_drop),
                 ('main_lane_out', main_lane_out), ('main_value', main_value),
                 ('input_r_lane', input_r_lane), ('input_btier_page', input_btier_page)]:
    write('mut_' + name, fn)
write('control', lambda f: None)
PY

n=0; rejected=0
for f in "$tmp"/mut_*.json; do
  n=$((n + 1))
  if "$bin" "$f" >/dev/null 2>&1; then
    echo "NOT REJECTED: $(basename "$f" .json)"
  else
    rejected=$((rejected + 1))
  fi
done
control=yes
"$bin" "$tmp/control.json" >/dev/null 2>&1 || control=no
echo "top mutations rejected: $rejected/$n, control passes: $control"
if [ "$rejected" -eq "$n" ] && [ "$control" = yes ]; then
  echo "TOP MUTATIONS OK"
else
  echo "TOP MUTATIONS FAILED"; exit 1
fi
