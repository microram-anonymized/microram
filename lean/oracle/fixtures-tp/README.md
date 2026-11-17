# Top-preparation and initialization fixtures

These are the source files for the 2519-fixture comparison described in
`RebuildBound/Spec/Model/ENGINE_TOPPREP.md`. `fdtp.cpp` drives the real job;
`fdtp_engine.cpp` drives public `LevelArenaEngine::Initialize`. The Python
model imports no engine implementation. Every source needed is in this
directory.

The commands below start at the repository root. After setting `tp` and
`ORACLE_TP_WORK`, they also work from any other directory. The default work
directory, when the variable is omitted, is
`lean/.lake/oracle/fixtures-tp`. Use a fresh
work directory when regenerating to avoid retaining stale fixture files.
All binaries, fixtures, manifests, and reports go in the work directory;
the scripts do not write Python bytecode beside these sources.

Requirements: Python 3, a C++17 compiler (defaults to `/usr/bin/c++`, override
with `CXX`), and an x86 host with the AVX-512 features required by the engine.
Builds use `-march=native`, the current engine headers, and the checked-in
engine test support header. Lean checks additionally need the repository's
Lean toolchain and dependencies.

```bash
tp="$PWD/lean/oracle/fixtures-tp"
export ORACLE_TP_WORK="$PWD/lean/.lake/oracle/fixtures-tp"

"$tp/build_fdtp.sh"
"$tp/build_fdtp_engine.sh"
"$tp/build_fdtp.sh" --asserts
"$tp/build_fdtp_engine.sh" --asserts

python3 "$tp/gen_tp.py" --n-prep 1600 --n-init 800 --seed 20261002
python3 "$tp/gen_engine_tp.py"
python3 "$tp/gen_tp.py" --n-prep 1600 --n-init 800 --seed 20261002 \
  --out "$ORACLE_TP_WORK/fx-assert" --exe "$ORACLE_TP_WORK/fdtp_assert"
python3 "$tp/gen_engine_tp.py" "$ORACLE_TP_WORK/fx-engine-assert" \
  "$ORACLE_TP_WORK/fdtp_engine_assert"

python3 "$tp/run_tp.py" --engine-dir "$ORACLE_TP_WORK/fx-engine" \
  --assert-dir "$ORACLE_TP_WORK/fx-assert" \
  --engine-assert-dir "$ORACLE_TP_WORK/fx-engine-assert"
python3 "$tp/report_check_tp.py"
python3 "$tp/mutate_tp.py"
```

The canonical job battery attempts 1600 preparations and 800 initializations.
One preparation, `p0679_hotmany_T16.json`, is intentionally beyond the dumper's
input capacity (`A main overfull`); its refusal is recorded in `manifest.json`,
and no fixture is written for it. Thus `fx` and `fx-assert` each contain 2399
fixtures. Each public-engine directory contains 120 fixtures. The generator
prints every harness error; this one expected refusal is not an engine
capacity-failure fixture. Check its identity and the full counts explicitly:

```bash
python3 - <<'PY'
import json, os
from pathlib import Path
work = Path(os.environ['ORACLE_TP_WORK'])
for name in ('fx', 'fx-assert'):
    directory = work / name
    manifest = json.loads((directory / 'manifest.json').read_text())
    rejected = [a for a in manifest['attempts'] if a['status'] != 0]
    assert manifest['seed'] == 20261002 and manifest['n'] == 2400
    assert len(rejected) == manifest['harness_errors'] == 1
    assert rejected[0]['file'] == 'p0679_hotmany_T16.json'
    assert rejected[0]['status'] == 2 and 'A main overfull' in rejected[0]['error']
    assert len(list(directory.glob('p*.json'))) == 1599
    assert len(list(directory.glob('i*.json'))) == 800
for name in ('fx-engine', 'fx-engine-assert'):
    assert len(list((work / name).glob('e*.json'))) == 120
print('Generation counts and the expected refusal match.')
PY
```

`run_tp.py` writes `RESULTS.txt` and `fx/summary.json`. It requires all 2519
model comparisons and both assertion-build byte comparisons to pass, and
rejects empty requested directories. `report_check_tp.py` checks the report's
packing and first-failure witnesses over the 2399 job fixtures and writes
`REPORT_CHECK.txt`. `mutate_tp.py` writes `MUTATIONS.txt` and requires a passing
baseline and at least one rejected fixture for each of its 13 mutations.
These checkers exit nonzero on failures. The public-engine generator also
exits nonzero for any harness error; the job generator records all harness
errors in its manifest, which the count check above validates.

Run the independent Lean model against the regenerated fixtures:

```bash
ORACLE_JOBS=16 ORACLE_ARGS=--tp "$tp/../check_fixtures.sh" \
  "$ORACLE_TP_WORK/fx" "$ORACLE_TP_WORK/fx-engine"
```

The build scripts always rebuild. Job generation supports `--jobs` (default
48); the model comparison also supports `--jobs` (default 48). Public-engine
generation uses 16 workers. The fixture contents and scenario seed do not
depend on the worker count or the current directory.
