# Radix (general-digit) merge fixtures

These are the source files for the 8592-fixture battery of the
separated-sources ordinary merge at digits 2-8 described in
`RebuildBound/Spec/Model/ENGINE_RADIX.md` (format `rebuild-fixture/0`,
checked by the Lean oracle's `--sep` mode, `RebuildBound/Oracle/SepDiff.lean`).
`fd3.cpp` drives the real level-arena merge job at any branching, level and
digit. `model3.py` is an independent Python model of the engine semantics
(written from the ENGINE_*.md extraction); it imports no engine code. No source from the ignored
`.lake/oracle/` cache is required.

| file | role |
| --- | --- |
| `fd3.cpp` | the dumper: one job per run, knobs on the command line, C++ self-check, writes the fixture |
| `build_fd3.sh` | compiles it into the work directory (`fd3`, or `fd3_assert` with `--asserts`) |
| `gen.py` | the battery: 18 configurations x 500 seeded knob sets, each run through `fd3` and compared with `model3.py`; writes `results.json` |
| `model3.py` | the Python model (`model3.py F.json...` also works standalone) |
| `stats.py` | per-digit match counts, failure kinds and path coverage from `results.json` |
| `cmp_radix.py` | compares two batteries: `results.json` job by job and every fixture byte for byte |

The commands below start at the repository root. After setting `rx` and
`ORACLE_RADIX_WORK`, they also work from any other directory. The default
work directory, when the variable is omitted, is
`lean/.lake/oracle/fixtures-radix` (gitignored).
Requirements: Python 3, a C++17 compiler (`/usr/bin/c++`, override with
`CXX`), an x86 host with the AVX-512 features the engine requires, and for
the Lean check the repository's Lean toolchain. The kept battery takes about
4.7 GB.

```bash
rx="$PWD/lean/oracle/fixtures-radix"
export ORACLE_RADIX_WORK="$PWD/lean/.lake/oracle/fixtures-radix"

"$rx/build_fd3.sh"                        # -> $ORACLE_RADIX_WORK/fd3
python3 -B "$rx/gen.py" "$ORACLE_RADIX_WORK/battery" 500 --keep --jobs 24
#   per configuration: run / match / harness_skip / success / failure kinds;
#   TOTAL {'run': 8592, 'ok': 8592, 'skip': 408, 'bad': 0}; exit 1 on a mismatch
python3 -B "$rx/stats.py" "$ORACLE_RADIX_WORK/battery/results.json"   # optional
python3 -B "$rx/cmp_radix.py" OLD_BATTERY "$ORACLE_RADIX_WORK/battery" # optional
ORACLE_ARGS=--sep "$rx/../check_fixtures.sh" "$ORACLE_RADIX_WORK/battery"
```

`gen.py` writes `battery/<label>/<idx>.json` and `battery/results.json`;
`check_fixtures.sh` skips `results.json`. Without `--keep` a matching fixture
with index 2 or more is deleted after the Python comparison; the Lean check
needs `--keep`. The knob sets are seeded
by label and index (`random.Random(f'{label}/{idx}')`), so the battery does
not depend on the worker count. All 9000 knob sets are attempted. Under the
current two-block CBC routing, 408 fail the fixture's B-carry contract before
the merge job starts: 401 report `the fixture's carry shed while routing` and
7 report `the fixture's carry route overflowed` (exit 2). These input-construction
refusals remain in `results.json` and produce no fixture; they are not counted
as Lean comparisons. Earlier routing used different fixture/refusal counts.
Generation with the Python model takes several minutes; the Lean check a few
minutes.

Expected: 8592 fixtures, containing 3902 engine successes and 4690 capacity
failures, plus the 408 construction refusals above. The Python model must match
every produced fixture. The Lean oracle must report O2 pass for all 8592, O1
and O3 pass on every engine success, failing-test kind `match` on every capacity
failure, and no mismatching fixture.
