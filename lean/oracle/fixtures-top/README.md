# Top-finish fixtures

These are the source files for the 1000-fixture top-finish battery described
in `RebuildBound/Spec/Model/ENGINE_TOP.md` (format `top-finish-fixture/0`,
checked by the Lean oracle's default mode, model `RebuildBound.Model.topJob`,
`RebuildBound/Oracle/TopDiff.lean`). `fdtop.cpp` drives the real top
`LevelMergeJob`. `model_top.py` is an independent Python model of the engine
semantics (written from the ENGINE_*.md extraction); it imports no engine code. No source from
the ignored `.lake/oracle/` cache is required.

| file | role |
| --- | --- |
| `fdtop.cpp` | the dumper: one top job per run (preparation, then the finish over constructed B inputs), writes the fixture |
| `build_fdtop.sh` | compiles it into the work directory (`fdtop`, or `fdtop_assert` with `--asserts`) |
| `gen_top.py` | the battery: a seeded scenario list (families x geometries x seeds), kept in attempt order until 1000 fixtures |
| `model_top.py` | the Python model |
| `run_top.py` | compares `model_top.py` with every fixture; prints the breakdown and writes `summary.json` beside the fixtures |
| `report_check.py` | checks REPORT's top-resolution proposition against the engine output on every premise-satisfying fixture |

The commands below start at the repository root. After setting `top` and
`ORACLE_TOP_WORK`, they also work from any other directory. The default work
directory, when the variable is omitted, is
`lean/.lake/oracle/fixtures-top` (gitignored).
Requirements: Python 3, a C++17 compiler (`/usr/bin/c++`, override with
`CXX`), an x86 host with the AVX-512 features the engine requires, and for
the Lean check the repository's Lean toolchain.

```bash
top="$PWD/lean/oracle/fixtures-top"
export ORACLE_TOP_WORK="$PWD/lean/.lake/oracle/fixtures-top"

"$top/build_fdtop.sh"                     # -> $ORACLE_TOP_WORK/fdtop
"$top/build_fdtop.sh" --asserts           # -> $ORACLE_TOP_WORK/fdtop_assert
python3 -B "$top/gen_top.py"              # -> $ORACLE_TOP_WORK/fx (seed 20261001)
#   kept 1000 fixtures, 117 preparation failures skipped, of 1152 attempts
python3 -B "$top/gen_top.py" --out "$ORACLE_TOP_WORK/fx-assert" \
  --exe "$ORACLE_TOP_WORK/fdtop_assert"
diff -rq -x manifest.json -x summary.json "$ORACLE_TOP_WORK/fx" "$ORACLE_TOP_WORK/fx-assert"   # no output
python3 -B "$top/run_top.py"              # model == engine: 1000, exit 0 iff all agree
python3 -B "$top/report_check.py"         # agree: 823, disagree: 0, excluded: 177
"$top/../check_fixtures.sh" "$ORACLE_TOP_WORK/fx"
"$top/../top_mutations.sh" "$ORACLE_TOP_WORK/fx/f0005_rleaf_g7.json"
```

To compare with an existing battery `OLD`, compare the fixtures byte for
byte: `diff -rq -x manifest.json -x summary.json OLD "$ORACLE_TOP_WORK/fx"`.
`manifest.json` records each attempt's dumper summary line, which contains
the output path, so it differs between two output directories in that path
only.

`fdtop` exits 0 (success or a capacity failure of the finish: both are
fixtures), 3 (the preparation itself failed: skipped, nothing written) or 2
(harness error). The scenarios are drawn from the seed before any run, so the
battery does not depend on the worker count (`--jobs`, default 24).
Generation takes about a second, the Lean check about 15 s.
`top_mutations.sh` without an argument takes its fixture from
`$ORACLE_TOP_WORK/fx/`.

Expected: 1000 fixtures, 772 engine successes and 228 capacity failures; the
Lean oracle reports O2 pass for all 1000, O3 pass on the 772 successes,
failing-test kind `match` on the 228 failures, O1 pass on 601 and `premise`
on the 171 successes whose inputs break `TopShape` on purpose, no
mismatching fixture; the nine top mutations are rejected.
