# d = 2 merge fixtures

These are the source files for the 1964-knob-set d = 2 battery described in
`RebuildBound/Spec/Model/ENGINE_D2.md` (format `rebuild-fixture/0`, checked by
the Lean oracle's default mode, model `RebuildBound.Model.job`). `fd2.cpp`
drives the real level-arena merge job; it is the round-trip dumper
`../fixture_dump.cpp` with extra knobs. `model.py` is an independent Python
model of the engine semantics (written from the ENGINE_*.md extraction); it
imports no engine code. No source from the ignored `.lake/oracle/` cache is required.

| file | role |
| --- | --- |
| `fd2.cpp` | the dumper: one job per run, knobs on the command line, C++ self-check, writes the fixture |
| `build_fd2.sh` | compiles it into the work directory (`fd2`, or `fd2_assert` with `--asserts`) |
| `regen_d2.py` | the battery: decodes each fixture's knobs from its name and runs `fd2` |
| `names.txt` | the battery's irregular names (96 `fx`, 166 `fy/g_`); the 1536 `fy/f_` names are a grid in `regen_d2.py` |
| `model.py` | the Python model: `model.py F.json...` prints the lane-exact comparison, exit 0 iff all agree |
| `cmp_d2.py` | compares two batteries name by name and byte for byte |

The commands below start at the repository root. After setting `d2` and
`ORACLE_D2_WORK`, they also work from any other directory. The default work
directory, when the variable is omitted, is
`lean/.lake/oracle/fixtures-d2` (gitignored).
Requirements: Python 3, a C++17 compiler (`/usr/bin/c++`, override with
`CXX`), an x86 host with the AVX-512 features the engine requires, and for
the Lean check the repository's Lean toolchain.

```bash
d2="$PWD/lean/oracle/fixtures-d2"
export ORACLE_D2_WORK="$PWD/lean/.lake/oracle/fixtures-d2"

"$d2/build_fd2.sh"                       # -> $ORACLE_D2_WORK/fd2
python3 -B "$d2/regen_d2.py" "$ORACLE_D2_WORK/battery"
#   1949 fixtures, 15 exact known carry-construction refusals; any deviation exits 1
python3 -B "$d2/test_regen_d2.py"          # inventory/refusal and subset regressions
python3 -B "$d2/cmp_d2.py" OLD_BATTERY "$ORACLE_D2_WORK/battery"   # optional
find "$ORACLE_D2_WORK/battery" -name '[fg]_*.json' -print0 \
  | xargs -0 -P 32 -n 50 python3 -B "$d2/model.py" > /dev/null    # exit 0 iff all agree
"$d2/../check_fixtures.sh" "$ORACLE_D2_WORK/battery"
```

`regen_d2.py` writes `battery/fx/`, `battery/fy/` and `battery/manifest.json`
(every run's arguments and exit status); `check_fixtures.sh` skips the
manifest. `regen_d2.py --from DIR` regenerates the names of an existing
battery instead of the canonical list. The dumper exits 0 (self-check passed;
an engine capacity failure is a legitimate `failure` fixture), 1 (self-check
violation; the fixture is still written) or 2 (harness error). The manifest
retains every status and diagnostic and marks `expected_refusal` explicitly.
The 15 names in `EXPECTED_CARRY_REFUSALS` must exit 2 with exactly the carry-shed
diagnostic: their forced keys and seeded filler no longer form a valid incoming
B main under two-block CBC routing. This refusal happens while constructing the
input, before the merge job starts, and produces no fixture. An unexpected
refusal, a missing result, a changed known disposition (including success), or
a stale output for a refused name makes generation fail. `--from` and subsets
validate only the names selected for that invocation. Generation
takes about a second on 24 workers, the Lean check about 25 s.

Expected: all 1964 knob sets attempted, 1949 fixtures produced and 15 known
input-construction refusals. The produced fixtures contain 1132 engine successes
and 817 capacity failures. The Lean oracle must report O2 pass for all 1949,
O1 (engine and model output) and O3 pass on the 1132 successes, failing-test kind
`match` on the 817 failures, and no mismatching fixture. The 15 refused inputs
are recorded separately; they are not counted as Lean comparisons.

The fixture names encode the knobs (`decode` in `regen_d2.py`): `fx/f_SEED_OLDER_FRESH`
(`--seed --forced-older --forced-fresh`), `fy/f_SEED_A_OLDER_BFA_BF_AF`
(`--seed --a-per-bucket --forced-older --btier-from-atier --btier-forced
--atier-forced`), `fy/g_SEED_OLDERLIST_FRESHLIST_BFA` (`--seed --older-list
--fresh-list --btier-from-atier`); the suffix `--tombs` adds `--tombs`.
