# Deamortization model

These scripts compute the paper's deamortization costs for B = 2, 4 and 8.
They find the rebuild speed each non-top level needs to avoid stalls and the
average number of tables a lookup searches. Their results appear in the
comparison table "Costs of deamortization" and in the online appendix "Rebuild
Speed and Tables per Lookup". The model is a logical schedule of merges and
storage regions, not a simulation of the engine's threads. The Python scripts
need only the standard library; the figure also needs numpy and matplotlib.

| File | Purpose |
|---|---|
| `deamortization_analysis.py` | Table averages and the figure of tables per lookup against rebuild speed, under the three-region layout |
| `arena_coupling/hier.py` | Hierarchy simulator: each level's merges, coupled through carry arrivals and waits for free regions |
| `arena_coupling/layout_speeds.py` | Minimum speeds and per-level table averages under the paper's layout; `--check` reproduces the model without the storage limit |
| `arena_coupling/layout_extra.py` | Convergence in depth at B = 8, and per-digit shares of work after a carry arrives |
| `deamortization_late_share.py` | Minimum speed when a share of each merge follows its carry's arrival, without the storage limit |
| `deamortization_closed_form.py` | Closed forms for the model without the storage limit |
| `check_deamortization_closed_form.py` | Checks the closed forms against exact recurrences and the event simulator |
| `arena_coupling/run_*.py`, `peak.py`, `timeline.py` | Earlier comparisons of storage policies and adoption rules |
| `arena_coupling/share.cpp`, `share2.cpp` | Use the engine's planners to count the share of each merge's bucket accesses that follows its carry's arrival |

## Running

Every script can be run from any directory. Run times are from a laptop.

```sh
python analysis/deamortization/deamortization_analysis.py --summary-only  # ~15 s
python analysis/deamortization/deamortization_analysis.py -o deamortized_probe_tradeoff.pdf
python analysis/deamortization/arena_coupling/layout_speeds.py            # ~45 s
python analysis/deamortization/check_deamortization_closed_form.py
```

The summary prints one row per B:

| B | Minimum speed | Tables per level | Probe overhead | Tables per lookup |
|---|---|---|---|---|
| 2 | 1.0 | 1.500 | 3.000 | 1.5 log N |
| 4 | 2.5625 | 1.549 | 1.549 | 0.77 log N |
| 8 | 5.2748 | 1.399 | 0.933 | 0.47 log N |

Probe overhead is relative to the amortized binary hierarchy, which searches
0.5 log N tables on average, so tables per lookup is the overhead times
0.5 log N.

`share.cpp` and `share2.cpp` include engine headers relative to the
repository root and are not part of the CMake build. Compile them from the
repository root with the library's compiler and ISA, for example
`g++ -std=c++17 -O2 -march=native -I. analysis/deamortization/arena_coupling/share2.cpp`.
The arguments are `[log2 N] [owner threads] [B]` (`share.cpp` fixes B = 8).
