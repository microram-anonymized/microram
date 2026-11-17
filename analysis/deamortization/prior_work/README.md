# Prior deamortization schemes

These scripts check the costs of prior deamortization schemes that the paper
compares against: the two-version schedule of Ostrovsky and Shoup, the fixed
per-level arenas with Goldreich and Ostrovsky's rehash, Goodrich et al.'s
tables plus history, and PD-ORAM. They were copied from the paper
repository's `GO96-analysis/`, where `report.tex` derives the numbers. The
scripts need only the Python standard library. `simulate.py` imports
`deamortization_closed_form.py` from the parent directory.

| File | Purpose |
|---|---|
| `simulate.py` | Discrete-event model of the binary two-buffer and 2.5-buffer schedules and of the B-ary streamable schedule |
| `check_prior_work.py` | Checks the scheduling and reserved record slots of the prior schemes (exact cyclic sweeps for L = 2..14 and an event simulation) |
| `check_closed_form.py` | Checks the B-ary closed forms against both event simulators: `simulate.py` and `../deamortization_analysis.py` |

## Running

```sh
python analysis/deamortization/prior_work/check_prior_work.py     # ~4 s
python analysis/deamortization/prior_work/check_closed_form.py    # ~2 s
python analysis/deamortization/prior_work/simulate.py --branching
python analysis/deamortization/prior_work/simulate.py --probe-curve
```

`check_prior_work.py` prints:

```
Exact cyclic sweeps: L=2..14 passed
Ostrovsky-Shoup, event simulation L=8: average=6.66666666667, peak=9
Ostrovsky-Shoup, alpha=0: 5.99 stalls; 6 and 6.01 pass
Fixed per-level hash-rebuild arenas: 3 times baseline
Goodrich tables plus history, expansion->2: 11/4 times baseline, 11N record slots
PD-ORAM L=14: storage witness=2.499954222, average=21, peak=28
PD-ORAM deadline compression: (C(2m)/m)/(C(2m)/(2m)) = 2
```
