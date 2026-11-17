#!/usr/bin/env python3
"""Generate the SelRange3 certificate tables, kernel checks and per-shape theorems.

SelRange3 (`Spec/Selected.lean`): every `r = 3` shape of `selBudgets` meets its
range budget. The range term is

    selRange g = D 2^t Σ_{a<3} stopLoss(rangeLawR 64 32 P 2^I t 3 (qMass 64 k 3 a)) 64

with `t = k - I`, `P = earlyCap`. The class masses are `qc / 2^nb`, `nb = 64 - k`,
with `qc ∈ {2^nb / 3 + 1, 2^nb / 3}` (NCA5's `qCount_eq`): two class laws per
shape. Each class law is certified as in NCA5 (`Glue.lean`, `class_bound`):

* `TabT<t>K<k><X>th`  the depth-`t` tree law of NCA1 (`Tab<t>.lean`, parsed, not
                      regenerated) thinned by `q = qc / 2^nb` (`checkThin`, at `q`
                      in lowest terms `qcT / 2^nbT`): exact, rounded up once to
                      scale `2^320`;
* `TabT<t>K<k><X>s<n>` partial sum `n = 2, 3` of the radix node (`checkConv`),
                      rounded up to `2^320` after every product;
* the final check: NCA1's `checkFinal` on the one-row table `[rootMarg 64 S_3]`
  at `P`, `g = 2^I`, early probability `qc / 2^(nb + t)`, NCA1's truncation term
  off; P10r's term is bounded by `2^I / 10^46` in `Glue.lean`.

The thinned table and the partial sums depend only on the chain key
`(t, q in lowest terms, r, H)` (`chain_key`). Classes with equal keys (e.g.
`T7K16A`: `93824992236886 / 2^48`, `T7K17A`: `46912496118443 / 2^47`) share one
chain: its tables and its thinning and partial-sum checks are generated once,
named after the first class (in configuration order) with that key, and the
other classes refer to them; every class keeps its own final check.
`DirectJobANumerics/gen.py` reuses this plan (`plan`) to refer to these chains.

The per-shape arithmetic (`selRange_le`): the old-map density
`D ≤ 2^m / (2^m - n (num - 2^m))` (SelRange1's `density_le`; `D = 1` at `d = 3`)
and `2^m 2^t (3 (tn 10^46 + 2^I td)) bd ≤ bn (2^m - n (num - 2^m)) (td 10^46)`
for the budget `bn / bd`.

The kernel checks are dealt round-robin (by class law) into `LANES` modules
`Lane<j>.lean` whose checks run one after the other (`Elab.async` off), so that
neither `lake build` nor `leanchecker` (which replays modules in parallel and
the declarations of one module in sequence) runs more than `LANES` of them at
once (a thinning check takes about 17 GB).

No floating point enters a table or a check. Usage: `python3 gen.py`
(`--dry` to compute and print without writing).
"""
import importlib.util
import math
import multiprocessing as mp
import re
import sys
import time
from fractions import Fraction as Q
from pathlib import Path

sys.set_int_max_str_digits(0)
sys.dont_write_bytecode = True  # keep the other packages' directories clean
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]          # .../lean
NCA1_DIR = HERE.parent / 'NCA1'
NCA5_DIR = HERE.parent / 'NCA5'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


nca5 = load('nca5gen', NCA5_DIR / 'gen.py')   # thin, conv, root_marg (and NCA1's gen as nca5.G1)
nca1 = nca5.G1

C, H, L = 64, 256, 64
PREC = 320
D = 1 << PREC
assert nca1.D == D and nca5.D == D and nca1.H == H and nca5.H == H and nca5.C == C
NTAYLOR, RRED = nca1.NTAYLOR, nca1.RRED
LAM_A, LAM_B = 32, 1
W = 64                  # word width
R = 3                   # the radix
SIGDIG = 5              # significant digits of the stop-loss targets
EPS_EXP = 46            # P10r's term is at most 2^I / 10^EPS_EXP
LANES = 4
PKG = 'RebuildBound.Proofs.SelRange3'
CHECKER = 'RebuildBound.Proofs.NCA5.Checker'


# --- shapes and budgets, from Spec/Selected.lean -----------------------------------
def parse_budgets():
    src = (ROOT / 'RebuildBound/Spec/Selected.lean').read_text()
    block = src[src.index('def selBudgets'):]
    block = block[:block.index(')]') + 2]
    pat = re.compile(
        r'-- (?P<name>L\d d\d \((?:uniform|half)\))[^\n]*\n\s*'
        r'\((?P<geom>\{[^}]*\}),\s*\n\s*(?P<bn>\d+) / 10 \^ (?P<be>\d+), (?P<rn>\d+) / 10 \^ (?P<re>\d+)\)')
    out = []
    for mt in pat.finditer(block):
        fields = dict((k.strip(), int(v)) for k, v in
                      (f.split(':=') for f in mt['geom'].strip('{} ').split(',')))
        out.append(dict(name=mt['name'], geom=mt['geom'], g=fields,
                        bn=int(mt['bn']), be=int(mt['be'])))
    assert len(out) == 34, len(out)
    return out


def val2(n):
    e = 0
    while n != 0 and n % 2 == 0:
        n //= 2
        e += 1
    return e


def shape_params(s):
    g = s['g']
    k = g['K'] + g['e']
    t = k - g['I']
    P = g['aTierPages'] * g['C'] + g['I'] * (g['stashPages'] * g['C'])
    d = g['r'] * 2 ** g['e']
    Dm1 = d - 1
    e2 = val2(Dm1)
    r2 = Dm1 // 2 ** e2
    m = W - (g['K'] + e2)
    num = r2 * ((2 ** m + r2 - 1) // r2)
    n = 32 * (Dm1 * 2 ** g['K'])
    nb = W - k
    return dict(k=k, t=t, I=g['I'], P=P, m=m, num=num, n=n, nb=nb,
                qcA=2 ** nb // R + 1, qcB=2 ** nb // R)


def cfg_id(cfg):
    t, k, P, I = cfg
    return f'T{t}K{k}'


def reduce_mass(qc, nb):
    """`qc / 2^nb` in lowest terms."""
    while nb > 0 and qc % 2 == 0:
        qc //= 2
        nb -= 1
    return qc, nb


def chain_key(t, qc, nb, r):
    """What the thinned table and the partial sums depend on: the NCA1 depth-`t`
    table, the mass in lowest terms, the radix (number of partial sums) and the
    cutoff `H` (`C` and the scale `2^PREC` are fixed)."""
    qcT, nbT = reduce_mass(qc, nb)
    return (t, qcT, nbT, r, H)


def plan(budgets):
    """The configurations, the class laws (in order), their lanes, and the chains.

    Returns `(configs, classes, chains)`: `configs` maps a configuration to its
    shapes; `classes` lists `dict(cfg, X, qc, nb, cid, key, lane)` (the lane of the
    class's final check); `chains` maps a chain key to `dict(cid, lane, users)`,
    named after and checked in the lane of its first class."""
    r3 = [s for s in budgets if s['g']['r'] == R]
    assert len(r3) == 10
    configs = {}
    for s in r3:
        sp = shape_params(s)
        s['sp'] = sp
        assert 4 <= sp['t'] <= 9 and s['g']['C'] == 64
        cfg = (sp['t'], sp['k'], sp['P'], sp['I'])
        configs.setdefault(cfg, []).append(s)
    # one depth and mass exponent per configuration
    assert len({(c[0], c[1]) for c in configs}) == len(configs)
    classes, chains = [], {}
    for cfg in sorted(configs):
        sp = configs[cfg][0]['sp']
        for X, qc in (('A', sp['qcA']), ('B', sp['qcB'])):
            j = len(classes)
            cid = cfg_id(cfg) + X
            key = chain_key(cfg[0], qc, sp['nb'], R)
            ch = chains.setdefault(key, dict(cid=cid, lane=j % LANES, users=[]))
            ch['users'].append(cid)
            classes.append(dict(cfg=cfg, X=X, qc=qc, nb=sp['nb'], cid=cid, key=key,
                                lane=j % LANES))
    return configs, classes, chains


# --- tables -------------------------------------------------------------------------
def read_table(t):
    src = (NCA1_DIR / f'Tab{t}.lean').read_text()
    rows = re.findall(rf'def t{t}_r(\d+) : List Nat := \[([^\]]*)\]', src)
    assert [int(m) for m, _ in rows] == list(range(C + 1))
    return [[int(x) for x in body.split(',')] if body.strip() else [] for _, body in rows]


# --- the final check (NCA1's checkFinal on [rootMarg C S_r], truncation term off) ----
def final_parts(Rm, P, I, ap, dp):
    G = 2 ** I
    cs = Rm + [0] * (H + 1 - len(Rm))
    assert len(cs) == H + 1
    Qv = [D] + cs[1:]
    W2 = sum(cs[j] << j for j in range(1, H + 1))
    wf = 2 * PREC + 8
    Wd = nca1.Width(wf)
    fuel = G.bit_length()
    A = nca1.pow_round(Wd, Qv, fuel, G)
    choose, c = [], 1
    for j in range(H + 1):
        choose.append(c)
        c = c * max(P - j, 0) // (j + 1)
    # ℕ subtraction, as in `binomRow`: `(d - a)^(P - j)` with `P - j = 0` for `j ≥ P`
    bl = [nca1.cdiv(D * c * ap ** j * (dp - ap) ** max(P - j, 0), dp ** P)
          for j, c in enumerate(choose)]
    assert sum(bl) * sum(A) < 1 << wf
    cc = nca1.conv_trunc(bl, A, H + 1)
    fin = sum(cc[n] * max(n - L, 0) for n in range(H + 1))
    rr = max(1, nca1.cdiv(G * W2, D))
    assert G * W2 <= D * rr
    um = nca1.umNum(NTAYLOR, rr, G * W2, D)
    tail = nca1.cdiv((H + 1 - L) * (dp + ap) ** P * um, 2 ** (H + 1) * dp ** P)
    return dict(wf=wf, fuel=fuel, rr=rr, fin=fin, tail=tail, total=Q(fin, D * D) + Q(tail, D))


def run_chain(key):
    """One chain: the thinned table (at the mass in lowest terms) and the partial sums."""
    t, qcT, nbT, r, h = key
    assert h == H
    st = time.time()
    F = read_table(t)
    Tb, wT = nca5.thin(F, qcT, 2 ** nbT)
    S, steps = Tb, []
    for n in range(2, r + 1):
        S, w = nca5.conv(S, Tb)
        steps.append((w, S))
    return dict(key=key, qcT=qcT, nbT=nbT, Tb=Tb, wT=wT, steps=steps, secs=time.time() - st)


def run_final(job):
    """The final series of one class law (without target), from its chain's last table."""
    S, P, I, qc, dp = job
    st = time.time()
    fp = final_parts(nca5.root_marg(S), P, I, qc, dp)
    return fp, time.time() - st


# --- emitting Lean ------------------------------------------------------------------
HEADER = '/-! {doc} Generated by `RebuildBound/Proofs/SelRange3/gen.py`; do not edit. -/\n\n'


def emit_table(fname, name, F, doc):
    out = [HEADER.format(doc=doc), 'namespace RebuildBound.SelRange3.Tab\n']
    for m, row in enumerate(F):
        out.append(f'def {name}_r{m} : List Nat := [{", ".join(map(str, row))}]\n')
    out.append(f'def {name} : List (List Nat) :=\n  [{", ".join(f"{name}_r{m}" for m in range(len(F)))}]\n')
    out.append('end RebuildBound.SelRange3.Tab')
    (HERE / f'{fname}.lean').write_text('\n'.join(out) + '\n')


def emit_lane(j, imports, checks):
    """One lane: its kernel checks, in sequence."""
    lines = [''.join(f'import {i}\n' for i in imports),
             HEADER.format(doc=f'Kernel checks, lane {j} of {LANES} (see `SelRange3.lean`, "Lanes").'),
             '-- One kernel check at a time: this module\'s checks run in sequence.',
             'set_option Elab.async false\n',
             'namespace RebuildBound.SelRange3\n']
    for (thm, doc, stmt) in checks:
        lines += [f'/-- {doc} -/', f'theorem {thm} : {stmt} = true := by', '  decide +kernel\n']
    lines.append('end RebuildBound.SelRange3')
    (HERE / f'Lane{j}.lean').write_text('\n'.join(lines) + '\n')


def shape_ident(s):
    lvl, dig, conf = s['name'].replace('(', '').replace(')', '').split()
    return f'{"u" if conf == "uniform" else "h"}{lvl}{dig}'


def chain_checks(ch):
    """The kernel checks of one chain: their imports and (theorem, doc, statement)."""
    t = ch['key'][0]
    cid, qcT, nbT = ch['cid'], ch['qcT'], ch['nbT']
    tab = f'{PKG}.Tab{cid}'
    imports = [f'RebuildBound.Proofs.NCA1.Tab{t}', f'{tab}th'] + \
        [f'{tab}s{n}' for n in range(2, ch['key'][3] + 1)]
    out = [(f'thin_{cid}',
            f'Kernel check of the thinning of NCA1\'s depth-{t} table by `{qcT}/2^{nbT}` '
            f'({", ".join(ch["users"])}).',
            f'NCA5.checkThin {ch["wT"]} {qcT} (2 ^ {nbT}) {C} {H} NCA1.Tab.t{t} Tab.{cid}_th')]
    prev = f'Tab.{cid}_th'
    for n, (w, _) in enumerate(ch['steps'], start=2):
        out.append((f'conv_{cid}_{n}', f'Kernel check of partial sum {n} of the radix node '
                    f'({", ".join(ch["users"])}).',
                    f'NCA5.checkConv {w} (2 ^ {PREC}) {H} {prev} Tab.{cid}_th Tab.{cid}_s{n}'))
        prev = f'Tab.{cid}_s{n}'
    return imports, out


def final_check(res, ch):
    """The final check of one class law: its imports and (theorem, doc, statement)."""
    cfg, qc, cid = res['cfg'], res['qc'], res['cid']
    t, k, P, I = cfg
    nb = W - k
    prev = f'Tab.{ch["cid"]}_s{ch["key"][3]}'
    fp = res['fp']
    out = [(f'final_{cid}',
            f'Kernel check of the stop-loss series from the root-loss marginal ({cid}).',
            f'NCA1.checkFinal {fp["wf"]} (2 ^ {PREC}) {NTAYLOR} {fp["rr"]} {RRED} {H} {L} '
            f'(2 ^ {I}) {P} {qc} (2 ^ {nb + t}) {LAM_A} {LAM_B} 0 {fp["fuel"]} '
            f'{res["tn"]} (10 ^ {res["tde"]}) 0 [NCA5.rootMarg {C} {prev}]')]
    return [f'{PKG}.Tab{ch["cid"]}s{ch["key"][3]}'], out


def emit_config(cfg, results, chains, shapes, tn, tde):
    t, k, P, I = cfg
    nb = W - k
    name = cfg_id(cfg)
    lanes = set()
    for X in 'AB':
        res = results[(cfg, X)]
        lanes |= {res['lane'], chains[res['key']]['lane']}
    imports = [f'{PKG}.Glue'] + sorted(f'{PKG}.Lane{j}' for j in lanes)
    lines = [''.join(f'import {i}\n' for i in imports),
             HEADER.format(doc=f'The `r = 3` range law at depth `t = {t}`, `k = {k}` '
                               f'(class masses `qc / 2^{nb}`), early cap `P = {P}`, `g = 2^{I}` roots.'),
             'open RebuildBound.Spec RebuildBound.Model',
             'open scoped ENNReal\n',
             'namespace RebuildBound.SelRange3\n']
    for X in 'AB':
        res = results[(cfg, X)]
        cid = name + X
        ch = chains[res['key']]
        chid = ch['cid']
        steps = ', '.join(f'({w}, Tab.{chid}_s{n})' for n, (w, _) in enumerate(ch['steps'], start=2))
        convs = ', '.join(f'conv_{chid}_{n}' for n in range(2, R + 1))
        hqT = 'rfl' if (ch['qcT'], ch['nbT']) == (res['qc'], nb) else '(by norm_num)'
        lines += [f'/-- Class {X} (`qc = {res["qc"]}`): certified stop-loss '
                  f'`{float(res["fp"]["total"]):.10e}`. -/',
                  f'theorem class_{cid} (q : unitInterval) (hq : (q : ℝ) = (({res["qc"]} : ℕ) : ℝ) / ((2 ^ {nb} : ℕ) : ℝ)) :',
                  f'    stopLoss (rangeLawR 64 32 {P} (2 ^ {I}) {t} {R} q) 64 ≤',
                  f'      ({tn} : ℝ≥0∞) / (10 ^ {tde} : ℕ) + (2 ^ {I} : ℝ≥0∞) / 10 ^ {EPS_EXP} :=',
                  f'  class_bound RebuildBound.P10r (r := {R}) (t := {t}) (P := {P}) (i := {I}) (nb := {nb})',
                  f'    (qc := {res["qc"]}) (qcT := {ch["qcT"]}) (nbT := {ch["nbT"]})',
                  f'    (steps := [{steps}]) q hq SelRange1.bnd{t} rfl',
                  f'    (by norm_num) (by norm_num) (by norm_num) rfl {hqT} thin_{chid} ⟨{convs}, trivial⟩',
                  f'    final_{cid}\n']
    for s in shapes:
        sp = s['sp']
        lines += [f'/-- {s["name"]}: range term `≤ {float(s["value"]):.6e}`, budget '
                  f'`{s["bn"]} / 10^{s["be"]}`. -/',
                  f'theorem {shape_ident(s)} : selRange {s["geom"]} ≤',
                  f'    ENNReal.ofReal (({s["bn"]} / 10 ^ {s["be"]} : ℚ) : ℝ) :=',
                  f'  selRange_le {s["geom"]}',
                  f'    (r := {R}) (t := {t}) (i := {I}) (P := {P}) (nb := {nb}) (qcA := {sp["qcA"]})',
                  f'    (qcB := {sp["qcB"]}) (n := {sp["n"]}) (m := {sp["m"]}) (num := {sp["num"]})',
                  f'    (tn := {tn}) (td := 10 ^ {tde}) (bn := {s["bn"]}) (bd := 10 ^ {s["be"]})',
                  '    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl',
                  f'    class_{name}A class_{name}B (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
                  '    (by norm_num) (by norm_num)\n']
    lines.append('end RebuildBound.SelRange3')
    (HERE / f'{name}.lean').write_text('\n'.join(lines) + '\n')


MAIN = """
/-!
# SelRange3: the `r = 3` range terms of the selected shapes (package SelRange3)

`RebuildBound.SelRange3 : SelRange3_statement`: each of the 10 `r = 3` shapes of
`selBudgets` (digits 3 and 6) meets its range budget. Generated by
`RebuildBound/Proofs/SelRange3/gen.py`; do not edit.

@DOC@
-/

open RebuildBound.Spec in
/-- **SelRange3.** -/
theorem RebuildBound.SelRange3 : RebuildBound.Spec.SelRange3_statement := by
  unfold SelRange3_statement SelRangeAt
  intro x hx
  simp only [selBudgets, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with @PATTERN@
@CASES@
"""

# Kernel costs measured by hand (see the docstring below); update after regenerating.
DOC = """**Route** (`Glue.lean`). For an `r = 3` shape (`d = 3 · 2^e`, `k = K + e`,
`t = k - I`, `P = earlyCap`, `g = 2^I`), every class mass is `qc / 2^nb` with
`nb = 64 - k` and `qc = 2^nb / 3 + 1` (class A) or `qc = 2^nb / 3` (class B)
(NCA5's `qCount_eq`; `sum_classes`), so the class sum is at most 3 times a
common bound of the two class laws. One class law (`class_bound`, NCA5's
argument for every radix, depth, early cap, `g` and class mass): P10r at
`H = 256`; NCA1's depth-`t` table (`Tab4` … `Tab7`, bounded through SelRange1's
`bnd<t>` by NCA1's `base` and level theorems, so no tree level is rechecked)
thinned by `qc / 2^nb` (`thin_<cfg><X>`, NCA5's `checkThin`: exact, then one
rounding to scale `2^320`); partial sums 2 and 3 of the radix node
(`conv_<cfg><X>_2`, `conv_<cfg><X>_3`, NCA5's `checkConv`, chained by
`ConvChain`); the root-loss marginal and NCA1's `checkFinal` on the one-row
table with its own truncation term off (`final_<cfg><X>`); P10r's term is at most
`2^I / 10^46` (`eps_bound`). The old-map density (radix 5 at `d = 6`, exactly 1
at `d = 3`) is bounded by SelRange1's `density_le`.

Nine configurations `T<t>K<k>` (`L2 d6 (uniform)` and `L3 d3 (half)` share
`t = 5`, `k = 8`, `P = 256`, `I = 3`), 18 class laws. The two classes of a
configuration agree to ten significant digits. The thinning and the partial
sums depend only on `t` and the class mass, which `gen.py` reduces to lowest
terms: four pairs of classes have equal masses (`T5K8B` = `T5K7B`,
`T5K11A` = `T5K10A`, `T6K14B` = `T6K13B`, `T7K17A` = `T7K16A`, e.g.
`93824992236886 / 2^48 = 46912496118443 / 2^47`), so the second class of each
pair uses the first one's tables and checks (`class_bound`'s `hqT`): 14 chains,
42 thinning and partial-sum checks and 18 final checks, 60 kernel checks.

| shape            | config   | `P`  | `g`    | proved bound | budget     | margin | Python     |
|------------------|----------|------|--------|--------------|------------|--------|------------|
| L2 d3 (half)     | `T4K6`   | 192  | `2^2`  | 7.6613e-31   | 7.78e-31   | 1.53 % | 7.7009e-31 |
| L2 d3 (uniform)  | `T5K7`   | 192  | `2^2`  | 8.7204e-33   | 9.01e-33   | 3.21 % | 8.9195e-33 |
| L2 d6 (uniform)  | `T5K8`   | 256  | `2^3`  | 1.1130e-31   | 1.14e-31   | 2.37 % | 1.1272e-31 |
| L3 d3 (half)     | `T5K8`   | 256  | `2^3`  | 1.1130e-31   | 1.14e-31   | 2.37 % | 1.1272e-31 |
| L3 d3 (uniform)  | `T5K10`  | 384  | `2^5`  | 1.5921e-29   | 1.62e-29   | 1.72 % | 1.5989e-29 |
| L3 d6 (uniform)  | `T5K11`  | 448  | `2^6`  | 1.8018e-28   | 1.83e-28   | 1.54 % | 1.8064e-28 |
| L4 d3 (uniform)  | `T6K13`  | 960  | `2^7`  | 1.9557e-27   | 1.98e-27   | 1.23 % | 1.9592e-27 |
| L4 d6 (uniform)  | `T6K14`  | 1088 | `2^8`  | 2.1608e-26   | 2.19e-26   | 1.33 % | 2.1630e-26 |
| L5 d3 (uniform)  | `T7K16`  | 1280 | `2^9`  | 8.6707e-28   | 8.78e-28   | 1.24 % | 8.6848e-28 |
| L5 d6 (uniform)  | `T7K17`  | 1408 | `2^10` | 6.1371e-27   | 6.21e-27   | 1.17 % | 6.1425e-27 |

"Proved bound" is `D 2^t 3 (tn / td + 2^I / 10^46)` with the configuration's
common target `tn / td` (five significant digits above both classes); the
margin is against the budget. Every certified value is below the Python
certifier's (by 0.09 % to 2.2 %), which majorizes `(1 + W)^g` by `exp(g W)` and
uses `λ = 32 + 2^-36`.

**Kernel cost** (`decide +kernel`; each check measured in its own `lean`
process, two at a time on a loaded 64-thread host with `LEAN_NAT_MAX_SIZE = 10^9`;
"type checking" time from the profiler, peak RSS from
`/usr/bin/time`). Per class law:

| theorem            | check                       | kernel         | peak RSS       |
|--------------------|-----------------------------|----------------|----------------|
| `thin_<cfg><X>`    | thinning (`checkThin`)      | 16.7 – 28.7 s  | 14.5 – 17.2 GB |
| `conv_<cfg><X>_2`  | partial sum 2 (`checkConv`) | 10.3 – 18.1 s  | 3.6 – 3.7 GB   |
| `conv_<cfg><X>_3`  | partial sum 3 (`checkConv`) | 15.5 – 25.9 s  | 4.9 – 5.0 GB   |
| `final_<cfg><X>`   | final series (`checkFinal`) | 2.1 – 4.9 s    | 1.5 – 1.7 GB   |

Per configuration (both classes, eight checks, counting shared chains once per
class), kernel time: `T4K6` 95.6 s, `T5K7` 94.8 s, `T5K8` 94.0 s,
`T5K10` 104.7 s, `T5K11` 107.6 s, `T6K13` 107.2 s, `T6K14` 115.8 s, `T7K16`
130.4 s, `T7K17` 139.3 s (about 48 s per class law unloaded). Sharing the
chains removes the thinning and partial-sum
checks of `T5K8B`, `T5K11A`, `T6K14B` and `T7K17A` (12 checks, about 45 s of
kernel time per chain). `Glue`, the configuration modules and this
module take under 6 s each; the 42 tables (0.3 – 0.7 MB of source each)
elaborate in 6 – 28 s under 1 GB.

**Lanes.** The 60 checks live in four modules `Lane0` … `Lane3` (the class
laws dealt round-robin, 14, 14, 16 and 16 checks; a shared chain is checked in
the lane of its first class), each with `Elab.async` off so that its checks run
one after the other. `leanchecker` replays modules in parallel but the
declarations of one module in sequence, so neither `lake build` nor
`leanchecker` runs more than four kernel checks of this package at once.
`lake build` builds the lanes in about 3 minutes wall at about 20 GB peak RSS
per process, and `leanchecker` replays the package in about 7.5 min at about
106 GB (the four lanes plus the imported environments of the other modules'
replay tasks). One module per check would let `leanchecker` run every check at
once, which needs several hundred GB.

**Probability obstacles:** none beyond NCA5's; Mathlib's
measures throughout (`binomial`, `poissonMeasure`, `Measure.conv`,
`Measure.bind`, `lintegral`) through point masses on `ℕ` and `ℕ × ℕ`."""


def main():
    dry = '--dry' in sys.argv
    budgets = parse_budgets()
    configs, classes, chains = plan(budgets)
    st = time.time()
    with mp.Pool(min(len(chains), 18)) as pool:
        for ch in pool.map(run_chain, list(chains)):
            chains[ch['key']].update(ch)
        finals = pool.map(run_final, [
            (chains[c['key']]['steps'][-1][1], c['cfg'][2], c['cfg'][3], c['qc'],
             2 ** (c['nb'] + c['cfg'][0])) for c in classes])
    results = {}
    for c, (fp, secs) in zip(classes, finals):
        results[(c['cfg'], c['X'])] = dict(c, fp=fp, secs=secs)
    print(f'computed {len(chains)} chains and {len(classes)} class laws in '
          f'{time.time() - st:.0f}s', flush=True)
    targets = {}
    for cfg in sorted(configs):
        t, k, P, I = cfg
        tot = max(results[(cfg, X)]['fp']['total'] for X in 'AB')
        ex = math.floor(math.log10(tot.numerator) - math.log10(tot.denominator)) - (SIGDIG - 1)
        assert ex < 0
        tde = -ex
        td = 10 ** tde
        tn = math.ceil(tot * td)
        targets[cfg] = (tn, tde)
        for X in 'AB':
            res = results[(cfg, X)]
            ch = chains[res['key']]
            fp = res['fp']
            assert (fp['fin'] + D * fp['tail']) * td <= tn * D * D
            res['tn'], res['tde'] = tn, tde
            print(f'{cfg_id(cfg)}{X}: qc {res["qc"]}, chain {ch["cid"]} ({ch["qcT"]}/2^{ch["nbT"]}, '
                  f'thin w {ch["wT"]}, conv w {[w for w, _ in ch["steps"]]}, {ch["secs"]:.0f}s), '
                  f'total {float(fp["total"]):.10e} (tail {float(Q(fp["tail"], D)):.2e}), '
                  f'{res["secs"]:.0f}s')
        print(f'{cfg_id(cfg)}: P {P}, g 2^{I}, target {tn}e-{tde}')
        for s in configs[cfg]:
            sp = s['sp']
            two_m = 2 ** sp['m']
            delta = sp['num'] - two_m
            assert delta >= 0 and sp['n'] * delta < two_m
            Dd = two_m - sp['n'] * delta
            bd = 10 ** s['be']
            # the arithmetic check of `selRange_le`
            lhs = two_m * 2 ** t * (R * (tn * 10 ** EPS_EXP + 2 ** I * td)) * bd
            rhs = s['bn'] * (Dd * (td * 10 ** EPS_EXP))
            assert lhs <= rhs, (s['name'], float(Q(lhs, rhs)))
            s['value'] = Q(two_m, Dd) * 2 ** t * R * (Q(tn, td) + Q(2 ** I, 10 ** EPS_EXP))
            exact = Q(two_m, Dd) * 2 ** t * sum(
                (1 if a < 2 ** sp['nb'] % R else 0) * results[(cfg, 'A')]['fp']['total'] +
                (0 if a < 2 ** sp['nb'] % R else 1) * results[(cfg, 'B')]['fp']['total']
                for a in range(R))
            print(f'  {s["name"]:16s} D - 1 <= {float(Q(two_m, Dd) - 1):.3e}, certified class sum '
                  f'{float(exact):.6e}, stated {float(s["value"]):.6e}, budget {s["bn"]}e-{s["be"]}, '
                  f'margin {float(1 - Q(lhs, rhs)):.4%}')
    if dry:
        return
    # tables: one set per chain
    for ch in chains.values():
        t = ch['key'][0]
        cid, users = ch['cid'], ', '.join(ch['users'])
        emit_table(f'Tab{cid}th', f'{cid}_th', ch['Tb'],
                   f'Upper table of `(truncTree 64 32 256 {t}).bind (thinPair q)`, '
                   f'`q = {ch["qcT"]}/2^{ch["nbT"]}` ({users}), at scale `2^{PREC}`.')
        for n, (_, S) in enumerate(ch['steps'], start=2):
            emit_table(f'Tab{cid}s{n}', f'{cid}_s{n}', S,
                       f'Upper table of partial sum {n} of the radix node ({users}), '
                       f'at scale `2^{PREC}`.')
    # lanes: the class laws dealt round-robin (`plan`); a chain's checks go to the
    # lane of its first class, just before that class's final check
    lanes = [([CHECKER], []) for _ in range(LANES)]
    for c in classes:
        res, ch = results[(c['cfg'], c['X'])], chains[c['key']]
        parts = [chain_checks(ch)] if ch['cid'] == c['cid'] else []
        parts.append(final_check(res, ch))
        lane_imps, lane_checks = lanes[c['lane']]
        for imps, cl in parts:
            lane_imps += [i for i in imps if i not in lane_imps]
            lane_checks += cl
    for j, (imps, cl) in enumerate(lanes):
        emit_lane(j, imps, cl)
    for cfg in sorted(configs):
        emit_config(cfg, results, chains, configs[cfg], *targets[cfg])
    # main module
    imports = ''.join(f'import {PKG}.{cfg_id(c)}\n' for c in sorted(configs))
    cases = []
    for s in budgets:
        if s['g']['r'] == R:
            cases.append(f'  · intro _; exact SelRange3.{shape_ident(s)}')
        else:
            cases.append('  · intro hr; exact absurd hr (by decide)')
    pattern = ' | '.join(['rfl'] * len(budgets))
    main_src = (imports + MAIN.replace('@DOC@', DOC).replace('@PATTERN@', pattern)
                .replace('@CASES@', '\n'.join(cases)))
    (HERE.parent / 'SelRange3.lean').write_text(main_src)


if __name__ == '__main__':
    main()
