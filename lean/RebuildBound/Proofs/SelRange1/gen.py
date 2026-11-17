#!/usr/bin/env python3
"""Generate the SelRange1 kernel checks and per-shape theorems.

SelRange1 (`Spec/Selected.lean`): every `r = 1` shape of `selBudgets` meets its
range budget. At `r = 1` the range term is `D 2^t stopLoss(rangeLaw 64 32 P
2^-t 2^I t) 64` with `t = k - I` (`Glue.lean`), so each shape needs

* a stop-loss bound `tn / td`: P10 and NCA1's root tables `Tab.t<t>`
  (`λ = 32`, `H = 256`, scale `2^320`), then NCA1's `checkFinal` at the
  shape's `P`, `p = 2^-t`, `g = 2^I` (one module per distinct `(t, P, I)`,
  so that lake builds them in parallel);
* the density `D = (num / 2^m)^n ≤ 2^m / (2^m - n (num - 2^m))` (`Glue.lean`,
  from Bernoulli's inequality), with `num`, `m` and `n` evaluated here and
  re-checked by the kernel (`rfl`);
* `2^m 2^t tn bd ≤ bn (2^m - n (num - 2^m)) td` for the budget `bn / bd`.

The shapes and budgets are parsed from `Spec/Selected.lean`; the tables from
NCA1's `Tab<t>.lean`; the integer arithmetic is NCA1's (`NCA1/gen.py`,
imported), so every emitted check holds by construction. No floating point
enters a check. Usage: `python3 gen.py` (under a minute).
"""
import importlib.util
import math
import re
import sys
from fractions import Fraction as Q
from pathlib import Path

sys.set_int_max_str_digits(0)
sys.dont_write_bytecode = True  # no __pycache__ in NCA1/
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]          # .../lean
NCA1_DIR = HERE.parent / 'NCA1'

spec = importlib.util.spec_from_file_location('nca1gen', NCA1_DIR / 'gen.py')
nca1 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(nca1)

C, H, L = nca1.C, nca1.H, nca1.L        # 64, 256, 64
PREC, D = nca1.PREC, nca1.D              # 2^320
NTAYLOR, RRED = nca1.NTAYLOR, nca1.RRED
LAM_A, LAM_B = nca1.LAM_A, nca1.LAM_B    # λ = 32
W = 64                                   # word width
SIGDIG = 5                               # significant digits of the stop-loss targets


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
    return dict(k=k, t=t, I=g['I'], P=P, m=m, num=num, n=n)


# --- tables -----------------------------------------------------------------------
def read_table(t):
    src = (NCA1_DIR / f'Tab{t}.lean').read_text()
    rows = {}
    for mt in re.finditer(rf'def t{t}_r(\d+) : List Nat := \[([^\]]*)\]', src):
        vals = [int(v) for v in mt[2].split(',')] if mt[2].strip() else []
        rows[int(mt[1])] = vals + [0] * (H + 1 - len(vals))
    assert sorted(rows) == list(range(C + 1))
    return [rows[m] for m in range(C + 1)]


# --- the final check at one (t, P, I) -------------------------------------------------
def final(F, t, P, I):
    """NCA1's `final` at depth `t`, early cap `P`, `p = 2^-t`, `g = 2^I`; returns the
    certified stop-loss (exact rational) and the check's parameters."""
    G = 2 ** I
    ea, ed = 1, 2 ** t
    cs = nca1.col_sums(F)
    Qv = [D] + cs[1:]
    W2 = sum(cs[j] << j for j in range(1, H + 1))
    wf = 2 * PREC + 8
    Wd = nca1.Width(wf)
    fuel = G.bit_length()
    A = nca1.pow_round(Wd, Qv, fuel, G)
    choose = []
    c = 1
    for j in range(H + 1):
        choose.append(c)
        c = c * max(P - j, 0) // (j + 1)
    # ℕ subtraction, as in `binomRow`: `(d - a)^(P - j)` with `P - j = 0` for `j ≥ P`
    bl = [nca1.cdiv(D * c * ea ** j * (ed - ea) ** max(P - j, 0), ed ** P)
          for j, c in enumerate(choose)]
    assert sum(bl) * sum(A) < 1 << wf
    cc = nca1.conv_trunc(bl, A, H + 1)
    fin = sum(cc[n] * max(n - L, 0) for n in range(H + 1))
    rr = max(1, nca1.cdiv(G * W2, D))
    assert G * W2 <= D * rr
    um = nca1.umNum(NTAYLOR, rr, G * W2, D)
    tail = nca1.cdiv((H + 1 - L) * (ed + ea) ** P * um, 2 ** (H + 1) * ed ** P)
    a, b = LAM_A, LAM_B
    E = nca1.eNum(NTAYLOR, RRED, a, b)
    pH = nca1.pT_list(a, b, E, H + 1)[H + 1]
    NX = (a * b + a * a) * (2 ** t - 1) * pH * (H + 2) * b
    den = b * b * ((H + 2) * b - a)
    s = math.isqrt(nca1.cdiv(NX * D, den)) + 1
    assert NX * D <= s * s * den
    total = Q(fin, D * D) + Q(tail, D) + Q(G * s, D)
    # target tn / td: total rounded up to SIGDIG significant digits
    ex = math.floor(math.log10(total.numerator) - math.log10(total.denominator)) - (SIGDIG - 1)
    if ex < 0:
        td, tn = 10 ** (-ex), math.ceil(total * 10 ** (-ex))
    else:
        raise AssertionError('stop-loss too large')
    assert (fin + D * (tail + G * s)) * td <= tn * D * D
    return dict(total=total, tn=tn, tde=-ex, td=td, wf=wf, fuel=fuel, rr=rr, s=s,
                parts=(Q(fin, D * D), Q(tail, D), Q(G * s, D)))


# --- emitting Lean ------------------------------------------------------------------
HEADER = '/-! {doc} Generated by `RebuildBound/Proofs/SelRange1/gen.py`; do not edit. -/\n\n'


def mod_name(cfg):
    t, P, I = cfg
    return f'T{t}P{P}I{I}'


def shape_ident(s):
    lvl, dig, conf = s['name'].replace('(', '').replace(')', '').split()
    return f'{"u" if conf == "uniform" else "h"}{lvl}{dig}'


def emit_config(cfg, fp, shapes):
    t, P, I = cfg
    name = mod_name(cfg)
    lines = [f'import RebuildBound.Proofs.SelRange1.Glue\n',
             HEADER.format(doc=f'Range term at depth `t = {t}`, early cap `P = {P}`, `g = 2^{I}` roots.'),
             'open RebuildBound.Spec RebuildBound.Model',
             'open scoped ENNReal\n',
             'namespace RebuildBound.SelRange1\n',
             f'/-- Kernel check of the stop-loss series (NCA1\'s `checkFinal`) at `t = {t}`, `P = {P}`,',
             f'`g = 2^{I}`: certified total `{float(fp["total"]):.6e}`. -/',
             f'theorem final_{name} : NCA1.checkFinal {fp["wf"]} (2 ^ {PREC}) {NTAYLOR} {fp["rr"]} {RRED} '
             f'{H} {L} (2 ^ {I}) {P} 1 (2 ^ {t}) {LAM_A} {LAM_B} {t} {fp["fuel"]} {fp["tn"]} '
             f'(10 ^ {fp["tde"]}) {fp["s"]} NCA1.Tab.t{t} = true := by',
             '  decide +kernel\n',
             f'/-- The stop-loss at `t = {t}`, `P = {P}`, `g = 2^{I}`. -/',
             f'theorem range_{name} : stopLoss (rangeLaw 64 32 {P} (halfPow {t}) (2 ^ {I}) {t}) 64 ≤',
             f'    ({fp["tn"]} : ℝ≥0∞) / (10 ^ {fp["tde"]} : ℕ) :=',
             f'  range_le final_{name} bnd{t} (by norm_num)\n']
    for s in shapes:
        sp = s['sp']
        lines += [f'/-- {s["name"]}: range term `≤ {float(s["value"]):.6e}`, budget '
                  f'`{s["bn"]} / 10^{s["be"]}`. -/',
                  f'theorem {shape_ident(s)} : selRange {s["geom"]} ≤',
                  f'    ENNReal.ofReal (({s["bn"]} / 10 ^ {s["be"]} : ℚ) : ℝ) :=',
                  f'  selRange_le {s["geom"]}',
                  f'    (t := {t}) (i := {I}) (P := {P}) (n := {sp["n"]}) (m := {sp["m"]})',
                  f'    (num := {sp["num"]}) (bn := {s["bn"]}) (bd := 10 ^ {s["be"]})',
                  '    rfl rfl rfl rfl rfl rfl rfl rfl range_' + name + ' (by norm_num)',
                  '    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n']
    lines.append('end RebuildBound.SelRange1')
    (HERE / f'{name}.lean').write_text('\n'.join(lines) + '\n')


MAIN = """
/-!
# SelRange1: the `r = 1` range terms of the selected shapes (package SelRange1)

`RebuildBound.SelRange1 : SelRange1_statement`: each of the 16 `r = 1` shapes of
`selBudgets` (digits 2, 4, 8) meets its range budget. Generated by
`RebuildBound/Proofs/SelRange1/gen.py`; do not edit.

**Route.** At `r = 1`, `qMass 64 k 1 0 = 1` and `radixRoot C λ t 1 1` is the law
of `R_t`, so `selRange g = D 2^t stopLoss(rangeLaw 64 32 P 2^-t 2^I t) 64` with
`t = k - I`, `P = earlyCap` (`Glue.lean`). The stop-loss is certified from P10
at `H = 256` and NCA1's root tables (`λ = 32`, scale `2^320`; NCA1's level
theorems, so no tree level is rechecked) by NCA1's `checkFinal` at the shape's
`P`, `p = 2^-t`, `g = 2^I`, one module per distinct `(t, P, I)` (13 modules).
The old-map density `D = (num / 2^m)^n` (`n = 32 (d - 1) U`, up to `1.5 · 10^7`)
is bounded by `2^m / (2^m - n (num - 2^m))` (`(1 + x)^n ≤ exp(n x) ≤ 1/(1 - n x)`);
it is exactly 1 at `d = 2`. The certified values are 1.2% to 6.4% below the
budgets (`gen.py` prints them).

@TIMING@
-/

open RebuildBound.Spec in
/-- **SelRange1.** -/
theorem RebuildBound.SelRange1 : RebuildBound.Spec.SelRange1_statement := by
  unfold SelRange1_statement SelRangeAt
  intro x hx
  simp only [selBudgets, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with @PATTERN@
@CASES@
"""

# Kernel costs measured by hand (see the docstring below); update after regenerating.
TIMING = """**Kernel cost** (`decide +kernel`; one `lean` process per module, run
sequentially on this host with `LEAN_NAT_MAX_SIZE = 10^9`; "type checking" time
from the profiler, peak RSS from `/usr/bin/time`). The final checks build in
parallel; with lake the whole package takes about 13 s wall.

| module        | kernel | wall  | peak RSS |
|---------------|--------|-------|----------|
| `Glue`        | 0.27 s | 4.3 s | 3.5 GB   |
| `T6P128I1`    | 1.36 s | 4.1 s | 3.7 GB   |
| `T7P128I1`    | 1.35 s | 4.7 s | 3.7 GB   |
| `T7P192I2`    | 1.41 s | 4.6 s | 3.7 GB   |
| `T7P256I3`    | 1.53 s | 4.8 s | 3.8 GB   |
| `T7P320I4`    | 1.60 s | 5.0 s | 3.8 GB   |
| `T7P384I5`    | 1.66 s | 4.9 s | 3.8 GB   |
| `T7P448I6`    | 1.73 s | 4.9 s | 3.8 GB   |
| `T8P832I6`    | 1.28 s | 4.1 s | 3.8 GB   |
| `T8P960I7`    | 1.79 s | 4.6 s | 3.9 GB   |
| `T9P960I7`    | 1.31 s | 4.6 s | 3.9 GB   |
| `T9P1088I8`   | 1.85 s | 5.1 s | 3.9 GB   |
| `T9P1280I9`   | 1.82 s | 5.0 s | 3.9 GB   |
| `T9P1408I10`  | 1.98 s | 5.2 s | 3.9 GB   |
| `SelRange1`   | 0.02 s | 3.6 s | 3.4 GB   |

Total kernel time 21.9 s. No tree level is rechecked: the tables' bounds come
from NCA1's `base` and `level2` … `level9`.

**Probability obstacles:** none. The `r = 1` identities use
Mathlib's measures (`Measure.ext_of_singleton` for `Bin(n, 1) = δ_n`,
`Measure.dirac_prod_dirac`, `Measure.bind_dirac`, `Measure.dirac_zero_conv`,
`Measure.map_congr`)."""


def main():
    budgets = parse_budgets()
    r1 = [s for s in budgets if s['g']['r'] == 1]
    assert len(r1) == 16
    tabs = {}
    configs = {}
    for s in r1:
        sp = shape_params(s)
        s['sp'] = sp
        assert 4 <= sp['t'] <= 9 and s['g']['C'] == 64
        configs.setdefault((sp['t'], sp['P'], sp['I']), []).append(s)
    results = {}
    for cfg in sorted(configs):
        t, P, I = cfg
        if t not in tabs:
            tabs[t] = read_table(t)
        fp = final(tabs[t], t, P, I)
        results[cfg] = fp
        print(f'{mod_name(cfg)}: total {float(fp["total"]):.10e} '
              f'(fin {float(fp["parts"][0]):.4e}, tail {float(fp["parts"][1]):.2e}, '
              f'eps {float(fp["parts"][2]):.2e}); target {fp["tn"]}e-{fp["tde"]}', flush=True)
        for s in configs[cfg]:
            sp = s['sp']
            two_m = 2 ** sp['m']
            delta = sp['num'] - two_m
            assert delta >= 0 and sp['n'] * delta < two_m
            Dd = two_m - sp['n'] * delta
            bd = 10 ** s['be']
            # the arithmetic check of `selRange_le`
            lhs = two_m * 2 ** t * fp['tn'] * bd
            rhs = s['bn'] * (Dd * fp['td'])
            assert lhs <= rhs, (s['name'], lhs / rhs)
            s['value'] = Q(two_m, Dd) * 2 ** t * fp['total']
            print(f'  {s["name"]:16s} D - 1 <= {float(Q(two_m, Dd) - 1):.3e}, value {float(s["value"]):.6e} '
                  f'budget {s["bn"]}e-{s["be"]} margin {float(1 - Q(lhs, rhs)):.4%}')
        emit_config(cfg, fp, configs[cfg])
    # main module
    imports = ''.join(f'import RebuildBound.Proofs.SelRange1.{mod_name(c)}\n' for c in sorted(configs))
    cases = []
    for s in budgets:
        if s['g']['r'] == 1:
            cases.append(f'  · intro _; exact SelRange1.{shape_ident(s)}')
        else:
            cases.append('  · intro hr; exact absurd hr (by decide)')
    pattern = ' | '.join(['rfl'] * len(budgets))
    main_src = (imports + MAIN.replace('@TIMING@', TIMING).replace('@PATTERN@', pattern).replace('@CASES@', '\n'.join(cases)))
    (HERE.parent / 'SelRange1.lean').write_text(main_src)


if __name__ == '__main__':
    main()
