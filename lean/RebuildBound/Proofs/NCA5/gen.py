#!/usr/bin/env python3
"""Generate the NCA5 certificate tables and kernel-check modules.

Mirrors the Lean checkers of `Checker.lean` (and NCA1's `checkFinal`) exactly
(same integers), so every emitted check holds by construction. Input: NCA1's
depth-5 table `Tab5.lean` (`truncTree 64 32 256 5` at scale `D = 2^320`),
parsed from its Lean source and not regenerated. For each class mass
`q = qc / 2^51` (one per distinct `qCount`):

* `TabThin<X>.lean`  the table of the thinned tree law (`checkThin`), the exact
                     thinning rounded up to scale `D`;
* `TabS<X><n>.lean`  the table of the `n`-th partial sum of the radix node,
                     `n = 2..r` (`checkConv`), rounded up to scale `D`;
* `Thin<X>.lean`, `Conv<X><n>.lean`  the kernel checks, one module each, so
                     that lake builds them in parallel;
* `Final<X>.lean`    NCA1's `checkFinal` on `[rootMarg C S_r]`.

No floating point enters a table. Usage: `python3 gen.py` (about 3 minutes).
"""
import math
import multiprocessing as mp
import re
import sys
import time
from fractions import Fraction as Q
from pathlib import Path

sys.set_int_max_str_digits(0)
sys.dont_write_bytecode = True  # keep NCA1's directory clean
HERE = Path(__file__).resolve().parent
NCA1 = HERE.parent / 'NCA1'
sys.path.insert(0, str(NCA1))
import gen as G1  # noqa: E402  (NCA1's generator: NTop exp enclosures, powRound)

# The instance (Spec/CANumR.lean): C = L = 64, λ = 32, P = 1088, g = 2^8, t = 5, r = 5,
# 64-bit words with carry bits 13: q_a = qCount 64 13 5 a / 2^51. Cutoff H = 256.
C, H, T, R, P, L = 64, 256, 5, 5, 1088, 64
G = 2 ** 8
assert G & (G - 1) == 0
QD = 2 ** 51                   # class-mass denominator 2^(W - b)
CLASSES = {'A': (QD + 2) // 5,  # classes 0, 1, 2 (2^51 mod 5 = 3)
           'B': (QD - 3) // 5}  # classes 3, 4
EARLY_D = QD * 2 ** T          # p = q 2^-t = qc / 2^56
LAM_A, LAM_B = 32, 1
PREC = 320
D = 1 << PREC
TARGET = (14205, 31)           # per class: tn / 10^td_exp
G1.D, G1.PREC = D, PREC


def cdiv(x, y):
    return (x + (y - 1)) // y


def load_tab5():
    src = (NCA1 / 'Tab5.lean').read_text()
    rows = re.findall(r'def t5_r(\d+) : List Nat := \[([^\]]*)\]', src)
    assert [int(m) for m, _ in rows] == list(range(C + 1))
    return [[int(x) for x in body.split(',')] if body.strip() else [] for _, body in rows]


# --- checkThin -------------------------------------------------------------------
def thin(F, al, d, Z=C, K=H):
    """Exact coefficients of `thinOut X α d K F`, the carry width, and the table."""
    be = d - al
    W = [[d ** (K - r) * math.comb(r, b) * al ** b * be ** (r - b) for b in range(r + 1)]
         for r in range(K + 1)]
    c = []
    for row in F:
        cm = [0] * (K + 1)
        for r, f in enumerate(row):
            if f:
                Wr = W[r]
                for b in range(r + 1):
                    cm[b] += f * Wr[b]
        c.append(cm)
    n = len(F)
    assert n == Z + 1 and all(len(row) <= K + 1 for row in F)
    out = []
    for i in range(n):
        row = [0] * (K + 1)
        for m in range(i, n):
            v = d ** (n - 1 - m) * math.comb(m, i) * al ** i * be ** (m - i)
            cm = c[m]
            for b in range(K + 1):
                if cm[b]:
                    row[b] += cm[b] * v
        out.append(row)
    w = max(sum(r) for r in out).bit_length()
    sc = d ** (Z + K)
    Tb = [trim([cdiv(x, sc) for x in r]) for r in out]
    return Tb, w


def trim(r):
    r = list(r)
    while r and r[-1] == 0:
        r.pop()
    return r


# --- checkConv -------------------------------------------------------------------
def pack(row, w):
    x = 0
    for v in reversed(row):
        x = (x << w) + v
    return x


def conv(A, B, K=H):
    sa = [sum(r) for r in A]
    sb = [sum(r) for r in B]
    mx = max(sum(sa[i] * sb[u - i] for i in range(max(0, u - len(B) + 1), min(u + 1, len(A))))
             for u in range(len(A) + len(B) - 1))
    w = mx.bit_length()
    Ap = [pack(r, w) for r in A]
    Bp = [pack(r, w) for r in B]
    mask = (1 << w) - 1
    out = []
    for u in range(K + 1):
        x = 0
        for i in range(max(0, u - len(B) + 1), min(u + 1, len(A))):
            x += Ap[i] * Bp[u - i]
        row = []
        for _ in range(K + 1 - u):
            row.append(cdiv(x & mask, D))
            x >>= w
        out.append(trim(row))
    while out and not out[-1]:
        out.pop()
    return out, w


def root_marg(A):
    """`rootMarg C A`: the marginal of `v + (u - C)₊`."""
    Rm = [0] * (H + 1)
    for u, row in enumerate(A):
        sh = max(u - C, 0)
        for v, x in enumerate(row):
            Rm[v + sh] += x
    return Rm


# --- checkFinal (NCA1), on the one-row table [rootMarg C S_r] ---------------------
def final(Rm, ap):
    cs = Rm + [0] * (H + 1 - len(Rm))
    Qv = [D] + cs[1:]
    W2 = sum(cs[j] << j for j in range(1, H + 1))
    wf = 2 * PREC + 8
    Wd = G1.Width(wf)
    fuel = G.bit_length()
    G1.H = H
    A = G1.pow_round(Wd, Qv, fuel, G)
    dp = EARLY_D
    bl = [cdiv(D * c * ap ** j * (dp - ap) ** (P - j), dp ** P)
          for j, c in enumerate(choose_list(H + 1))]
    assert sum(bl) * sum(A) < 1 << wf
    c = G1.conv_trunc(bl, A, H + 1)
    fin = sum(c[n] * max(n - L, 0) for n in range(H + 1))
    rr = max(1, cdiv(G * W2, D))
    um = G1.umNum(G1.NTAYLOR, rr, G * W2, D)
    tail = cdiv((H + 1 - L) * (dp + ap) ** P * um, 2 ** (H + 1) * dp ** P)
    tn, te = TARGET
    td = 10 ** te
    # t = 0 and s = 0: NCA1's truncation term vanishes; P10r's is bounded in `NCA5.lean`.
    assert (fin + D * tail) * td <= tn * D * D
    total = Q(fin, D * D) + Q(tail, D)
    return dict(wf=wf, fuel=fuel, rr=rr, fin=Q(fin, D * D), tail=Q(tail, D), total=total)


def choose_list(n):
    out, c = [], 1
    for j in range(n):
        out.append(c)
        c = c * (P - j) // (j + 1)
    return out


# --- emitting Lean -----------------------------------------------------------------
HEADER = '/-! {doc} Generated by `RebuildBound/Proofs/NCA5/gen.py`; do not edit. -/\n\n'


def emit_table(fname, name, F, doc):
    out = [HEADER.format(doc=doc), 'namespace RebuildBound.NCA5.Tab\n']
    for m, row in enumerate(F):
        out.append(f'def {name}_r{m} : List Nat := [{", ".join(map(str, row))}]\n')
    out.append(f'def {name} : List (List Nat) :=\n  [{", ".join(f"{name}_r{m}" for m in range(len(F)))}]\n')
    out.append('end RebuildBound.NCA5.Tab')
    (HERE / f'{fname}.lean').write_text('\n'.join(out) + '\n')


def emit_check(fname, imports, doc, thm, stmt):
    (HERE / f'{fname}.lean').write_text(
        ''.join(f'import {i}\n' for i in imports) + '\n' +
        HEADER.format(doc=doc) +
        'namespace RebuildBound.NCA5\n\n'
        f'/-- {doc} -/\n'
        f'theorem {thm} : {stmt} = true := by\n'
        '  decide +kernel\n\nend RebuildBound.NCA5\n')


def run_class(X):
    qc = CLASSES[X]
    st = time.time()
    F = load_tab5()
    log = []
    Tb, w = thin(F, qc, QD)
    emit_table(f'TabThin{X}', f'th{X}', Tb,
               f'Upper table of `(truncTree 64 32 256 5).bind (thinPair q)`, `q = {qc}/2^51`, at scale `2^{PREC}`.')
    emit_check(f'Thin{X}', ['RebuildBound.Proofs.NCA5.Checker', 'RebuildBound.Proofs.NCA1.Tab5',
                            f'RebuildBound.Proofs.NCA5.TabThin{X}'],
               f'Kernel check of the thinning by `{qc}/2^51` (class {X}).', f'thin{X}',
               f'checkThin {w} {qc} (2 ^ 51) {C} {H} NCA1.Tab.t5 Tab.th{X}')
    log.append(f'class {X}: thin w {w}, mass {float(Q(sum(map(sum, Tb)), D)):.15f}, {time.time() - st:.0f}s')
    S, prev = Tb, f'Tab.th{X}'
    prev_mod = f'RebuildBound.Proofs.NCA5.TabThin{X}'
    for n in range(2, R + 1):
        S, w = conv(S, Tb)
        emit_table(f'TabS{X}{n}', f's{X}{n}', S,
                   f'Upper table of partial sum {n} of the radix node, class {X}, at scale `2^{PREC}`.')
        imps = ['RebuildBound.Proofs.NCA5.Checker', f'RebuildBound.Proofs.NCA5.TabThin{X}',
                f'RebuildBound.Proofs.NCA5.TabS{X}{n}']
        if n > 2:
            imps.insert(2, prev_mod)
        emit_check(f'Conv{X}{n}', imps,
                   f'Kernel check of partial sum {n} of the radix node (class {X}).', f'conv{X}{n}',
                   f'checkConv {w} (2 ^ {PREC}) {H} {prev} Tab.th{X} Tab.s{X}{n}')
        log.append(f'class {X}: conv {n} w {w}, rows {len(S)}, '
                   f'mass {float(Q(sum(map(sum, S)), D)):.15f}, {time.time() - st:.0f}s')
        prev, prev_mod = f'Tab.s{X}{n}', f'RebuildBound.Proofs.NCA5.TabS{X}{n}'
    p = final(root_marg(S), qc)
    tn, te = TARGET
    emit_check(f'Final{X}', ['RebuildBound.Proofs.NCA5.Checker', prev_mod],
               f'Kernel check of the stop-loss series from the root-loss marginal (class {X}).',
               f'final{X}',
               f'NCA1.checkFinal {p["wf"]} (2 ^ {PREC}) {G1.NTAYLOR} {p["rr"]} {G1.RRED} {H} {L} '
               f'(2 ^ {G.bit_length() - 1}) {P} {qc} (2 ^ 56) {LAM_A} {LAM_B} 0 {p["fuel"]} '
               f'{tn} (10 ^ {te}) 0 [rootMarg {C} {prev}]')
    log.append(f'class {X}: final fin {float(p["fin"]):.12e}, tail {float(p["tail"]):.3e}, '
               f'total {float(p["total"]):.12e}, target {tn}e-{te}, '
               f'margin {float(1 - p["total"] / Q(tn, 10 ** te)):.3e}, {time.time() - st:.0f}s')
    return log, p['total']


def main():
    with mp.Pool(len(CLASSES)) as pool:
        res = pool.map(run_class, sorted(CLASSES))
    for log, _ in res:
        print('\n'.join(log))
    tot = 3 * res[0][1] + 2 * res[1][1]
    print(f'class sum {float(tot):.12e} (budget 7.107e-27, Python 7.1067151684e-27)')


if __name__ == '__main__':
    main()
