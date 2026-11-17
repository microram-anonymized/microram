#!/usr/bin/env python3
"""Generate the NCA1 certificate tables and kernel-check modules.

Mirrors the Lean checkers of `Checker.lean` exactly (same integers), so every
emitted check holds by construction:

* `Tab<t>.lean`   upper tables of `truncTree C λ H t` at scale `D = 2^PREC`
                  (rows: main count 0..C, columns: shadow count 0..H);
* `Base.lean`     `checkInit` for table 1 (Poisson masses, NTop enclosures);
* `Level<t>.lean` `checkLevel` from table t-1 to table t (one module per
                  level, so that lake builds them in parallel);
* `Final.lean`    `checkFinal`, the stop-loss series and the truncation term.

No floating point is used. Usage: `python3 gen.py` (about 5 minutes).
"""
import math
import sys
import time
from fractions import Fraction as Q
from pathlib import Path

sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent

# The instance (Spec/CANum.lean): C = L = 64, λ = 32, P = 1408, p = 2^-9,
# g = 2^10, t = 9; truncation cutoff H = 256.
C, H, T, G, P, L = 64, 256, 9, 2 ** 10, 1408, 64
assert G & (G - 1) == 0  # g is emitted as a power of two
LAM_A, LAM_B = 32, 1          # λ = a / b
THIN_A, THIN_D = 1, 2         # binary thinning 1/2
EARLY_A, EARLY_D = 1, 512     # p = 2^-9
PREC = 320
D = 1 << PREC
NTAYLOR, RRED = 100, 32       # NTop exp enclosure: Taylor terms, range reduction
TARGET = (2691, 10 ** 33)


def cdiv(x, y):
    return (x + (y - 1)) // y


# --- NTop.Checker, transcribed -----------------------------------------------
def loT(a, b, r, i):
    v = D
    for k in range(i):
        v = (v * a) // (b * r * (k + 1))
    return v


def upT(a, b, r, i):
    v = D
    for k in range(i):
        v = cdiv(v * a, b * r * (k + 1))
    return v


def powLo(x, m):
    v = D
    for _ in range(m):
        v = (v * x) // D
    return v


def powUp(x, m):
    v = D
    for _ in range(m):
        v = cdiv(v * x, D)
    return v


def lmNum(N, r, a, b):
    return powLo(sum(loT(a, b, r, i) for i in range(N)), r)


def umNum(N, r, a, b):
    us = sum(upT(a, b, r, i) for i in range(N)) + cdiv(upT(a, b, r, N) * (N + 1), N)
    return powUp(us, r)


def eNum(N, r, a, b):
    return cdiv(D * D, lmNum(N, r, a, b))


def pT_list(a, b, E, n):
    out = [E]
    for m in range(n):
        out.append(cdiv(out[-1] * a, b * (m + 1)))
    return out


# --- the checkers ---------------------------------------------------------------
def initial():
    E = eNum(NTAYLOR, RRED, LAM_A, LAM_B)
    p = pT_list(LAM_A, LAM_B, E, H)
    F = [[0] * (H + 1) for _ in range(C + 1)]
    for n in range(H + 1):
        F[min(n, C)][max(n - C, 0)] = p[n]
    return F


def level_out(F, x, al, d):
    """`levelOut x α d C H F` at R = ℕ."""
    be = d - al
    basis = [d ** (H - r) * (be + al * x) ** r for r in range(H + 1)]
    R = [sum(f * e for f, e in zip(row, basis)) for row in F]
    n = len(R)
    # mthin: P_a = Σ_m R_m d^(n-1-m) C(m,a) α^a β^(m-a)
    Pl = [sum(R[m] * d ** (n - 1 - m) * math.comb(m, a) * al ** a * be ** (m - a)
              for m in range(a, n)) for a in range(n)]
    S = [0] * (2 * n - 1)
    for i in range(n):
        for j in range(i, n):
            pr = Pl[i] * Pl[j]
            S[i + j] += pr if i == j else 2 * pr
    tail = 0
    for s in reversed(S[C:]):
        tail = s + tail * x
    return S[:C] + [tail]


def level(F, al=THIN_A, d=THIN_D):
    bound = level_out(F, 1, al, d)
    w = max(bound).bit_length() + 1
    out = level_out(F, 1 << w, al, d)
    c = D * d ** (2 * (H + C))
    mask = (1 << w) - 1
    F2 = []
    for m in range(C + 1):
        x, row = out[m], []
        for v in range(H + 1 - m):
            row.append(cdiv(x & mask, c))
            x >>= w
        F2.append(row + [0] * m)
    return F2, w


def col_sums(F):
    return [sum(row[j] for row in F) for j in range(H + 1)]


def conv_trunc(A, B, n):
    return [sum(A[i] * B[k - i] for i in range(k + 1) if i < len(A) and k - i < len(B))
            for k in range(n)]


class Width:
    def __init__(self, w):
        self.w = w

    def mul_round(self, A, B):
        assert sum(A) * sum(B) < 1 << self.w
        return [cdiv(c, D) for c in conv_trunc(A, B, H + 1)]


def pow_round(W, Qv, fuel, n):
    if fuel == 0:
        assert n == 0
        return [D]
    if n == 0:
        return [D]
    h = pow_round(W, Qv, fuel - 1, n // 2)
    s = W.mul_round(h, h)
    return W.mul_round(s, Qv) if n % 2 == 1 else s


def choose_list(n):
    out, c = [], 1
    for j in range(n):
        out.append(c)
        c = c * (P - j) // (j + 1)
    return out


def final(F):
    cs = col_sums(F)
    Qv = [D] + cs[1:]
    W2 = sum(cs[j] << j for j in range(1, H + 1))
    wf = 2 * PREC + 8
    Wd = Width(wf)
    fuel = G.bit_length()
    A = pow_round(Wd, Qv, fuel, G)
    bl = [cdiv(D * c * EARLY_A ** j * (EARLY_D - EARLY_A) ** (P - j), EARLY_D ** P)
          for j, c in enumerate(choose_list(H + 1))]
    assert sum(bl) * sum(A) < 1 << wf
    c = conv_trunc(bl, A, H + 1)
    fin = sum(c[n] * max(n - L, 0) for n in range(H + 1))
    # exp(g W2 / D) <= umNum / D, which needs g W2 <= D r.
    rr = max(1, cdiv(G * W2, D))
    um = umNum(NTAYLOR, rr, G * W2, D)
    tail = cdiv((H + 1 - L) * (EARLY_D + EARLY_A) ** P * um, 2 ** (H + 1) * EARLY_D ** P)
    # Truncation term: X = (λ + λ²)(2^t - 1) τ_H(λ) <= NX / (b² D ((H+2) b - a)) <= (s / D)².
    a, b = LAM_A, LAM_B
    E = eNum(NTAYLOR, RRED, a, b)
    pH = pT_list(a, b, E, H + 1)[H + 1]
    NX = (a * b + a * a) * (2 ** T - 1) * pH * (H + 2) * b
    den = b * b * ((H + 2) * b - a)
    s = math.isqrt(cdiv(NX * D, den)) + 1
    assert NX * D <= s * s * den
    total = Q(fin, D * D) + Q(tail, D) + Q(G * s, D)
    tn, td = TARGET
    assert (fin + D * (tail + G * s)) * td <= tn * D * D
    print(f'final: fin {float(Q(fin, D * D)):.12e}, tail {float(Q(tail, D)):.3e}, '
          f'eps {float(Q(G * s, D)):.3e}, total {float(total):.12e}, '
          f'target {tn / td:.4e}, margin {float(1 - total / Q(tn, td)):.3e}')
    return dict(wf=wf, fuel=fuel, rr=rr, s=s)


# --- emitting Lean -----------------------------------------------------------------
HEADER = '/-! {doc} Generated by `RebuildBound/Proofs/NCA1/gen.py`; do not edit. -/\n\n'


def emit_table(t, F):
    name = f't{t}'
    out = [HEADER.format(doc=f'Upper table of `truncTree 64 32 256 {t}` at scale `2^{PREC}`.'),
           'namespace RebuildBound.NCA1.Tab\n']
    for m, row in enumerate(F):
        r = list(row)
        while r and r[-1] == 0:
            r.pop()
        out.append(f'def {name}_r{m} : List Nat := [{", ".join(map(str, r))}]\n')
    out.append(f'def {name} : List (List Nat) :=\n  [{", ".join(f"{name}_r{m}" for m in range(len(F)))}]\n')
    out.append('end RebuildBound.NCA1.Tab')
    (HERE / f'Tab{t}.lean').write_text('\n'.join(out) + '\n')


def emit_level(t, w):
    (HERE / f'Level{t}.lean').write_text(
        f'import RebuildBound.Proofs.NCA1.Checker\nimport RebuildBound.Proofs.NCA1.Tab{t - 1}\n'
        f'import RebuildBound.Proofs.NCA1.Tab{t}\n\n' +
        HEADER.format(doc=f'Level check, depth {t - 1} to {t} (kernel time and memory: see `NCA1.lean`).') +
        'namespace RebuildBound.NCA1\n\n'
        f'/-- Kernel check of one binary level (depth {t - 1} to {t}). -/\n'
        f'theorem level{t} : checkLevel {w} {THIN_A} {THIN_D} (2 ^ {PREC}) {C} {H} Tab.t{t - 1} Tab.t{t} = true := by\n'
        '  decide +kernel\n\nend RebuildBound.NCA1\n')


def emit_base():
    (HERE / 'Base.lean').write_text(
        'import RebuildBound.Proofs.NCA1.Checker\nimport RebuildBound.Proofs.NCA1.Tab1\n\n' +
        HEADER.format(doc='Base check: table 1 bounds the Poisson masses.') +
        'namespace RebuildBound.NCA1\n\n'
        '/-- Kernel check of the depth-one table. -/\n'
        f'theorem base : checkInit (2 ^ {PREC}) {NTAYLOR} {RRED} {LAM_A} {LAM_B} {C} {H} Tab.t1 = true := by\n'
        '  decide +kernel\n\nend RebuildBound.NCA1\n')


def emit_final(p):
    tn, td = TARGET
    (HERE / 'Final.lean').write_text(
        f'import RebuildBound.Proofs.NCA1.Checker\nimport RebuildBound.Proofs.NCA1.Tab{T}\n\n' +
        HEADER.format(doc='Final check: stop-loss series and truncation term.') +
        'namespace RebuildBound.NCA1\n\n'
        '/-- Kernel check of the stop-loss series from the root table. -/\n'
        f'theorem final : checkFinal {p["wf"]} (2 ^ {PREC}) {NTAYLOR} {p["rr"]} {RRED} {H} {L} '
        f'(2 ^ {G.bit_length() - 1}) {P} '
        f'{EARLY_A} {EARLY_D} {LAM_A} {LAM_B} {T} {p["fuel"]} {tn} (10 ^ 33) {p["s"]} Tab.t{T} = true := by\n'
        '  decide +kernel\n\nend RebuildBound.NCA1\n')


def main():
    F = initial()
    emit_table(1, F)
    emit_base()
    for t in range(2, T + 1):
        st = time.time()
        F, w = level(F)
        emit_table(t, F)
        emit_level(t, w)
        print(f'level {t}: w {w}, mass {float(Q(sum(map(sum, F)), D)):.15f}, '
              f'{time.time() - st:.1f}s', flush=True)
    emit_final(final(F))


if __name__ == '__main__':
    main()
