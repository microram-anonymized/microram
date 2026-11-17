#!/usr/bin/env python3
"""Stash size against N for the Z = 4 read-path tree, fold 1, round-robin reads
(every such row of a run_stash_tail_long.py run, exported with its `export`
command), in the style of the Path ORAM paper's stash figure: one line per
security parameter.  The paper's Figure 9 is drawn by plot_stash_tail.py;
this script adds bootstrap intervals and the extrapolated requirement.

  plot_stash_vs_n.py DEST [--runs RUN_DIR] [--lambdas 12,17,22,27,32]

--runs RUN_DIR  recompute DEST/stash_vs_n.csv from the per-seed .hist files of
                the (gitignored) run directory: for each fold-1 round-robin
                row (read from the files' own headers) and each lambda, the
                measured stash size and a 95% bootstrap interval over seeds.
                Rows without completed seeds are skipped, and so is a lambda
                the row's samples cannot resolve (fewer than 2^lambda).
                Without it, the plots are drawn from the CSV already in DEST.
--lambdas L,..  the security parameters (default 12,17,22,27,32).

Writes DEST/stash_vs_n.{png,pdf}, which uses measured points only, no
extrapolation: the stash size for lambda is the smallest k with
P(op-max >= k) <= 2^-lambda.  A stash of k lanes then overflows on at most a
2^-lambda fraction of accesses, which is the same convention as
stash_requirement.py's k*.

It also writes DEST/stash_vs_n_extrapolated.{png,pdf}: k* at 2^-64, 2^-80 and
2^-96 from DEST/requirement_B.txt (stash_requirement.py --bits B > ...), with
the fit +- 2 jackknife s.e. from DEST/fits.csv as an error bar, against the
127 / 191 / 255 lanes that 2 / 3 / 4 stash registers hold, for the fold-1
round-robin rows of fits.csv; it is skipped without fits.csv and
requirement files.
"""
import argparse
import csv
import glob
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run_stash_tail_long as R  # noqa: E402

import matplotlib  # noqa: E402
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

LAMBDAS = [12, 17, 22, 27, 32]
# One hue, light -> dark with lambda (an ordinal ramp, validated: monotone
# lightness, visible steps, light end >= 2:1 on the surface).
RAMP5 = ["#86b6ef", "#5598e7", "#2a78d6", "#1c5cab", "#0d366b"]
RAMP3 = ["#5598e7", "#256abf", "#0d366b"]
INK, SECONDARY, MUTED = "#0b0b0b", "#52514e", "#898781"
GRID, AXIS, SURFACE = "#e1e0d9", "#c3c2b7", "#fcfcfb"
BOOT = 2000
BOOT_SEED = 1  # the bootstrap resamples are fixed, so a rerun redraws the same bars
SUP = lambda n: str(n).translate(str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹"))


def ramp(n):
    """n colours along RAMP5, light to dark."""
    if n == len(RAMP5):
        return list(RAMP5)
    rgb = [tuple(int(c[i:i + 2], 16) for i in (1, 3, 5)) for c in RAMP5]
    out = []
    for j in range(n):
        x = j * (len(rgb) - 1) / max(1, n - 1)
        i = min(int(x), len(rgb) - 2)
        f = x - i
        out.append("#" + "".join(f"{round(a + (b - a) * f):02x}" for a, b in zip(rgb[i], rgb[i + 1])))
    return out


def need(tail, samples, lam):
    """The smallest k with tail[k] <= samples * 2^-lam."""
    limit = samples * 2.0 ** -lam
    return int(np.argmax(tail <= limit))


def fold1_roundrobin_rows(run_dir):
    """[(log2 N, label, files)] of the run's fold-1 round-robin rows, by the
    spec and workload in each row's .hist headers; rows without files are
    left out."""
    rows = []
    for d in sorted(glob.glob(os.path.join(run_dir, "runs", "*"))):
        files = sorted(glob.glob(os.path.join(d, "*.hist")))
        if not files:
            continue
        spec, workload = {}, None
        with open(files[0]) as f:
            for line in f:
                if line.startswith("spec "):
                    spec = dict(kv.split("=", 1) for kv in line.split()[1].split(","))
                elif line.startswith("workload "):
                    workload = line.split()[1]
                elif line.startswith("hist "):
                    break
        n = int(spec["n"]) if "n" in spec else 1 << int(spec.get("logn", "0"))
        if workload != "roundrobin" or int(spec.get("fold", 1)) != 1 or n & (n - 1):
            continue
        rows.append((n.bit_length() - 1, os.path.basename(d), files))
    return sorted(rows)


def compute(run_dir, dest, lambdas):
    rng = np.random.default_rng(BOOT_SEED)
    out = []
    for log2_n, row, files in fold1_roundrobin_rows(run_dir):
        bins = [R.read_seed_file(f)[("steady", "op-max")] for f in files]
        bins = [b for b in bins if b]
        if not bins:
            print(f"{row}: no steady op-max samples; skipped")
            continue
        kmax = max(max(b) for b in bins)
        # T[s, k] = seed s's samples with op-max >= k, for k = 0 .. kmax + 1.
        T = np.array([R.tail_of(b, kmax) for b in bins], dtype=np.float64)
        pooled = T.sum(axis=0)
        boot = np.empty((BOOT, T.shape[1]))
        for i in range(BOOT):
            w = np.bincount(rng.integers(0, len(bins), len(bins)), minlength=len(bins))
            boot[i] = w @ T
        for lam in lambdas:
            if pooled[0] * 2.0 ** -lam < 1:
                continue  # too few samples to resolve 2^-lam
            k = need(pooled, pooled[0], lam)
            ks = np.array([need(b, b[0], lam) for b in boot])
            lo, hi = np.percentile(ks, [2.5, 97.5])
            out.append({"row": row, "log2_n": log2_n, "seeds": len(bins),
                        "samples": int(pooled[0]), "lambda": lam, "stash": k,
                        "boot_lo": int(lo), "boot_hi": int(hi),
                        "count_ge_stash": int(pooled[k])})
        print(f"{row}: {len(bins)} seeds, max {kmax}")
    if not out:
        sys.exit(f"{run_dir}/runs: no fold-1 round-robin rows with data")
    with open(os.path.join(dest, "stash_vs_n.csv"), "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(out[0]))
        w.writeheader()
        w.writerows(out)


def style(ax):
    ax.set_facecolor(SURFACE)
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_color(AXIS)
    ax.tick_params(colors=SECONDARY, labelsize=9, length=3, color=AXIS)
    ax.grid(axis="y", color=GRID, linewidth=0.6)
    ax.set_axisbelow(True)


def plot_measured(dest, lambdas):
    rows = list(csv.DictReader(open(os.path.join(dest, "stash_vs_n.csv"))))
    have = {int(r["lambda"]) for r in rows}
    if not have & set(lambdas):
        sys.exit(f"{dest}/stash_vs_n.csv has lambdas {sorted(have)}, none of {lambdas}; "
                 "recompute it with --runs")
    fig, ax = plt.subplots(figsize=(6.4, 4.0), facecolor=SURFACE)
    style(ax)
    xs = sorted({int(r["log2_n"]) for r in rows})
    for lam, color in zip(lambdas, ramp(len(lambdas))):
        pts = sorted((int(r["log2_n"]), int(r["stash"]), int(r["boot_lo"]), int(r["boot_hi"]))
                     for r in rows if int(r["lambda"]) == lam)
        if not pts:
            print(f"lambda {lam}: not in {dest}/stash_vs_n.csv; recompute with --runs")
            continue
        x = [p[0] for p in pts]
        y = [p[1] for p in pts]
        ax.vlines(x, [p[2] for p in pts], [p[3] for p in pts], color=color, linewidth=1.0, alpha=0.55)
        ax.plot(x, y, color=color, linewidth=2.0, marker="o", markersize=5.5,
                markeredgecolor=SURFACE, markeredgewidth=1.2, label=f"{lam}", zorder=3)
        ax.annotate(f"λ = {lam}", (x[-1], y[-1]), xytext=(8, 0), textcoords="offset points",
                    va="center", fontsize=9, color=SECONDARY)
    ax.set_xticks(xs)
    ax.set_xlim(xs[0] - 0.6, xs[-1] + 2.2)
    ax.set_ylim(0, None)
    ax.set_xlabel("log₂ N", color=INK, fontsize=10)
    ax.set_ylabel("Stash size (entries)", color=INK, fontsize=10)
    leg = ax.legend(title="Security parameter λ", ncol=len(lambdas), fontsize=8.5, title_fontsize=9,
                    loc="upper left", frameon=False, handlelength=1.6, columnspacing=1.0)
    for t in leg.get_texts():
        t.set_color(SECONDARY)
    leg.get_title().set_color(SECONDARY)
    ax.set_title(r"Measured stash size for a per-access overflow probability of $2^{-\lambda}$",
                 color=INK, fontsize=10.5, loc="left")
    seeds = {int(r["log2_n"]): int(r["seeds"]) for r in rows}
    usual = max(set(seeds.values()), key=list(seeds.values()).count)
    more = ", ".join(f"{s} at N = 2{SUP(n)}" for n, s in sorted(seeds.items()) if s != usual)
    fig.text(0.01, 0.01,
             f"Z = 4 read-path tree, fold 1, load 0.5, round-robin reads; {usual} seeds × 5·10⁸ accesses"
             f" per N{f' ({more})' if more else ''}.\n"
             "Bars: 95% bootstrap interval over seeds.",
             color=MUTED, fontsize=7.5)
    fig.tight_layout(rect=(0, 0.06, 1, 1))
    for ext in ("png", "pdf"):
        fig.savefig(os.path.join(dest, f"stash_vs_n.{ext}"), dpi=200, facecolor=SURFACE)
    plt.close(fig)


def read_requirement(path, rows):
    """{row: k*} from a stash_requirement.py listing ({} if it is missing)."""
    out = {}
    if not os.path.exists(path):
        return out
    for line in open(path):
        p = line.split()
        if p and p[0] in rows and len(p) > 11:
            out[p[0]] = float(p[11])
    return out


def plot_extrapolated(dest):
    path = os.path.join(dest, "fits.csv")
    if not os.path.exists(path):
        print(f"no {path}; skipping the extrapolated plot")
        return False
    fits = {r["row"]: r for r in csv.DictReader(open(path))
            if r["phase"] == "steady" and r["series"] == "op-max"
            and r["workload"] == "roundrobin" and int(r["fold"]) == 1
            and float(r["log2_n"]).is_integer()}
    labels = [l for _, l in sorted((int(float(r["log2_n"])), l) for l, r in fits.items())]
    kstars = {bits: read_requirement(os.path.join(dest, f"requirement_{bits}.txt"), labels)
              for bits in (64, 80, 96)}
    if not labels or not any(kstars.values()):
        print(f"no fold-1 round-robin fits or requirement_B.txt in {dest}; "
              "skipping the extrapolated plot")
        return False
    fig, ax = plt.subplots(figsize=(6.4, 4.0), facecolor=SURFACE)
    style(ax)
    xs = [int(float(fits[r]["log2_n"])) for r in labels]
    for lanes, regs in ((127, 2), (191, 3), (255, 4)):
        ax.axhline(lanes, color=AXIS, linewidth=0.9, linestyle=(0, (4, 3)), zorder=1)
        ax.text(xs[0] - 0.5, lanes + 3, f"A = {regs}: {lanes} lanes", color=MUTED, fontsize=8)
    for bits, color in zip((64, 80, 96), RAMP3):
        kstar = kstars[bits]
        have = [(x, r) for x, r in zip(xs, labels) if r in kstar]
        if not have:
            continue
        hx = [x for x, _ in have]
        fit = [float(fits[r][f"lanes_at_2^-{bits}"]) for _, r in have]
        se = [float(fits[r][f"lanes_at_2^-{bits}_se"] or "nan") for _, r in have]
        y = [kstar[r] for _, r in have]
        ax.vlines(hx, [f - 2 * s for f, s in zip(fit, se)], [f + 2 * s for f, s in zip(fit, se)],
                  color=color, linewidth=1.0, alpha=0.55)
        ax.plot(hx, y, color=color, linewidth=2.0, marker="o", markersize=5.5,
                markeredgecolor=SURFACE, markeredgewidth=1.2, label=rf"$2^{{-{bits}}}$", zorder=3)
        ax.annotate(rf"$2^{{-{bits}}}$", (hx[-1], y[-1]), xytext=(8, 0), textcoords="offset points",
                    va="center", fontsize=9, color=SECONDARY)
    seeds = {x: int(fits[r]["seeds"]) for x, r in zip(xs, labels)}
    usual = max(set(seeds.values()), key=list(seeds.values()).count)
    for x, n in seeds.items():
        if n != usual:
            ax.annotate(f"{n} seeds", (x, kstars[96].get(labels[xs.index(x)], 0)),
                        xytext=(-12, 12), textcoords="offset points", ha="right", va="bottom",
                        fontsize=8, color=SECONDARY)
    ax.set_xticks(xs)
    ax.set_xlim(xs[0] - 0.6, xs[-1] + 2.2)
    ax.set_ylim(0, 280)
    ax.set_xlabel("log₂ N", color=INK, fontsize=10)
    ax.set_ylabel("Required stash k* (lanes)", color=INK, fontsize=10)
    leg = ax.legend(title="Per-access overflow probability", ncol=3, fontsize=8.5, title_fontsize=9,
                    loc="lower left", frameon=False, handlelength=1.6)
    for t in leg.get_texts():
        t.set_color(SECONDARY)
    leg.get_title().set_color(SECONDARY)
    ax.set_title("Extrapolated stash requirement k* (stash_requirement.py)", color=INK,
                 fontsize=10.5, loc="left")
    fig.text(0.01, 0.01,
             "Line: k* = max(fit + 2 s.e., deepest fitted point carried at the flatter slope).\n"
             "Bars: fit ± 2 jackknife s.e.",
             color=MUTED, fontsize=7.5)
    fig.tight_layout(rect=(0, 0.06, 1, 1))
    for ext in ("png", "pdf"):
        fig.savefig(os.path.join(dest, f"stash_vs_n_extrapolated.{ext}"), dpi=200, facecolor=SURFACE)
    plt.close(fig)
    return True


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("dest")
    ap.add_argument("--runs")
    ap.add_argument("--lambdas", default=",".join(map(str, LAMBDAS)))
    a = ap.parse_args()
    try:
        lambdas = [int(x) for x in a.lambdas.split(",") if x.strip()]
    except ValueError:
        ap.error(f"--lambdas: not a list of integers: {a.lambdas!r}")
    if not lambdas:
        ap.error("--lambdas: give at least one")
    os.makedirs(a.dest, exist_ok=True)
    if a.runs:
        compute(a.runs, a.dest, lambdas)
    plot_measured(a.dest, lambdas)
    wrote = "stash_vs_n"
    if plot_extrapolated(a.dest):
        wrote += "{,_extrapolated}"
    print(f"wrote {a.dest}/{wrote}.{{png,pdf}}")


if __name__ == "__main__":
    main()
