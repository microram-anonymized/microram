#!/usr/bin/env python3
"""Figure 9 and the stash-tail numbers of Appendix A.3/A.4, from one
`run_stash_tail_long.py export` directory (its tail.csv and fits.csv only).

  plot_stash_tail.py EXPORT_DIR [--out DIR] [--lambdas 15,20,25,30]
                     [--target-bits 95] [--no-figure] [--check-paper]

Writes into DIR (default EXPORT_DIR):
  tree_stash_tail.pdf, .png    Figure 9: (a) the stash tail of the 2^20 and
                               2^21 trees with and without merged levels,
                               measured marks and fitted lines; (b) the
                               measured stash size for 2^-lambda per access
                               against N, without merged levels.  Needs
                               matplotlib; skipped with a note without it.
  stash_tail_summary.txt, .json  every row's fit at the target, its
                               extrapolation to the library's stash, the
                               Figure 9(b) table, and each A.3/A.4 number
                               beside the paper's value.

Everything uses the steady phase's op-max series: x is the number of
records left in the stash after an access.

  * Measured stash size for 2^-lambda: the smallest k with
    P[x >= k] <= 2^-lambda (count_ge_k <= samples * 2^-lambda); "not
    reached" when no measured k gets there.  No extrapolation.
  * Fitted line: log2 P[x >= k] = intercept - slope * k (fits.csv, the
    window and fit of `run_stash_tail_long.py export`).
  * k at 2^-B: (B + intercept) / slope, the plain line (the paper's
    number), without the jackknife margin and flat-tail guard that
    stash_requirement.py adds to its k*.  Registers needed:
    ceil((k + 1) / 64), as A registers hold 64 A - 1 records beside the
    accessed one.
  * At the stash: the line at 64 A and at 64 A - 1, where A is the
    library's default stash registers for the row's leaf bits and fold
    (src/oram/tree/cpu_tree_layout.hpp, DefaultStashRegisters).  The engine
    overflows when x > 64 A - 1, so 64 A is the overflow event and 64 A - 1
    is one record more conservative.  Per 2^31 accesses adds 31 (a union
    bound).

Rows are found by workload (roundrobin), log2 N and fold, not by label, so a
relabelled run still matches; rows missing from the export, or whose tail
was too short to fit, are reported as missing and left out of the figure.
The N sweep (Figure 9(b)) is every fold-1 round-robin row in the export.
`--check-paper` exits 1 unless every paper number is present and agrees.
"""

import argparse
import csv
import json
import math
import os
import sys

TARGET_BITS = 95
LAMBDAS = (15, 20, 25, 30)
PAPER_SWEEP_LOG2N = (12, 15, 18, 20, 21, 24, 27)
# Figure 9(b) as published: measured stash size per lambda at the N above.
PAPER_FIG9B = {15: (15, 15, 15, 15, 15, 16, 16),
               20: (20, 21, 22, 22, 22, 22, 22),
               25: (26, 27, 28, 29, 29, 29, 29),
               30: (32, 33, 35, 34, 36, 36, 39)}
# Figure 9(a): (log2 N, fold, legend, colour, marker), in legend order; the
# paper draws the 2^20 rows first (DRAW_ORDER).  Merging m levels is fold
# m + 1 (src/oram/tree/DESIGN.md).
FIG9A = ((20, 1, "$2^{20}$, no merge", "#5598e7", "o"),
         (21, 1, "$2^{21}$, no merge", "#f39a6b", "^"),
         (20, 3, "$2^{20}$, merge 2 levels", "#104281", "D"),
         (21, 4, "$2^{21}$, merge 3 levels", "#b4461c", "s"))
DRAW_ORDER = (0, 2, 1, 3)
RAMP = ("#a397ef", "#7a68e0", "#5440c0", "#2f1f85")  # Figure 9(b), light to dark
PAPER_LABEL = {(20, 1): "N20-f1-rr", (21, 1): "N21-f1-rr", (20, 3): "N20-f3-rr",
               (21, 4): "N21-f4-rr", (21, 5): "N21-f5-rr", (12, 1): "N12-f1-rr",
               (15, 1): "N15-f1-rr", (18, 1): "N18-f1-rr", (24, 1): "N24-f1-rr",
               (27, 1): "N27-f1-rr"}
WIDE_STASH_LEAF_BITS = 23  # src/oram/tree/cpu_tree_layout.hpp


def default_registers(fold, leaf_bits):
    """DefaultStashRegisters (src/oram/tree/cpu_tree_layout.hpp)."""
    return 3 if fold <= 4 and leaf_bits < WIDE_STASH_LEAF_BITS else 4


def default_fold(leaf_bits):
    """DefaultFold (src/oram/tree/cpu_tree_layout.hpp)."""
    return leaf_bits - 15 if 17 <= leaf_bits <= 20 else 1


def log2_n_of(text):
    value = float(text)
    return int(value) if value.is_integer() else value


def load(export_dir):
    """(rows, fits): rows[label] = the row's steady op-max tail and identity;
    fits[label] = its fits.csv line (steady op-max), if it was fitted."""
    rows, fits = {}, {}
    with open(os.path.join(export_dir, "tail.csv"), newline="") as f:
        for r in csv.DictReader(f):
            if r["phase"] != "steady" or r["series"] != "op-max":
                continue
            row = rows.setdefault(r["row"], {
                "label": r["row"], "workload": r["workload"],
                "log2_n": log2_n_of(r["log2_n"]), "fold": int(r["fold"]),
                "leaf_bits": int(r["lambda"]), "seeds": int(r["seeds"]),
                "samples": int(r["samples"]), "points": {}})
            row["points"][int(r["k"])] = (int(r["count_ge_k"]), float(r["neg_log2_p_ge_k"]))
    with open(os.path.join(export_dir, "fits.csv"), newline="") as f:
        for r in csv.DictReader(f):
            if r["phase"] == "steady" and r["series"] == "op-max":
                fits[r["row"]] = r
                rows.setdefault(r["row"], {
                    "label": r["row"], "workload": r["workload"],
                    "log2_n": log2_n_of(r["log2_n"]), "fold": int(r["fold"]),
                    "leaf_bits": int(r["lambda"]), "seeds": int(r["seeds"]),
                    "samples": int(r["samples"]), "points": {}})
    return rows, fits


def find(rows, log2_n, fold, notes):
    """The label of the round-robin row of this log2 N and fold, or None."""
    hits = [l for l, r in rows.items() if r["workload"] == "roundrobin"
            and r["log2_n"] == log2_n and r["fold"] == fold]
    if len(hits) > 1:
        pick = PAPER_LABEL.get((log2_n, fold))
        pick = pick if pick in hits else hits[0]
        notes.append(f"several round-robin rows at 2^{log2_n} fold {fold} "
                     f"({', '.join(hits)}); using {pick}")
        return pick
    return hits[0] if hits else None


def stash_needed(row, lam):
    """The smallest measured k with P[x >= k] <= 2^-lam, or None."""
    for k in sorted(row["points"]):
        if row["points"][k][0] * 2.0 ** lam <= row["samples"]:
            return k
    return None


def line_at(fit, k):
    return float(fit["intercept_log2"]) - float(fit["slope_bits_per_lane"]) * k


def k_at(fit, bits):
    return (bits + float(fit["intercept_log2"])) / float(fit["slope_bits_per_lane"])


def registers_for(k):
    return math.ceil((k + 1) / 64)


def row_summary(row, fit, target):
    out = {"label": row["label"], "workload": row["workload"], "log2_n": row["log2_n"],
           "fold": row["fold"], "merged_levels": row["fold"] - 1,
           "leaf_bits": row["leaf_bits"],
           "library_default_fold": default_fold(row["leaf_bits"]) == row["fold"],
           "seeds": row["seeds"], "samples": row["samples"],
           "max": max(row["points"]) if row["points"] else None, "fitted": fit is not None}
    if fit is None:
        return out
    a = default_registers(row["fold"], row["leaf_bits"])
    k = k_at(fit, target)
    out.update({
        "window": [int(fit["window_k0"]), int(fit["window_k1"])],
        "intercept_log2": float(fit["intercept_log2"]),
        "slope_bits_per_record": float(fit["slope_bits_per_lane"]),
        "r2": float(fit["r2"]),
        "k_at_target": k, "registers_for_k_at_target": registers_for(k),
        "default_registers": a,
        "log2_p_at_64A": line_at(fit, 64 * a),
        "log2_p_at_64A_minus_1": line_at(fit, 64 * a - 1),
    })
    out["log2_p_at_64A_per_2^31_accesses"] = out["log2_p_at_64A"] + 31
    out["log2_p_at_64A_minus_1_per_2^31_accesses"] = out["log2_p_at_64A_minus_1"] + 31
    return out


def summarize(rows, fits, target=TARGET_BITS, lambdas=LAMBDAS):
    notes = []
    per_row = {l: row_summary(r, fits.get(l), target) for l, r in rows.items()}
    paper_target = target == TARGET_BITS
    claims = []

    def claim(cid, text, label, value, shown, paper, agrees, unit="", complete=True):
        # status: agrees / differs; missing (no row, no fit, or the run never
        # got that deep); incomplete (it needs rows that are missing); not
        # compared (no paper value at this --target-bits / --lambdas).
        status = ("not compared" if paper is None else "missing" if value is None
                  else "incomplete" if not complete else "agrees" if agrees else "differs")
        claims.append({"id": cid, "text": text, "row": label, "value": value,
                       "shown": shown, "unit": unit, "paper": paper, "status": status})

    def fitted(log2_n, fold):
        label = find(rows, log2_n, fold, notes)
        return (label, per_row[label]) if label and per_row[label]["fitted"] else (label, None)

    t = f"2^-{target}"
    # A.3, "Estimating the stash size" (Figure 9(a) lines).
    for log2_n, fold, what, slope_paper, k_paper in ((20, 3, "2^20, merge 2 levels", "0.76", 134),
                                                      (21, 4, "2^21, merge 3 levels", "0.69", 158)):
        label, s = fitted(log2_n, fold)
        v = s["slope_bits_per_record"] if s else None
        claim(f"A.3 slope {what}", f"A.3: fitted line of the {what} tree falls by", label,
              v, f"{v:.2f}" if s else None, slope_paper,
              s is not None and f"{v:.2f}" == slope_paper, "bits per record")
        v = s["k_at_target"] if s else None
        claim(f"A.3 k at {t} {what}", f"A.3: the {what} line reaches {t} at", label,
              v, f"{v:.1f}" if s else None, k_paper if paper_target else None,
              s is not None and round(v) == k_paper, "records")
    label21, s21 = fitted(21, 4)
    for key, slots in (("log2_p_at_64A", "64A"), ("log2_p_at_64A_minus_1", "64A-1")):
        v = s21[key] if s21 else None
        lanes = (64 * s21["default_registers"] - (slots == "64A-1")) if s21 else None
        claim(f"A.3 log2 P at {slots} 2^21 merge 3",
              f"A.3: the 2^21 merge-3 line at {lanes} records ({slots}, A = "
              f"{s21['default_registers'] if s21 else '?'}), log2 per access", label21,
              v, f"{v:.2f}" if s21 else None, -118, s21 is not None and abs(v + 118) < 1)
    label20, s20 = fitted(20, 3)
    v = s20["log2_p_at_64A"] if s20 else None
    claim("A.3 log2 P at 64A 2^20 merge 2",
          "A.3: the 2^20 merge-2 line at 64A records, log2 per access (paper: less than "
          "the 2^21 tree's)", label20, v, f"{v:.2f}" if s20 else None,
          "less than 2^21 merge 3", s20 is not None and s21 is not None
          and v < s21["log2_p_at_64A"] and s20["log2_p_at_64A_minus_1"] < s21["log2_p_at_64A_minus_1"])
    # A.3, "Merging levels into the stash" (2^21, merged 0 / 3 / 4 levels).
    merges = {}
    for fold, k_paper, regs_paper in ((1, 121, None), (4, 158, 3), (5, 199, 4)):
        label, s = fitted(21, fold)
        v = s["k_at_target"] if s else None
        merges[fold - 1] = {"row": label, "k_at_target": v,
                            "registers": s["registers_for_k_at_target"] if s else None}
        claim(f"A.3 k at {t} 2^21 merged {fold - 1}",
              f"A.3: 2^21 with {fold - 1} merged levels needs, at {t}", label, v,
              f"{v:.1f}" if s else None, k_paper if paper_target else None,
              s is not None and round(v) == k_paper, "records")
        if regs_paper is not None:
            r = s["registers_for_k_at_target"] if s else None
            claim(f"A.3 registers 2^21 merged {fold - 1}",
                  f"A.3: stash registers that hold it, ceil((k + 1) / 64)", label, r,
                  str(r) if s else None, regs_paper if paper_target else None,
                  r == regs_paper)
    # Figure 9(b) and the N sweep.
    sweep = sorted((r["log2_n"], l) for l, r in rows.items()
                   if r["workload"] == "roundrobin" and r["fold"] == 1
                   and isinstance(r["log2_n"], int))
    fig9b = {"log2_n": [n for n, _ in sweep], "rows": [l for _, l in sweep],
             "seeds": [rows[l]["seeds"] for _, l in sweep], "lambdas": list(lambdas),
             "stash": {str(lam): [stash_needed(rows[l], lam) for _, l in sweep] for lam in lambdas},
             "paper": {}}
    for lam in lambdas:
        if lam not in PAPER_FIG9B:
            continue
        fig9b["paper"][str(lam)] = [PAPER_FIG9B[lam][PAPER_SWEEP_LOG2N.index(n)]
                                    if n in PAPER_SWEEP_LOG2N else None for n, _ in sweep]
        for n, paper in zip(PAPER_SWEEP_LOG2N, PAPER_FIG9B[lam]):
            label = find(rows, n, 1, [])
            v = stash_needed(rows[label], lam) if label else None
            claim(f"Fig 9(b) 2^-{lam} 2^{n}", f"Figure 9(b): stash size for 2^-{lam} at "
                  f"N = 2^{n}", label, v, str(v) if v is not None else None, paper,
                  v == paper, "records")
    missing_sweep = [n for n in PAPER_SWEEP_LOG2N if n not in fig9b["log2_n"]]
    fitted_sweep = [(per_row[l], l) for _, l in sweep if per_row[l]["fitted"]]
    complete = not missing_sweep and len(fitted_sweep) == len(sweep)
    worst = {}
    for key in ("log2_p_at_64A_minus_1", "log2_p_at_64A"):
        if fitted_sweep:
            s, l = max(fitted_sweep, key=lambda x: x[0][key])
            worst[key] = {"row": l, "value": s[key]}
        v = worst[key]["value"] if key in worst else None
        slots = "64A-1" if key.endswith("minus_1") else "64A"
        claim(f"A.3 N sweep worst at {slots}",
              f"A.3: worst N-sweep line at {slots} records, log2 per access",
              worst[key]["row"] if key in worst else None, v,
              f"{v:.2f}" if v is not None else None, "below -144",
              v is not None and v < -144, complete=complete)
    # A.4: the 2^21 tree per 2^31 accesses, and the other trees.
    for key, slots in (("log2_p_at_64A_per_2^31_accesses", "64A"),
                       ("log2_p_at_64A_minus_1_per_2^31_accesses", "64A-1")):
        v = s21[key] if s21 else None
        claim(f"A.4 2^21 per 2^31 accesses at {slots}",
              f"A.4: the 2^21 merge-3 tree at {slots} records, log2 per 2^31 accesses",
              label21, v, f"{v:.2f}" if s21 else None, -87,
              s21 is not None and abs(v + 87) < 1)
    others = {}
    for scope, keep in (("library default fold", lambda s: s["library_default_fold"]),
                        ("all measured rows", lambda s: True)):
        cand = [(s["log2_p_at_64A"], l) for l, s in per_row.items()
                if s["fitted"] and l != label21 and keep(s)
                and isinstance(s["log2_n"], (int, float)) and s["log2_n"] <= 27]
        if cand:
            v, l = max(cand)
            others[scope] = {"row": l, "log2_p_at_64A": v,
                             "log2_p_at_64A_minus_1": per_row[l]["log2_p_at_64A_minus_1"]}
    o = others.get("library default fold")
    claim("A.4 other trees lower", "A.4: worst other tree up to 2^27 at the library default "
          "fold, at 64A records, log2 per access (paper: lower than the 2^21 tree's)",
          o["row"] if o else None, o["log2_p_at_64A"] if o else None,
          f"{o['log2_p_at_64A']:.2f}" if o else None, "lower than 2^21 merge 3",
          o is not None and s21 is not None and o["log2_p_at_64A"] < s21["log2_p_at_64A"],
          complete=complete and all(find(rows, n, f, []) in fits for n, f in PAPER_LABEL))

    unfitted = sorted(l for l, s in per_row.items() if not s["fitted"])
    compared = [c for c in claims if c["status"] != "not compared"]
    return {"series": "steady op-max", "target_bits": target,
            "rows": per_row, "unfitted_rows": unfitted,
            "merging_at_2^21": merges, "figure_9b": fig9b,
            "n_sweep_worst": worst, "other_trees_worst": others,
            "claims": claims, "notes": list(dict.fromkeys(notes)),
            "missing": [c["id"] for c in claims if c["status"] == "missing"],
            "agrees_with_paper": bool(compared) and all(c["status"] == "agrees" for c in compared)}


def fmt(v, spec):
    return "-" if v is None else format(v, spec)


def render_text(s, export_dir):
    t = s["target_bits"]
    out = [f"Tree stash tail, {s['series']} (from {export_dir})",
           f"x = records left in the stash after an access; target 2^-{t} per access;",
           "A = the library's default stash registers for the row (64A slots; the engine "
           "overflows when x > 64A - 1).", ""]
    head = (f"{'row':12s} {'log2N':>5s} {'fold':>4s} {'L':>3s} {'seeds':>5s} {'max':>4s} "
            f"{'window':>7s} {'slope':>6s} {'k@2^-' + str(t):>8s} {'regs':>4s} {'A':>2s} "
            f"{'P@64A-1':>8s} {'P@64A':>8s} {'/2^31':>7s}")
    out += ["Per row (log2 probabilities; /2^31 is P@64A per 2^31 accesses):", head]
    for l, r in sorted(s["rows"].items(), key=lambda x: (x[1]["fold"], x[1]["log2_n"], x[0])):
        line = (f"{l:12s} {str(r['log2_n']):>5s} {r['fold']:4d} {r['leaf_bits']:3d} "
                f"{r['seeds']:5d} {fmt(r['max'], '4d')}")
        if not r["fitted"]:
            out.append(line + "  (tail too short to fit)")
            continue
        w = f"{r['window'][0]}..{r['window'][1]}"
        out.append(line + f" {w:>7s} {r['slope_bits_per_record']:6.3f} {r['k_at_target']:8.1f} "
                   f"{r['registers_for_k_at_target']:4d} {r['default_registers']:2d} "
                   f"{r['log2_p_at_64A_minus_1']:8.2f} {r['log2_p_at_64A']:8.2f} "
                   f"{r['log2_p_at_64A_per_2^31_accesses']:7.2f}")
    f9 = s["figure_9b"]
    out += ["", "Figure 9(b): measured stash size for 2^-lambda per access "
            "(smallest k with P[x >= k] <= 2^-lambda; '-' = not reached), fold 1, round-robin:",
            "  lambda " + "".join(f"{'2^' + str(n):>6s}" for n in f9["log2_n"])]
    for lam in f9["lambdas"]:
        out.append(f"  {lam:6d} " + "".join(f"{fmt(v, 'd'):>6s}" for v in f9["stash"][str(lam)]))
        if str(lam) in f9["paper"]:
            out.append(f"  {'paper':>6s} " + "".join(f"{fmt(v, 'd'):>6s}" for v in f9["paper"][str(lam)]))
    out.append("  seeds  " + "".join(f"{v:6d}" for v in f9["seeds"]))
    out += ["", "Paper numbers (Appendix A.3, A.4; Figure 9(b) cells above):"]
    for c in s["claims"]:
        if c["id"].startswith("Fig 9(b)"):
            continue
        verdict = "DIFFERS" if c["status"] == "differs" else c["status"]
        out.append(f"  {c['text']}: {c['shown'] or '-'} {c['unit']}".rstrip()
                   + f"  [{c['row'] or 'no row'}; paper {c['paper']}; {verdict}]")
    cells = [c for c in s["claims"] if c["id"].startswith("Fig 9(b)")]
    if cells:
        count = {st: [c["id"][9:] for c in cells if c["status"] == st]
                 for st in ("agrees", "differs", "missing")}
        out.append(f"  Figure 9(b): {len(count['agrees'])} of {len(cells)} cells agree"
                   + (f"; {len(count['differs'])} differ ({', '.join(count['differs'])})"
                      if count["differs"] else "")
                   + (f"; {len(count['missing'])} missing" if count["missing"] else ""))
    for scope, o in s["other_trees_worst"].items():
        out.append(f"  worst tree other than 2^21 merge 3 ({scope}): {o['row']}, "
                   f"{o['log2_p_at_64A']:.2f} at 64A, {o['log2_p_at_64A_minus_1']:.2f} at 64A-1")
    if s["unfitted_rows"]:
        out.append(f"  rows without a fit: {', '.join(s['unfitted_rows'])}")
    gaps = [i for i in s["missing"] if not i.startswith("Fig 9(b)")]
    if gaps:
        out.append(f"  missing (no row, no fit, or not reached): {', '.join(gaps)}")
    for n in s["notes"]:
        out.append(f"  note: {n}")
    out.append("")
    out.append("All paper numbers present and agreeing." if s["agrees_with_paper"]
               else "Not every paper number is present and agreeing.")
    return "\n".join(out) + "\n"


def plot(rows, fits, s, dest):
    """Figure 9 into dest/tree_stash_tail.{pdf,png}; False without matplotlib."""
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.lines import Line2D
    except ImportError:
        return False
    W, H = 261.82, 171.05  # points, as published (3.64 x 2.38 in)
    rc = {"font.family": "DejaVu Sans", "mathtext.fontset": "dejavusans", "font.size": 7,
          "axes.titlesize": 7.2, "axes.labelsize": 7.5, "xtick.major.size": 2.5,
          "ytick.major.size": 2.5, "xtick.major.pad": 1.5, "ytick.major.pad": 1.5,
          "legend.fontsize": 6, "pdf.fonttype": 42}
    with plt.rc_context(rc):
        fig = plt.figure(figsize=(W / 72, H / 72))
        a = fig.add_axes([42.42 / W, 55.47 / H, 91.19 / W, 97.07 / H])
        b = fig.add_axes([153.93 / W, 55.47 / H, 91.19 / W, 97.07 / H])
        # (a) Stash tail: every fourth measured k, and the fitted line over its window.
        handles, lowest, deepest = [], -40, 80
        for i in DRAW_ORDER:
            log2_n, fold, label, color, marker = FIG9A[i]
            row = find(rows, log2_n, fold, [])
            if row is None:
                continue
            pts = rows[row]["points"]
            start = 2 if fold == 1 else 4
            ks = [k for k in sorted(pts) if k >= start and (k - start) % 4 == 0]
            ys = [-pts[k][1] for k in ks]
            a.plot(ks, ys, ls="none", marker=marker, ms=2.6, color=color, mec="white",
                   mew=0.3, zorder=3)
            if row in fits:
                k0, k1 = int(fits[row]["window_k0"]), int(fits[row]["window_k1"])
                a.plot([k0, k1], [line_at(fits[row], k0), line_at(fits[row], k1)],
                       color=color, lw=1.1, zorder=2)
            if ys:
                lowest = min(lowest, math.floor(min(ys) / 10) * 10)
                deepest = max(deepest, math.ceil(max(ks) / 20) * 20)
        for i in range(len(FIG9A)):
            log2_n, fold, label, color, marker = FIG9A[i]
            if find(rows, log2_n, fold, []) is not None:
                handles.append(Line2D([], [], color=color, lw=1.1, marker=marker, ms=2.6,
                                      mec="white", mew=0.3, label=label))
        a.set_xlim(0, deepest)
        a.set_ylim(lowest, 1)
        ticks = list(range(0, lowest - 1, -10))
        a.set_yticks(ticks)  # set_*ticks(ticks, labels) needs matplotlib >= 3.5
        a.set_yticklabels(["1" if v == 0 else f"$2^{{{v}}}$" for v in ticks])
        a.set_xticks(range(0, deepest + 1, 20))
        a.grid(True, color="#b0b0b0", lw=0.45, alpha=0.25)
        a.set_axisbelow(True)
        a.set_xlabel("Records left in the stash, k")
        a.set_ylabel("Probability per access")
        a.set_title("(a) Stash tail")
        if handles:
            fig.legend(handles=handles, ncol=2 if len(handles) > 2 else 1,
                       loc="lower left", frameon=False,
                       bbox_to_anchor=(7.2 / W, 7.2 / H), handlelength=1.4,
                       handletextpad=0.3, columnspacing=0.7, labelspacing=0.15,
                       borderaxespad=0)
        else:
            a.text(0.5, 0.5, "no data", transform=a.transAxes, ha="center", va="center")
        # (b) Stash size needed, measured, fold 1.
        f9 = s["figure_9b"]
        top = 45
        bh = []
        for lam, color in zip(f9["lambdas"], RAMP * (1 + len(f9["lambdas"]) // len(RAMP))):
            pts = [(n, v) for n, v in zip(f9["log2_n"], f9["stash"][str(lam)]) if v is not None]
            b.plot([p[0] for p in pts], [p[1] for p in pts], color=color, lw=1.1, marker="o",
                   ms=2.6, mec="white", mew=0.3)
            bh.append(Line2D([], [], color=color, lw=1.1, marker="o", ms=2.6, mec="white",
                             mew=0.3, label=f"$2^{{-{lam}}}$"))
            if pts:
                top = max(top, math.ceil(max(p[1] for p in pts) / 5) * 5 + 5)
        if f9["log2_n"]:
            lo = min(f9["log2_n"]) - min(f9["log2_n"]) % 3
            xt = list(range(lo, max(f9["log2_n"]) + 1, 3))
            b.set_xticks(xt)
            b.set_xticklabels([f"$2^{{{n}}}$" for n in xt], fontsize=6.3)
            b.set_xlim(min(f9["log2_n"]) - 0.05 * (max(f9["log2_n"]) - min(f9["log2_n"]) or 15),
                       max(f9["log2_n"]) + 0.05 * (max(f9["log2_n"]) - min(f9["log2_n"]) or 15))
        else:
            b.text(0.5, 0.5, "no data", transform=b.transAxes, ha="center", va="center")
        b.set_ylim(0, top)
        b.set_yticks(range(0, top, 10))
        b.set_xlabel("Records N")
        b.set_title("(b) Stash size needed")
        fig.legend(handles=bh, ncol=len(bh), loc="lower center", frameon=False,
                   bbox_to_anchor=(199.5 / W, 9.3 / H), title="Overflow probability",
                   title_fontsize=6, handlelength=1.4, handletextpad=0.3,
                   columnspacing=0.7, borderaxespad=0)
        fig.savefig(os.path.join(dest, "tree_stash_tail.pdf"), metadata={"CreationDate": None})
        fig.savefig(os.path.join(dest, "tree_stash_tail.png"), dpi=300)
        plt.close(fig)
    return True


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("export_dir", help="a `run_stash_tail_long.py export` directory")
    ap.add_argument("--out", help="where to write (default: EXPORT_DIR)")
    ap.add_argument("--lambdas", default=",".join(map(str, LAMBDAS)),
                    help="Figure 9(b)'s overflow exponents (default 15,20,25,30)")
    ap.add_argument("--target-bits", type=int, default=TARGET_BITS,
                    help="per-access exponent for k at 2^-B (default 95, the paper's)")
    ap.add_argument("--no-figure", action="store_true", help="write the summary only")
    ap.add_argument("--check-paper", action="store_true",
                    help="exit 1 unless every paper number is present and agrees")
    a = ap.parse_args(argv)
    try:
        lambdas = tuple(int(x) for x in a.lambdas.split(",") if x.strip())
    except ValueError:
        ap.error(f"--lambdas: not a list of integers: {a.lambdas!r}")
    if not lambdas or any(lam <= 0 for lam in lambdas):
        ap.error("--lambdas: give positive integers")
    if a.target_bits <= 0:
        ap.error("--target-bits must be positive")
    for name in ("tail.csv", "fits.csv"):
        if not os.path.exists(os.path.join(a.export_dir, name)):
            sys.exit(f"{a.export_dir}/{name} not found; run `run_stash_tail_long.py export` first")
    rows, fits = load(a.export_dir)
    s = summarize(rows, fits, a.target_bits, lambdas)
    dest = a.out or a.export_dir
    os.makedirs(dest, exist_ok=True)
    text = render_text(s, a.export_dir)
    with open(os.path.join(dest, "stash_tail_summary.txt"), "w") as f:
        f.write(text)
    with open(os.path.join(dest, "stash_tail_summary.json"), "w") as f:
        json.dump(s, f, indent=1)
        f.write("\n")
    print(text, end="")
    if not a.no_figure:
        if plot(rows, fits, s, dest):
            print(f"wrote {dest}/tree_stash_tail.{{pdf,png}} and stash_tail_summary.{{txt,json}}")
        else:
            print(f"matplotlib not available: wrote {dest}/stash_tail_summary.{{txt,json}} only")
    if a.check_paper and not s["agrees_with_paper"]:
        sys.exit(1)


if __name__ == "__main__":
    main()
