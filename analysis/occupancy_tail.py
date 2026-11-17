#!/usr/bin/env python3
"""Occupancy reducer: occupancy distributions and block-based empirical tails.

Reads the JSON of ``cpu_byteslice_occupancy_observer`` and reports, for every
structure identity (kind, level, index): capacity, exposure count, maximum
occupancy, maximum load %, the occupancy histogram and the empirical
exceedance P(occupancy >= k).

INDEPENDENCE.  Exposures are not independent samples: the stashes of one
rebuild job are one correlated snapshot set (they route the same records),
and consecutive jobs of a level share most of their live keys.  So the
reducer never treats exposures as samples for an interval.  Its unit is a
BLOCK: ``--block-jobs M`` consecutive jobs of the structure's level (default
8), summarised by the largest occupancy any exposure of the structure had in
the block.  P(block max >= k) is estimated by the fraction of blocks reaching
k and bounded above by a one-sided Clopper-Pearson bound (exact binomial,
confidence ``--confidence``, default 0.95) on the count of blocks that did.
That is a bound on a per-block exceedance probability under the ASSUMPTION
that distinct blocks are independent draws; jobs use fresh hash nonces, so the
dependence between blocks is only through the shared live key set, but that is
an assumption and is stated in every report.  The per-exposure fraction is
kept beside it as a point estimate only.

WHAT ZERO OVERFLOWS MEAN.  The engine's capacities are fixed and an overflow
is a thrown failure, so an observed run can only report "no overflow in n
blocks".  That bounds the per-block overflow probability by about
-ln(1 - confidence)/n (about 3/n at 95 %), nowhere near 2^-64, and says
nothing about the certificate's conditional bound.  Nothing here fits or
extrapolates a tail.

``--certificate configuration_space_2pK.json`` compares the capacities with
the certified candidate of the same (levels, r0, D, ladder): the certificate
records per-level stash and tier BUCKET counts (capacity = 64 x buckets) and
a composed bound per shape, but no per-structure occupancy law, so the
comparison is capacity equality plus the shape's composed bound.
"""

import argparse
import json
import math
import sys
from pathlib import Path

BUCKET = 64


# --------------------------------------------------------------------------
# Exact binomial upper confidence bound (Clopper-Pearson), no dependencies
# --------------------------------------------------------------------------

def _betacf(a, b, x):
    tiny = 1e-300
    qab, qap, qam = a + b, a + 1.0, a - 1.0
    c, d = 1.0, 1.0 - qab * x / qap
    d = tiny if abs(d) < tiny else d
    d = 1.0 / d
    h = d
    for m in range(1, 10000):
        m2 = 2 * m
        aa = m * (b - m) * x / ((qam + m2) * (a + m2))
        d = 1.0 + aa * d
        d = tiny if abs(d) < tiny else d
        c = 1.0 + aa / c
        c = tiny if abs(c) < tiny else c
        d = 1.0 / d
        h *= d * c
        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))
        d = 1.0 + aa * d
        d = tiny if abs(d) < tiny else d
        c = 1.0 + aa / c
        c = tiny if abs(c) < tiny else c
        d = 1.0 / d
        delta = d * c
        h *= delta
        if abs(delta - 1.0) < 3e-16:
            break
    return h


def betainc(a, b, x):
    """Regularised incomplete beta I_x(a, b)."""
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    ln_front = (math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b)
                + a * math.log(x) + b * math.log1p(-x))
    front = math.exp(ln_front)
    if x < (a + 1.0) / (a + b + 2.0):
        return front * _betacf(a, b, x) / a
    return 1.0 - front * _betacf(b, a, 1.0 - x) / b


def binom_cdf(k, n, p):
    """P(X <= k) for X ~ Binomial(n, p)."""
    if k < 0:
        return 0.0
    if k >= n:
        return 1.0
    return 1.0 - betainc(k + 1, n - k, p)


def clopper_pearson_upper(k, n, confidence):
    """One-sided upper bound p_u with P(X <= k | p_u) = 1 - confidence."""
    if n <= 0:
        return 1.0
    if k >= n:
        return 1.0
    alpha = 1.0 - confidence
    if k == 0:
        return 1.0 - alpha ** (1.0 / n)
    lo, hi = k / n, 1.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if binom_cdf(k, n, mid) > alpha:
            lo = mid
        else:
            hi = mid
    return hi


# --------------------------------------------------------------------------
# Reduction
# --------------------------------------------------------------------------

def blocks_of(job_max, block_jobs):
    """Block maxima over consecutive groups of `block_jobs` jobs.  A trailing
    partial block is dropped, so every block has the same exposure."""
    n = len(job_max) // block_jobs
    return [max(job_max[i * block_jobs:(i + 1) * block_jobs]) for i in range(n)]


def exceedance_rows(hist, events, block_max, confidence):
    """Rows for every threshold k from the smallest observed occupancy up to
    max + 1: per-exposure fraction, and the block count / fraction / CP upper
    bound of block maxima >= k."""
    observed = [k for k, c in enumerate(hist) if c]
    if not observed:
        return []
    top = observed[-1]
    nblocks = len(block_max)
    rows = []
    at_or_above = events
    below = 0
    for k in range(observed[0], top + 2):
        if k > observed[0]:
            below += hist[k - 1] if k - 1 < len(hist) else 0
            at_or_above = events - below
        blocks = sum(1 for m in block_max if m >= k)
        row = {
            "k": k,
            "exposures": at_or_above,
            "exposure_fraction": at_or_above / events if events else 0.0,
            "blocks": blocks,
            "n_blocks": nblocks,
            "block_fraction": blocks / nblocks if nblocks else None,
            "block_upper": (clopper_pearson_upper(blocks, nblocks, confidence)
                            if nblocks else None),
        }
        rows.append(row)
    return rows


def reduce_structure(st, block_jobs, confidence):
    cap = st["capacity"]
    hist = st["hist"]
    events = st["events"]
    jobs = st["job_max"]
    bm = blocks_of(jobs, block_jobs)
    rows = exceedance_rows(hist, events, bm, confidence)
    out = {
        "kind": st["kind"], "level": st["level"], "index": st["index"],
        "capacity": cap, "events": events, "jobs": len(jobs),
        "n_blocks": len(bm), "max": st["max"],
        "max_load_pct": 100.0 * st["max"] / cap if cap else None,
        "overflows": st.get("overflows", 0),
        "histogram": {str(k): c for k, c in enumerate(hist) if c},
        "exceedance": rows,
        # The overflow event itself: block max >= capacity + 1 is not
        # representable, so the bound is for "reaching capacity" (full) too.
        "full_blocks": sum(1 for m in bm if m >= cap),
    }
    out["full_upper"] = (clopper_pearson_upper(out["full_blocks"], len(bm),
                                               confidence) if bm else None)
    # The count-based bound for "an overflow in a block", given none was seen.
    out["overflow_block_upper"] = (clopper_pearson_upper(
        min(out["overflows"], len(bm)), len(bm), confidence) if bm else None)
    return out


def group_key(s):
    return (s["kind"], s["level"], s["index"])


def reduce_report(doc, block_jobs=8, confidence=0.95):
    if doc.get("schema") != "occupancy_observer_v1":
        raise ValueError("not an occupancy_observer_v1 document")
    if block_jobs < 1:
        raise ValueError("block_jobs must be at least 1")
    structures = [reduce_structure(s, block_jobs, confidence)
                  for s in sorted(doc["structures"], key=group_key)]
    meta = doc["meta"]
    return {
        "meta": meta,
        "block_jobs": block_jobs,
        "confidence": confidence,
        "interval": ("one-sided Clopper-Pearson upper bound on the fraction of "
                     "blocks of %d consecutive jobs whose maximum reaches k; "
                     "blocks assumed independent" % block_jobs),
        "caveat": ("zero overflows do not establish 2^-64; a run of n blocks "
                   "bounds the per-block overflow probability by about 3/n at "
                   "95 percent"),
        "structures": structures,
    }


# --------------------------------------------------------------------------
# Certificate comparison
# --------------------------------------------------------------------------

def certificate_capacities(cert_doc, meta):
    """Candidates of the certificate with the run's (levels, r0, D, ladder)."""
    ladder = meta.get("level_fanouts")
    found = []
    for cand in cert_doc.get("candidates", []):
        if (cand.get("levels") == meta.get("levels")
                and cand.get("prefix_flushes") == meta.get("prefix_flushes")
                and cand.get("top_digit") == meta.get("top_digit")):
            if ladder and cand.get("level_fanouts") not in (None, ladder):
                continue
            found.append(cand)
    return found


def compare_certificate(report, cert_doc):
    meta = report["meta"]
    cands = certificate_capacities(cert_doc, meta)
    if not cands:
        return {"matched": False,
                "note": "no certificate candidate has this shape"}
    cand = cands[0]
    rows = []
    for s in report["structures"]:
        lvl = s["level"]
        want = None
        if s["kind"] in ("stage_stash", "radix_stash", "merge_stash",
                         "retained_carry"):
            want = cand["stash_buckets"][lvl - 1] * BUCKET
        elif s["kind"] == "final_tier":
            want = cand["level_tier_buckets"][lvl - 1] * BUCKET
        rows.append({"kind": s["kind"], "level": lvl, "index": s["index"],
                     "engine_capacity": s["capacity"],
                     "certificate_capacity": want,
                     "equal": None if want is None else want == s["capacity"]})
    return {
        "matched": True, "candidate": cand.get("name"),
        "composed_bound_log2": cand.get("conditional_lifetime_log2_display"),
        "status": cand.get("status"), "rows": rows,
        "all_capacities_equal": all(r["equal"] for r in rows
                                    if r["equal"] is not None),
        "note": ("range leaves have capacity 64 x stacked pages and are "
                 "certified by the coarse-range event of the shape, not by a "
                 "bucket count recorded here"),
    }


# --------------------------------------------------------------------------
# Text report
# --------------------------------------------------------------------------

def render_text(report, cert=None, max_rows=6):
    m = report["meta"]
    lines = []
    lines.append("capacity %s (requested %s), K%s/V%s, B=%s r0=%s D=%s L=%s,"
                 " ladder %s" % (m["capacity"], m["requested_capacity"],
                                 m["key_bytes"], m["value_bytes"],
                                 m["branching"], m["prefix_flushes"],
                                 m["top_digit"], m["levels"],
                                 m.get("level_fanouts")))
    lines.append("mode: %s; workload %s (%s%% updates); settle %s, observed %s"
                 " accesses; certificate status %s (%s)" % (
                     m["mode"], m["workload"], m["update_percent"],
                     m["settle_accesses"], m["observed_accesses"],
                     m.get("certification_status"),
                     m.get("certification_bound_log2")))
    if m.get("failure"):
        lines.append("RUN STOPPED: %s (natural_overflow=%s)" % (
            m["failure"], m.get("natural_overflow")))
    lines.append(report["interval"])
    lines.append(report["caveat"])
    lines.append("")
    hdr = "%-20s %3s %3s %5s %9s %4s %6s %5s %7s  %s" % (
        "kind", "lvl", "idx", "cap", "exposures", "max", "load%", "jobs",
        "blocks", "tail P(block max >= k): k count/blocks upper")
    lines.append(hdr)
    for s in report["structures"]:
        tail = [r for r in s["exceedance"] if r["k"] >= max(0, s["max"] - 2)]
        parts = ["%d:%d/%d<=%.2e" % (r["k"], r["blocks"], r["n_blocks"],
                                      r["block_upper"])
                 for r in tail[:max_rows] if r["block_upper"] is not None]
        lines.append("%-20s %3d %3d %5d %9d %4d %6.1f %5d %7d  %s" % (
            s["kind"], s["level"], s["index"], s["capacity"], s["events"],
            s["max"], s["max_load_pct"] or 0.0, s["jobs"], s["n_blocks"],
            " ".join(parts)))
    if cert is not None:
        lines.append("")
        if not cert["matched"]:
            lines.append("certificate: " + cert["note"])
        else:
            lines.append("certificate candidate %s, composed bound 2^%s: "
                         "capacities equal for every comparable structure: %s"
                         % (cert["candidate"], cert["composed_bound_log2"],
                            cert["all_capacities_equal"]))
            for r in cert["rows"]:
                if r["equal"] is False:
                    lines.append("  MISMATCH %s level %d index %d: engine %s,"
                                 " certificate %s" % (
                                     r["kind"], r["level"], r["index"],
                                     r["engine_capacity"],
                                     r["certificate_capacity"]))
    return "\n".join(lines)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("input", help="observer JSON")
    ap.add_argument("--block-jobs", type=int, default=8)
    ap.add_argument("--confidence", type=float, default=0.95)
    ap.add_argument("--certificate", help="configuration_space_2pK.json")
    ap.add_argument("--json", action="store_true", help="print JSON, not text")
    ap.add_argument("--rows", type=int, default=6,
                    help="tail rows per structure in the text report")
    args = ap.parse_args(argv)
    doc = json.loads(Path(args.input).read_text())
    report = reduce_report(doc, args.block_jobs, args.confidence)
    cert = None
    if args.certificate:
        cert = compare_certificate(report, json.loads(
            Path(args.certificate).read_text()))
        report["certificate"] = cert
    if args.json:
        json.dump(report, sys.stdout, indent=1)
        print()
    else:
        print(render_text(report, cert, args.rows))
    return 0


if __name__ == "__main__":
    sys.exit(main())
