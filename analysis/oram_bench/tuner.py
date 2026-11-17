"""The rebuild cost model's tuner: fit LevelArenaRebuildCost to one machine.

The level-arena benchmark's `--fit-rows` prints, per level and per run, the
model's features as the library counts them (LevelRebuildFeatures,
SaturatedProbeFeatures) beside what was measured, so nothing here re-derives a
geometry. `run_grid` drives the benchmark over a grid; `fit` turns rows into
the `rebuild_cost_*` override block a preset carries, and a report of every
row's measured against modelled cost. What is fitted:

- line, residual line, offer line and job terms: level cost per access =
  touch_lines x line + residual_lines x residual_line + offer_lines x
  offer_line + jobs x job, non-negative least squares on relative error, over
  rows whose groups run on one thread each (a helper's share is not in the
  owner's time). They are separate because they cost differently per line: a
  residual pass sweeps stash-sized pools that stay in cache, an offer merges a
  pool bucket into a main bucket, a route streams the level's tables. Rows
  that cannot separate a term (one routing, or rows from before the residual
  columns were printed) price it with the next coarser one. The slice line
  cost: the fitted line times the default model's margin, or the worst
  per-line cost among the rows the line term dominates if higher;
- the probe terms: requester time per access = buckets x per-bucket +
  bucket_lines x per-line, on scalar closed-loop runs that did not wait on the
  rebuild, then scaled down until the model's cost is at most every measured
  one. The model must give a rate at or above what one requester reaches: too
  high only cuts pieces finer, too low lets a piece outlast a window;
- the helper speedup s in 1 + s log2 m, from the top level's phase wall time
  (prepare + finish per job, `--stage-times`) across helper counts, and the
  top-thread cap: the largest measured m whose doubling still paid more than
  the thread gain floor. The cap is never extrapolated past what was measured.

The middle-level burst and the thread gain floor are not measurable this way
(the burst comes from deadline behaviour, the floor is a policy); they are
carried at the library's defaults and reported as such.
"""
from dataclasses import dataclass
import json
import math
import os
from pathlib import Path
import subprocess

from .codec import require

# The library's defaults (LevelArenaRebuildCost), for the unfitted fields and
# the collinear fallbacks.
DEFAULTS = {"line_picos": 845, "residual_line_picos": 397, "offer_line_picos": 1696, "job_nanos": 2659,
            "middle_burst_ppm": 300000, "helper_speedup_ppm": 550000,
            "max_top_threads": 8, "thread_gain_floor_ppm": 10000, "probe_bucket_picos": 20000,
            "probe_line_picos": 450, "slice_line_picos": 1500}
# A probe row whose requester parked on the rebuild for more than this share of
# its elapsed time measured the rebuild, not the probe.
PROBE_WAIT_SHARE = 0.02
# The slice budget keeps the default model's margin over the average line
# cost (its slice_line_picos over line_picos, a calibration choice), and rises
# further only where a row the line term dominates (job share under
# SLICE_JOB_SHARE) measured worse.
SLICE_MARGIN = DEFAULTS["slice_line_picos"] / DEFAULTS["line_picos"]
SLICE_JOB_SHARE = 0.1


def parse_rows(text):
    """The FIT_ROW JSON lines of benchmark output (anything else is ignored)."""
    rows = []
    for line in text.splitlines():
        if line.startswith("FIT_ROW "):
            row = json.loads(line[len("FIT_ROW "):])
            require(row.get("fit_row") in ("run", "level"), "unknown fit row kind")
            rows.append(row)
    return rows


def _nnls2(xs, ys, targets, weights):
    """min sum w (t - a x - b y)^2 with a, b >= 0; None where the columns are collinear."""
    sxx = sum(w * x * x for x, w in zip(xs, weights))
    syy = sum(w * y * y for y, w in zip(ys, weights))
    sxy = sum(w * x * y for x, y, w in zip(xs, ys, weights))
    sxt = sum(w * x * t for x, t, w in zip(xs, targets, weights))
    syt = sum(w * y * t for y, t, w in zip(ys, targets, weights))
    determinant = sxx * syy - sxy * sxy
    if sxx <= 0 or syy <= 0 or determinant <= 1e-9 * sxx * syy:
        return None
    a, b = (sxt * syy - syt * sxy) / determinant, (syt * sxx - sxt * sxy) / determinant
    if a < 0:
        a, b = 0.0, max(0.0, syt / syy)
    elif b < 0:
        a, b = max(0.0, sxt / sxx), 0.0
    return a, b


def _solve(matrix, vector):
    """Gaussian elimination with partial pivoting; None when singular."""
    n = len(vector)
    a = [list(row) + [v] for row, v in zip(matrix, vector)]
    scale = max(abs(x) for row in matrix for x in row) or 1.0
    for c in range(n):
        pivot = max(range(c, n), key=lambda r: abs(a[r][c]))
        if abs(a[pivot][c]) <= 1e-12 * scale:
            return None
        a[c], a[pivot] = a[pivot], a[c]
        for r in range(n):
            if r != c:
                f = a[r][c] / a[c][c]
                a[r] = [x - f * y for x, y in zip(a[r], a[c])]
    return [a[i][n] / a[i][i] for i in range(n)]


def _nnls(columns, targets, weights):
    """min sum w (t - sum_j c_j col_j)^2 with every c_j >= 0; None where the columns are collinear.

    Exact, by trying every active set: there are a handful of columns.
    """
    n = len(columns)
    gram = [[sum(w * a * b for a, b, w in zip(columns[i], columns[j], weights)) for j in range(n)]
            for i in range(n)]
    rhs = [sum(w * a * t for a, t, w in zip(columns[i], targets, weights)) for i in range(n)]
    diagonal = [gram[i][i] for i in range(n)]
    if min(diagonal) <= 0:
        return None
    # Conditioning on the correlation matrix, so the columns' units do not matter
    # (for two columns this is _nnls2's test).
    correlation = [[gram[i][j] / math.sqrt(diagonal[i] * diagonal[j]) for j in range(n)] for i in range(n)]
    if _det(correlation) <= 1e-9:
        return None
    best = None
    for mask in range(1, 1 << n):
        active = [j for j in range(n) if mask >> j & 1]
        solved = _solve([[gram[i][j] for j in active] for i in active], [rhs[i] for i in active])
        if solved is None or min(solved) < 0:
            continue
        c = [0.0] * n
        for j, v in zip(active, solved):
            c[j] = v
        # The weighted squared error less its constant t'Wt.
        error = sum(c[i] * c[j] * gram[i][j] for i in range(n) for j in range(n)) - 2 * sum(
            c[i] * rhs[i] for i in range(n))
        if best is None or error < best[0]:
            best = (error, c)
    return None if best is None else best[1]


def _det(m):
    """Determinant by elimination with partial pivoting."""
    a = [list(row) for row in m]
    n, det = len(a), 1.0
    for c in range(n):
        pivot = max(range(c, n), key=lambda r: abs(a[r][c]))
        if a[pivot][c] == 0:
            return 0.0
        if pivot != c:
            a[c], a[pivot] = a[pivot], a[c]
            det = -det
        det *= a[c][c]
        for r in range(c + 1, n):
            f = a[r][c] / a[c][c]
            a[r] = [x - f * y for x, y in zip(a[r], a[c])]
    return det


def _scale(xs, ys, targets, weights, a, b):
    """The one factor k minimising sum w (t - k (a x + b y))^2: the collinear fallback."""
    model = [a * x + b * y for x, y in zip(xs, ys)]
    denominator = sum(w * m * m for m, w in zip(model, weights))
    require(denominator > 0, "no modelled work in the fit rows")
    return sum(w * m * t for m, t, w in zip(model, targets, weights)) / denominator


def _shape(row):
    return (row["capacity"], row["key_bytes"], row["value_bytes"], row["branching"])


@dataclass(frozen=True)
class Fit:
    cost: dict        # every LevelArenaRebuildCost field, fitted or default
    fitted: list      # the fields the rows determined
    report: dict      # per-row residuals and what each fit used


@dataclass(frozen=True)
class RebuildTerms:
    line_picos: int           # per routing line
    residual_line_picos: int  # per line a residual pass sweeps
    offer_line_picos: int     # per line an offer merges into the main
    job_nanos: int
    slice_line_picos: int
    method: str
    residuals: list


# The column groupings tried in order: every term apart, then offers priced
# with the residual sweeps, then every line at one cost. A grouping's members
# share one fitted constant.
_GROUPINGS = [("least_squares", [["line"], ["residual"], ["offer"], ["job"]]),
              ("least_squares_residual_as_one", [["line"], ["residual", "offer"], ["job"]]),
              ("least_squares_one_line", [["line", "residual", "offer"], ["job"]])]


def fit_rebuild_terms(rows):
    """The rebuild terms (RebuildTerms) from level rows with one thread per group.

    Every term is fitted apart when the rows separate them; otherwise the
    offers share the residual sweeps' cost, then every line one cost (rows from
    before the residual columns were printed), and with one shape the defaults'
    ratios are scaled. The slice line cost is the fitted routing line times
    the default model's margin (SLICE_MARGIN), or the worst line cost among
    the rows the routing's line term dominates if that is higher: a piece
    budgeted below what its lines cost overruns its window.
    """
    usable = [r for r in rows if r["fit_row"] == "level" and r["top_helpers"] == 0 and r["owners"] > 0 and
              r["jobs"] > 0 and r["measured_ns_per_access"] > 0 and not r["batch"]]
    require(usable, "no level rows with owner threads and no helpers to fit the line and job terms")
    features = {"line": [r["touch_lines_per_access"] for r in usable],
                "residual": [r.get("residual_lines_per_access", 0.0) for r in usable],
                "offer": [r.get("offer_lines_per_access", 0.0) for r in usable],
                "job": [r["jobs_per_access"] for r in usable]}
    targets = [r["measured_ns_per_access"] for r in usable]
    weights = [1.0 / (t * t) for t in targets]  # relative error: every level counts alike
    cost = None
    for method, grouping in _GROUPINGS:
        columns = [[sum(features[name][i] for name in group) for i in range(len(usable))] for group in grouping]
        if not all(any(column) for column in columns):
            continue  # a term every row leaves at zero cannot be fitted
        solved = _nnls(columns, targets, weights)
        if solved is not None:
            cost = {name: c for group, c in zip(grouping, solved) for name in group}
            break
    if cost is None:
        # One shape cannot separate the terms; keep the defaults' ratio.
        lines = [features["line"][i] + features["residual"][i] + features["offer"][i] for i in range(len(usable))]
        k = _scale(lines, features["job"], targets, weights, DEFAULTS["line_picos"] / 1000.0, DEFAULTS["job_nanos"])
        line = k * DEFAULTS["line_picos"] / 1000.0
        cost, method = {"line": line, "residual": line, "offer": line, "job": k * DEFAULTS["job_nanos"]}, \
            "scaled_defaults"
    def model(i):
        return sum(cost[name] * features[name][i] for name in features)
    residuals = [{"shape": list(_shape(r)), "level": r["level"], "levels": r["levels"],
                  "measured_ns_per_access": r["measured_ns_per_access"],
                  "fitted_ns_per_access": model(i), "ratio": model(i) / targets[i]}
                 for i, r in enumerate(usable)]
    # Only rows the routing's line term clearly dominates say what a line
    # costs; in a job- or residual-heavy row (level 1) the "implied" line cost
    # absorbs the other terms' misfit.
    implied = []
    for i in range(len(usable)):
        rest = model(i) - cost["line"] * features["line"][i]
        if features["line"][i] > 0 and rest < SLICE_JOB_SHARE * targets[i]:
            implied.append((targets[i] - rest) / features["line"][i])
    slice_line = max([cost["line"] * SLICE_MARGIN] + implied)
    return RebuildTerms(round(cost["line"] * 1000), round(cost["residual"] * 1000), round(cost["offer"] * 1000),
                        round(cost["job"]), round(slice_line * 1000), method, residuals)


def fit_probe_terms(rows):
    """(probe_bucket_picos, probe_line_picos, method, residuals) from scalar closed-loop runs."""
    usable = [r for r in rows if r["fit_row"] == "run" and not r["write_only"] and not r["batch"] and
              not r["offered_kops"] and r["accesses"] > 0 and r["seconds"] > 0 and
              r["requester_park_nanos"] <= PROBE_WAIT_SHARE * r["seconds"] * 1e9]
    require(usable, "no scalar closed-loop run rows free of rebuild waits to fit the probe terms")
    xs = [r["probe_buckets"] for r in usable]
    ys = [r["probe_bucket_lines"] for r in usable]
    targets = [r["seconds"] * 1e9 / r["accesses"] for r in usable]
    weights = [1.0 / (t * t) for t in targets]
    solved = _nnls2(xs, ys, targets, weights)
    if solved is None:
        k = _scale(xs, ys, targets, weights, DEFAULTS["probe_bucket_picos"] / 1000.0,
                   DEFAULTS["probe_line_picos"] / 1000.0)
        bucket, line = k * DEFAULTS["probe_bucket_picos"] / 1000.0, k * DEFAULTS["probe_line_picos"] / 1000.0
        method = "scaled_defaults"
    else:
        (bucket, line), method = solved, "least_squares"
    # At or ABOVE every measured rate: the modelled cost may not exceed any measured one.
    envelope = min(t / (bucket * x + line * y) for x, y, t in zip(xs, ys, targets))
    bucket, line = bucket * min(1.0, envelope), line * min(1.0, envelope)
    residuals = [{"shape": list(_shape(r)), "measured_ns_per_access": t,
                  "modelled_ns_per_access": bucket * x + line * y,
                  "modelled_rate_over_measured": t / (bucket * x + line * y)}
                 for r, x, y, t in zip(usable, xs, ys, targets)]
    return max(1, round(bucket * 1000)), round(line * 1000), method + "+envelope", residuals


def fit_helpers(rows, gain_floor_ppm=DEFAULTS["thread_gain_floor_ppm"]):
    """(helper_speedup_ppm, max_top_threads, curves) from the top level's phase wall time, or None."""
    tops = [r for r in rows if r["fit_row"] == "level" and r["level"] == r["levels"] and
            "finish_wall_nanos" in r and r["finishes"] > 0 and r["prepares"] > 0 and
            (r["top_helpers"] == 0 or r["takes_lanes"])]
    curves = {}
    for r in tops:
        wall = r["prepare_wall_nanos"] / r["prepares"] + r["finish_wall_nanos"] / r["finishes"]
        curves.setdefault(_shape(r), {}).setdefault(1 + r["top_helpers"], []).append(wall)
    points, report = [], []
    for shape, curve in sorted(curves.items()):
        if 1 not in curve or len(curve) < 2:
            continue
        base = sorted(curve[1])[len(curve[1]) // 2]
        speedups = {m: base / sorted(walls)[len(walls) // 2] for m, walls in curve.items()}
        points.extend((m, speedup) for m, speedup in speedups.items() if m > 1)
        report.append({"shape": list(shape), "speedup_by_threads": {str(m): speedups[m] for m in sorted(speedups)}})
    if not points:
        return None
    s = sum((sp - 1.0) * math.log2(m) for m, sp in points) / sum(math.log2(m) ** 2 for m, _ in points)
    # The cap: on the largest shape (the most bandwidth-bound top), the largest
    # measured m whose step from the previous measured m still paid.
    largest = max(report, key=lambda item: item["shape"][0])["speedup_by_threads"]
    ms = sorted(int(m) for m in largest)
    cap = ms[0]
    for previous, m in zip(ms, ms[1:]):
        if largest[str(m)] > largest[str(previous)] * (1 + gain_floor_ppm / 1e6):
            cap = m
        else:
            break
    return max(0, round(s * 1e6)), max(1, cap), report


def fit(rows):
    terms = fit_rebuild_terms(rows)
    bucket, probe_line, probe_method, probe_residuals = fit_probe_terms(rows)
    cost = dict(DEFAULTS, line_picos=terms.line_picos, residual_line_picos=terms.residual_line_picos,
                offer_line_picos=terms.offer_line_picos, job_nanos=terms.job_nanos,
                probe_bucket_picos=bucket, probe_line_picos=probe_line,
                slice_line_picos=max(1, terms.slice_line_picos))
    require(terms.line_picos > 0 or terms.residual_line_picos > 0 or terms.offer_line_picos > 0 or
            terms.job_nanos > 0, "the fit priced no rebuild work")
    fitted = ["line_picos", "residual_line_picos", "offer_line_picos", "job_nanos", "slice_line_picos",
              "probe_bucket_picos", "probe_line_picos"]
    helpers = fit_helpers(rows)
    helper_report = None
    if helpers is not None:
        cost["helper_speedup_ppm"], cost["max_top_threads"], helper_report = helpers
        fitted += ["helper_speedup_ppm", "max_top_threads"]
    report = {"rebuild": {"method": terms.method, "rows": terms.residuals},
              "probe": {"method": probe_method, "rows": probe_residuals},
              "helpers": helper_report,
              "not_fitted": sorted(set(DEFAULTS) - set(fitted)),
              "note": "Validate on held-out capacities before adopting the fit. The burst and the gain "
                      "floor stay at the library's defaults."}
    return Fit(cost, fitted, report)


def override_block(result):
    """The preset override block: only the fitted fields, so defaults stay automatic.

    The helper fields apply only under a rebuild thread budget (the resolver
    refuses them next to an explicit owner count), so a candidate that pins
    `owner_threads` takes the block without them.
    """
    return {"incremental": {"rebuild_cost_" + name: result.cost[name] for name in result.fitted}}


def fit_record(rows, source):
    """What `fit-rebuild` writes: the block, the whole model, and the report."""
    result = fit(rows)
    return {"rebuild_cost_fit_schema_version": 1, "rows": len(rows), "source": source,
            "override": override_block(result), "cost": result.cost, "fitted": result.fitted,
            "report": result.report}


# The measurement grid. `target` is sized for a 16-core target (tens of
# minutes); `quick` is a short check of a small machine against the defaults. The
# helper counts are an upper list: `grid_commands` keeps those that fit the
# host's physical cores beside the requester and owners and the 64 rebuild
# lanes, and adds the widest valid count, without two threads sharing a core.
GRIDS = {
    "quick": {"rebuild": [(8, 1 << 22, 16), (8, 1 << 25, 16)],
              "probe": [(8, 1 << 18, 16), (8, 1 << 18, 256)], "helpers": []},
    "target": {"rebuild": [(b, c, v) for b in (4, 8) for c in (1 << 20, 1 << 22, 1 << 24, 1 << 25)
                           for v in (16, 48)],
               "probe": [(b, 1 << 18, v) for b in (4, 8) for v in (16, 256)],
               "helpers": [(8, c, 16, h) for c in (1 << 22, 1 << 25) for h in (0, 1, 3, 7, 15)]},
}


def physical_core_slots():
    """One allowed CPU per exposed physical core (this process's mask), or None
    where the host does not expose core identity."""
    from .doctor import _text
    from .topology import capture_topology
    allowed = sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else []
    return capture_topology(allowed, _text).physical_core_slots


def grid_commands(benchmark, grid, owners=3, reps=1, place=True, core_slots=None):
    """The benchmark invocations of one grid, as argument lists.

    The helper rows run the requester, `owners` owner threads and the helpers
    each on a physical core of its own, pinned with `--cpus` to `core_slots`
    (one CPU per core, from `physical_core_slots`) rather than placed near/far:
    a far domain of eight cores cannot hold the top's helpers, and a
    single-domain host places nothing, which lets them share SMT siblings.
    """
    require(grid in GRIDS, f"unknown grid {grid!r}; choose one of {sorted(GRIDS)}")
    base = [str(benchmark), "--key", "8", "--owners", str(owners), "--reps", str(reps), "--fit-rows"]
    common = base + (["--place"] if place else [])
    commands = []
    for branching, capacity, value in GRIDS[grid]["rebuild"] + GRIDS[grid]["probe"]:
        commands.append(common + ["--branching", str(branching), "--capacity", str(capacity),
                                  "--value", str(value)])
    rows = GRIDS[grid]["helpers"]
    if rows:
        require(core_slots is not None,
                "the helper rows pin one thread per physical core, and this host does not expose "
                "physical-core identity; run the quick grid, or fit from rows measured elsewhere")
        widest = len(core_slots) - 1 - owners
        require(widest >= 0, f"{len(core_slots)} physical cores cannot hold the requester and {owners} owners")
        # Two rebuild lanes per thread, within the engine's 64-lane limit.
        widest = min(widest, 31)
    for branching, capacity, value in dict.fromkeys(row[:3] for row in rows):
        counts = sorted({h for b, c, v, h in rows if (b, c, v) == (branching, capacity, value) and h <= widest} |
                        ({widest} if widest > 0 else set()))
        for helpers in counts:
            # Write-only, so the rebuild binds; twice as many lanes as threads.
            lanes = max(8, 2 * (1 + helpers))
            cpus = ",".join(str(cpu) for cpu in core_slots[:1 + owners + helpers])
            commands.append(base + ["--cpus", cpus, "--branching", str(branching), "--capacity", str(capacity),
                                    "--value", str(value), "--write-only", "--stage-times",
                                    "--rebuild-lanes", str(lanes), "--top-helpers", str(helpers)])
    return commands


def run_grid(benchmark, grid, rows_path, owners=3, reps=1, place=True, core_slots=None):
    """Run a grid, appending each run's FIT_ROW lines to `rows_path` as JSON lines."""
    benchmark = Path(benchmark).resolve(strict=True)
    rows_path = Path(rows_path)
    if core_slots is None and GRIDS.get(grid, {}).get("helpers"):
        core_slots = physical_core_slots()
    total = 0
    for command in grid_commands(benchmark, grid, owners, reps, place, core_slots):
        result = subprocess.run(command, capture_output=True, text=True, timeout=3600)
        require(result.returncode == 0, f"benchmark failed ({' '.join(command[1:])}): {result.stderr.strip()}")
        rows = parse_rows(result.stdout)
        require(rows, "the benchmark printed no FIT_ROW lines; rebuild it with --fit-rows support")
        with open(rows_path, "a") as stream:
            for row in rows:
                stream.write(json.dumps(row, sort_keys=True) + "\n")
        total += len(rows)
    return total


def load_rows(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]
