"""A 1-second throughput/latency series from one committed full-event attempt.

The per-request records come from the C++ reducer's `--events --format raw-csv`
export, which validates each record before printing it and the cohort's
completeness at the end; requests.csv is written to a partial file while the
records stream and published only after the replay passed (a failing replay
publishes nothing). One pass, and memory independent of the request count: see
`export`. Nothing here re-derives a statistic the live worker reported: the
series is a view of the raw events, binned by completion time.
"""
from contextlib import closing
import csv
import math
from pathlib import Path
import subprocess

from .codec import load_json, require
from .store import atomic_json, verify

SERIES_SCHEMA_VERSION = 1
NS_PER_S = 1_000_000_000
# Maintenance spans the worker retained as worker/markers.csv (role,level,start_ns,
# end_ns on the trial clock): ours from the top-merge log, H2O2RAM's bracketed
# rebuild accesses. worker.json maintenance_markers says why a backend has none.
MARKERS_ARTIFACT = "worker/markers.csv"
MARKER_COLUMNS = ["start_s", "end_s", "role", "level"]
REQUEST_COLUMNS = ["request_id", "status", "arrival_ns", "dispatch_ns", "completion_ns", "response_us", "queue_us",
                   "service_us", "batch_id"]
SERIES_COLUMNS = ["interval_start_s", "interval_end_s", "completions", "throughput_ops_per_second", "response_p50_us",
                  "response_p99_us", "response_max_us", "p99_sufficient_samples"]
MARKERS_UNAVAILABLE = ("the worker emits no maintenance start/end events; worker.json maintenance_coverage counts "
                       "access-count-derived carries only, which do not prove a completed rebuild")
OUTCOMES = {0: "rejected", 1: "timed_out", 2: "outstanding"}
PLOT_POINT_CAP = 200_000


def raw_events(reducer, chunks):
    """Yield (kind, fields) per raw-csv record in log order, then raise if the replay failed.

    The reducer validates each chunk's records before printing them, so every
    record seen here already passed the per-record checks; only completeness
    (the trial end) is known at the end, so publish nothing before this is
    exhausted. It runs in the chunks' directory on bare file names: thousands
    of absolute paths overflow ARG_MAX.
    """
    chunks = [Path(c) for c in chunks]
    directory = chunks[0].parent
    require(all(c.parent == directory for c in chunks), "event chunks must share one directory")
    command = [str(Path(reducer).resolve()), "--events", "--format", "raw-csv", *(c.name for c in chunks)]
    with subprocess.Popen(command, cwd=directory, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                          start_new_session=True) as process:
        try:
            rows = csv.reader(process.stdout)
            next(rows, None)  # header
            for row in rows:
                yield int(row[1]), row[2:]
            stderr = process.stderr.read()
        except BaseException:
            process.kill()
            raise
    require(process.returncode == 0, "raw replay failed: " + stderr)


def quantile(sorted_values, q):
    """Nearest rank on the exact values; unlike the reducer's histogram it is not bucketed."""
    return sorted_values[max(0, math.ceil(q * len(sorted_values)) - 1)]


class Series:
    """One row per interval of [0, horizon) by completion time; the last interval may be short.

    Only the open interval's responses are held. Completions must come in
    interval order, which the worker's single caller loop gives (each batch is
    dispatched at the previous one's completion read); one landing in an
    interval already closed is refused rather than binned wrongly.
    """
    def __init__(self, horizon_ns, interval_ns=NS_PER_S):
        self.horizon_ns, self.interval_ns = horizon_ns, interval_ns
        self.count = max(1, -(-horizon_ns // interval_ns))
        self.rows, self.values = [], []

    def add(self, completion_ns, response_ns):
        if completion_ns >= self.horizon_ns:
            return
        k = completion_ns // self.interval_ns
        require(k >= len(self.rows), "completion times go back into a closed interval")
        while len(self.rows) < k:
            self._close()
        self.values.append(response_ns)

    def _close(self):
        i, values = len(self.rows), self.values
        self.values = []
        start, end = i * self.interval_ns, min((i + 1) * self.interval_ns, self.horizon_ns)
        values.sort()
        self.rows.append({"interval_start_s": start / NS_PER_S, "interval_end_s": end / NS_PER_S,
                          "completions": len(values),
                          "throughput_ops_per_second": len(values) * NS_PER_S / (end - start),
                          "response_p50_us": quantile(values, .5) / 1e3 if values else "",
                          "response_p99_us": quantile(values, .99) / 1e3 if values else "",
                          "response_max_us": values[-1] / 1e3 if values else "",
                          "p99_sufficient_samples": len(values) >= 100})

    def finish(self):
        while len(self.rows) < self.count:
            self._close()
        return self.rows


def export(events, requests_path, interval_ns=NS_PER_S, plot_stride=None):
    """One pass over the raw events; writes requests.csv in request-id order.

    Returns (begin, series rows, max stall, counts, plot points). Memory holds
    the series rows, one interval's responses, the plot points (every
    `plot_stride`-th completion, none without a stride) and the requests that
    ended while a lower id was still pending (they wait to keep id order):
    never the whole cohort. The reducer guarantees what this relies on: a batch
    record precedes its members and no batch opens before the last one's
    members are all out, so only the open batch is kept; members are FIFO
    (completed ids rise), so the plot's stride over them is the id-order stride;
    arrival ids are gapless from the first arrival and each ends exactly once.
    """
    kind, f = next(events, (None, None))
    require(kind == 1, "event log has no trial begin")
    f = [int(v) for v in f]
    begin = {"saturated": f[0], "horizon_ns": f[1], "deadline_ns": f[2], "offered_cap": f[3],
             "queue_limit": f[4], "batch_maximum": f[5]}
    require(not begin["saturated"], "time series needs per-request events; saturated trials keep only count windows")
    horizon = begin["horizon_ns"]
    series = Series(horizon, interval_ns)
    counts = dict.fromkeys(("completed", "completions_after_window", *OUTCOMES.values()), 0)
    stall, stall_key, xs, ys = None, None, [], []
    batch, next_id, ended = None, None, {}
    with open(requests_path, "w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(REQUEST_COLUMNS)
        for kind, f in events:
            if kind == 2:
                if next_id is None:
                    next_id = int(f[0])
                continue
            if kind == 3:
                batch = (int(f[0]), int(f[2]), int(f[3]))
                continue
            if kind == 4:
                batch_id, dispatch, completion = batch
                request_id, arrival = int(f[1]), int(f[2])
                response = completion - arrival
                row = [request_id, "completed", arrival, dispatch, completion, response / 1e3,
                       (dispatch - arrival) / 1e3, (completion - dispatch) / 1e3, batch_id]
                series.add(completion, response)
                if stall_key is None or (response, -request_id) > stall_key:
                    stall_key = (response, -request_id)
                    stall = {"request_id": request_id, "response_us": response / 1e3,
                             "arrival_s": arrival / NS_PER_S, "completion_s": completion / NS_PER_S}
                if plot_stride and counts["completed"] % plot_stride == 0:
                    xs.append(completion / NS_PER_S)
                    ys.append(response / 1e3)
                counts["completed"] += 1
                counts["completions_after_window"] += completion >= horizon
            elif kind == 5:
                status, request_id, arrival = OUTCOMES[int(f[0])], int(f[1]), int(f[2])
                row = [request_id, status, arrival, "", "", "", "", "", ""]
                counts[status] += 1
            else:
                continue
            ended[request_id] = row
            while next_id in ended:
                writer.writerow(ended.pop(next_id))
                next_id += 1
    require(not ended, "raw events leave a gap in the request ids")
    counts["requests"] = sum(counts[k] for k in ("completed", *OUTCOMES.values()))
    return begin, series.finish(), stall, counts, (xs, ys)


def read_markers(attempt, manifest):
    """Maintenance spans in seconds, or None when the attempt retained none."""
    if not any(a["path"] == MARKERS_ARTIFACT for a in manifest["artifacts"]):
        return None
    with open(attempt / MARKERS_ARTIFACT, newline="") as stream:
        spans = [{"start_s": int(row["start_ns"]) / NS_PER_S, "end_s": int(row["end_ns"]) / NS_PER_S,
                  "role": row["role"], "level": row.get("level", "")} for row in csv.DictReader(stream)]
    for span in spans:
        require(span["start_s"] <= span["end_s"], "maintenance marker ends before it starts")
    return spans


def _write_csv(path, columns, rows):
    with open(path, "w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=columns)
        writer.writeheader()
        writer.writerows(rows)


def plot_series(path, points, rows, markers, stall, horizon_s):
    """Throughput per interval above a response scatter of `points` (completion s, response us) on one time
    axis; returns plotted points."""
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ImportError as error:
        raise ValueError("timeseries plot requires matplotlib in the offline analysis environment") from error
    fig, (top, bottom) = plt.subplots(2, 1, figsize=(10, 6), sharex=True, height_ratios=(1, 2))
    top.stairs([r["throughput_ops_per_second"] for r in rows], [r["interval_start_s"] for r in rows] +
               [rows[-1]["interval_end_s"]], color="tab:blue")
    top.set_ylabel("throughput (req/s)")
    bottom.scatter(*points, s=3, alpha=.5, rasterized=True, color="tab:gray")
    bottom.set_yscale("log")
    bottom.set_ylabel("response (us)")
    bottom.set_xlabel("completion time since measurement start (s)")
    # One color per maintenance role (a top merge's preparation, which may run
    # ahead almost continuously, must not hide its short carry-dependent merge).
    palette = ("tab:orange", "tab:green", "tab:purple", "tab:brown", "tab:pink", "tab:olive")
    colors = {}
    for span in markers or []:
        colors.setdefault(span["role"], palette[len(colors) % len(palette)])
    for axis in (top, bottom):
        axis.axvline(horizon_s, color="k", lw=.8, ls=":")
        labelled = set()
        for span in markers or []:
            first = axis is top and span["role"] not in labelled
            labelled.add(span["role"])
            axis.axvspan(span["start_s"], span["end_s"], color=colors[span["role"]], alpha=.25, lw=0,
                         label=f"maintenance: {span['role']}" if first else None)
    if stall:
        bottom.scatter([stall["completion_s"]], [stall["response_us"]], s=40, color="tab:red", zorder=3)
        bottom.annotate(f"max stall {stall['response_us']:.1f} us (request {stall['request_id']})",
                        (stall["completion_s"], stall["response_us"]), xytext=(8, -4), textcoords="offset points",
                        color="tab:red")
    if markers:
        top.legend(loc="upper right")
    fig.tight_layout()
    path = Path(path)
    for suffix in (".png", ".pdf"):
        fig.savefig(path.with_suffix(suffix), dpi=150)
    plt.close(fig)
    return len(points[0]) + (1 if stall else 0)


def timeseries(reducer, output, attempt=None, campaign=None, trial_id=None, environment_class=None,
               interval_ns=NS_PER_S, plot=True):
    reducer, output = Path(reducer).resolve(strict=True), Path(output)
    if campaign is not None:
        from .campaign import successful
        require(attempt is None and trial_id, "give --campaign with --trial-id, or --attempt")
        selected = successful(Path(campaign).resolve(), trial_id, environment_class)
        require(selected is not None, f"no complete committed attempt of trial {trial_id}")
        attempt = selected[0]
    require(attempt is not None, "give --attempt, or --campaign with --trial-id")
    attempt = Path(attempt).resolve()
    manifest = verify(attempt, deep=True)
    chunks = sorted(attempt / a["path"] for a in manifest["artifacts"]
                    if a["path"].startswith("worker/events/") and a["path"].endswith(".bin"))
    require(bool(chunks), "attempt has no full-event log (histogram-checkpoint trials keep no per-request events)")
    metadata = load_json(attempt / "worker/worker.json")
    require(metadata["lost_events"] == 0 and not metadata["writer_error"], "worker event log is incomplete")
    markers = read_markers(attempt, manifest)
    # The plot strides over the completions in id order; the stride needs their count before the stream.
    expected = metadata["trial_boundaries"][1] if plot else None
    stride = max(1, -(-expected // PLOT_POINT_CAP)) if plot else None
    created = not output.exists()
    output.mkdir(parents=True, exist_ok=True)
    partial = output / "requests.csv.partial"
    try:
        with closing(raw_events(reducer, chunks)) as events:
            begin, rows, stall, counts, points = export(events, partial, interval_ns, stride)
        require(not plot or counts["completed"] == expected, "worker.json trial_boundaries disagree with the raw events")
    except BaseException:
        partial.unlink(missing_ok=True)
        if created:
            output.rmdir()
        raise
    partial.replace(output / "requests.csv")
    _write_csv(output / "series.csv", SERIES_COLUMNS, rows)
    _write_csv(output / "markers.csv", MARKER_COLUMNS, markers or [])
    horizon_s = begin["horizon_ns"] / NS_PER_S
    plotted = plot_series(output / "series", points, rows, markers, stall, horizon_s) if plot else 0
    sidecar = {"series_schema_version": SERIES_SCHEMA_VERSION, "trial_id": manifest["trial_id"],
               "attempt_id": manifest["attempt_id"], "attempt": str(attempt),
               "time_origin": "trial clock zero = measurement start; clock_origin_steady_ns places it on steady_clock",
               "clock_origin_steady_ns": metadata.get("clock_origin_steady_ns"),
               "binning": "by completion time relative to the measurement start; interval k holds completions "
                          "in [k*interval, (k+1)*interval) within [0, horizon); the last interval is truncated "
                          "at the horizon and its throughput uses its own width",
               "quantiles": "exact nearest rank over the raw per-request responses in the interval",
               "interval_ns": interval_ns, "horizon_ns": begin["horizon_ns"],
               "requests": counts["requests"], "completed": counts["completed"],
               "completions_in_window": sum(r["completions"] for r in rows),
               "completions_after_window": counts["completions_after_window"],
               "rejected": counts["rejected"], "timed_out": counts["timed_out"], "outstanding": counts["outstanding"],
               "max_stall": stall, "markers": len(markers or []), "plot_points": plotted,
               "plot_note": f"at most {PLOT_POINT_CAP} evenly strided requests plus the maximum; the CSV keeps all",
               "maintenance_coverage": metadata.get("maintenance_coverage")}
    if markers is None:
        sidecar["markers_unavailable"] = (metadata.get("maintenance_markers") or {}).get(
            "unavailable", MARKERS_UNAVAILABLE)
    else:
        sidecar["markers_source"] = (metadata.get("maintenance_markers") or {}).get("source")
    atomic_json(output / "series.json", sidecar)
    return sidecar
