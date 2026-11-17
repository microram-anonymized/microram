"""The 1-second throughput/latency series (analysis/oram_bench/timeseries.py): synthetic raw
events through the real C++ reducer; skipped without a built reducer."""
import csv
import hashlib
import json
import os
from pathlib import Path
import struct
import tempfile
import unittest
from unittest.mock import patch
import zlib

from analysis.oram_bench import timeseries as ts

ROOT = Path(__file__).resolve().parents[2]
S = 1_000_000_000


def find_reducer():
    candidates = [os.environ.get("ORAM_BENCH_REDUCER", "")]
    candidates += [str(p) for p in sorted((ROOT / "build").glob("**/oram_bench_aggregate"))]
    candidates += [str(p) for p in sorted(Path.home().glob(".cache/oram-builds/*/analysis/oram_bench_aggregate"))]
    return next((Path(c) for c in candidates if c and Path(c).is_file()), None)


def write_chunk(path, sequence, events):
    payload = b"".join(struct.pack("<8Q", *e) for e in events)
    path.write_bytes(b"ORBEV01\n" + struct.pack("<4Q", len(payload), zlib.crc32(payload), sequence, len(events)) + payload)


def ev(kind, *fields):
    return (kind, *fields, *([0] * (7 - len(fields))))


# Horizon 3 s. Completions (arrival -> completion): id0 100 us and id1 300 us in [0,1);
# id2 101,000 us and id3 1,000 us (one batch) in [1,2); id4 500 us in [2,3); id5 completes at 3.05 s, after the window.
EVENTS = [
    ev(1, 0, 3 * S, 4 * S, 100, 10, 2, 1024),
    *[ev(2, i, a) for i, a in enumerate([S // 10, S // 2, 12 * S // 10, 13 * S // 10, 29 * S // 10, 299 * S // 100])],
    ev(3, 0, 1, S // 10, S // 10 + 100_000), ev(4, 0, 0, S // 10),
    ev(3, 1, 1, S // 2, S // 2 + 300_000), ev(4, 1, 1, S // 2),
    ev(3, 2, 2, 13 * S // 10, 13 * S // 10 + 1_000_000), ev(4, 2, 2, 12 * S // 10), ev(4, 2, 3, 13 * S // 10),
    ev(3, 3, 1, 29 * S // 10, 29 * S // 10 + 500_000), ev(4, 3, 4, 29 * S // 10),
    ev(3, 4, 1, 299 * S // 100, 305 * S // 100), ev(4, 4, 5, 299 * S // 100),
    ev(8, 305 * S // 100, 305 * S // 100, 6, 6, 6, 0, 100),
]


def golden_events():
    """A deterministic replay-valid log: 2255 requests over a 4.5 s horizon, batches of up to 8, an
    empty interval [2,3) s (no arrivals in [1.9,3) s), a sparse one [3,4) s, two stalls, interleaved
    rejections and timeouts, completions after the horizon and outstanding requests at the end."""
    state = [12345]
    def rand(lo, hi):  # LCG, stable across Python versions
        state[0] = (state[0] * 6364136223846793005 + 1442695040888963407) % 2**64
        return lo + (state[0] >> 33) % (hi - lo)
    horizon, batch, queue = 9 * S // 2, 8, 64
    times, t = [], S // 1000
    while t < horizon:
        times.append(t)
        t += rand(15_000_000, 16_000_000) if 3 * S <= t < 4 * S else rand(200_000, 2_000_000)
        if 19 * S // 10 <= t < 3 * S:
            t = 3 * S + rand(0, 1_000_000)
    events = [ev(1, 0, horizon, horizon + S, 10**6, queue, batch, 1024)]
    pending, offered, now, calls, completed, during, rejected = [], 0, 0, 0, 0, 0, 0
    def arrive_until(limit):
        nonlocal offered, rejected
        while offered < len(times) and times[offered] <= limit:
            events.append(ev(2, offered, times[offered]))
            if offered % 97 == 50:  # rejected at once, while lower ids still wait
                events.append(ev(5, 0, offered, times[offered]))
                rejected += 1
            else:
                pending.append((offered, times[offered]))
            offered += 1
    stop = horizon + 1_000_000
    while now < stop and (pending or offered < len(times)):
        arrive_until(now)
        if not pending:
            now = times[offered]
            continue
        if calls % 211 == 7 and len(pending) > 1:  # the head times out between batches
            events.append(ev(5, 1, *pending.pop(0)))
        members, pending[:] = pending[:batch], pending[batch:]
        service = rand(300_000, 3_000_000)
        if calls == 400:
            service = 30_000_000
        if horizon - 10_000_000 <= now < horizon and service < 10_000_000:
            service = 12_000_000
        events.append(ev(3, calls, len(members), now, now + service))
        events.extend(ev(4, calls, i, a) for i, a in members)
        calls += 1
        completed += len(members)
        during += len(members) * (now + service < horizon)
        now += service
    arrive_until(horizon)
    events.extend(ev(5, 2, i, a) for i, a in pending)
    caller = max(horizon, now)
    events.append(ev(8, caller, caller, offered, offered - rejected, completed, 0, 100))
    return events, [offered, completed, during, caller, caller, 0]


# sha256 of what the earlier in-memory exporter (one dict per request) wrote for golden_events() cut
# into four chunks with PLOT_POINT_CAP = 100; series.json is hashed as sorted-key JSON without "attempt".
GOLDEN = {"requests.csv": "a16886f6a4c2976f5642bd5caa5936e2b34ec97278ea54bd9d0b95486b05c53c",
          "series.csv": "416e8632ed3d084a36e0331e101d1581db30e08be5cc63efcadf57fc5121ad4c",
          "markers.csv": "d5544587e91971a0b483db025be8881f71914f037bf78052c566c36f36cfbedc",
          "series.json": "eeadbd7a8359d74ba6eaf500bc57d46300a51e796c90c45b576ad5dfcef2e496"}


def raw(events):
    """Records as raw_events yields them, for export() without the reducer."""
    return iter([(e[0], [str(v) for v in e[1:]]) for e in events])


class TimeSeriesTest(unittest.TestCase):
    def test_binning_short_last_interval_and_quantiles(self):
        series = ts.Series(5 * S // 2)
        for completion in (10_000, 20_000, 2 * S + 400_000_000, 5 * S):
            series.add(completion, completion)
        rows = series.finish()
        self.assertEqual([r["completions"] for r in rows], [2, 0, 1])
        self.assertEqual([r["interval_end_s"] for r in rows], [1, 2, 2.5])
        self.assertEqual([r["throughput_ops_per_second"] for r in rows], [2, 0, 2])  # 1 completion in 0.5 s
        self.assertEqual((rows[0]["response_p50_us"], rows[0]["response_p99_us"], rows[0]["response_max_us"]),
                         (10, 20, 20))
        self.assertEqual(rows[1]["response_p50_us"], "")
        self.assertFalse(rows[0]["p99_sufficient_samples"])

    def export(self, events, stride=None):
        with tempfile.TemporaryDirectory() as directory:
            return ts.export(raw(events), Path(directory) / "requests.csv", plot_stride=stride)

    def test_max_stall_ties_take_the_lowest_id(self):
        arrivals = [ev(2, i, 0) for i in (2, 3, 4)]
        members = [ev(3, 0, 1, 0, 5000), ev(4, 0, 4, 0), ev(3, 1, 1, 0, 9000), ev(4, 1, 3, 0),
                   ev(3, 2, 1, 0, 9000), ev(4, 2, 2, 0)]
        self.assertEqual(self.export([EVENTS[0], *arrivals, *members])[2]["request_id"], 2)
        self.assertIsNone(self.export([EVENTS[0]])[2])

    def test_a_completion_into_a_closed_interval_is_refused(self):
        late = [EVENTS[0], ev(2, 0, 0), ev(2, 1, 0), ev(3, 0, 1, 0, S + 5), ev(4, 0, 0, 0), ev(3, 1, 1, 0, 5),
                ev(4, 1, 1, 0)]
        with self.assertRaisesRegex(ValueError, "closed interval"):
            self.export(late)

    def test_chunks_must_share_one_directory(self):
        with self.assertRaisesRegex(ValueError, "one directory"):
            next(ts.raw_events("oram_bench_aggregate", [Path("a/0.bin"), Path("b/1.bin")]))

    def run_fixture(self, markers=None, plot=False, maintenance=None):
        reducer = find_reducer()
        if reducer is None:
            self.skipTest("oram_bench_aggregate is not built")
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        attempt = Path(directory.name) / "attempt"
        (attempt / "worker/events").mkdir(parents=True)
        write_chunk(attempt / "worker/events/00000000000000000000.bin", 0, EVENTS)
        (attempt / "worker/worker.json").write_text(json.dumps(
            {"lost_events": 0, "writer_error": "", "clock_origin_steady_ns": 7, "maintenance_coverage": None,
             "trial_boundaries": [6, 6, 5, 305 * S // 100, 305 * S // 100, 0],
             **({"maintenance_markers": maintenance} if maintenance else {})}))
        artifacts = [{"path": "worker/events/00000000000000000000.bin"}]
        if markers is not None:
            (attempt / "worker/markers.csv").write_text(markers)
            artifacts.append({"path": "worker/markers.csv"})
        manifest = {"trial_id": "t", "attempt_id": "a", "artifacts": artifacts}
        output = Path(directory.name) / "out"
        with patch.object(ts, "verify", return_value=manifest):
            sidecar = ts.timeseries(reducer, output, attempt=attempt, plot=plot)
        def read(name):
            with open(output / name, newline="") as stream:
                return list(csv.DictReader(stream))
        return sidecar, read, output

    def test_end_to_end_series(self):
        sidecar, read, output = self.run_fixture()
        series = read("series.csv")
        self.assertEqual([r["completions"] for r in series], ["2", "2", "1"])
        self.assertEqual([float(r["throughput_ops_per_second"]) for r in series], [2, 2, 1])
        self.assertEqual([(float(r["interval_start_s"]), float(r["interval_end_s"])) for r in series],
                         [(0, 1), (1, 2), (2, 3)])
        self.assertEqual([float(r["response_p50_us"]) for r in series], [100, 1000, 500])
        self.assertEqual([float(r["response_p99_us"]) for r in series], [300, 101000, 500])
        self.assertEqual([float(r["response_max_us"]) for r in series], [300, 101000, 500])
        requests = read("requests.csv")
        self.assertEqual(len(requests), 6)
        self.assertEqual(float(requests[2]["response_us"]), 101000)
        self.assertEqual(float(requests[2]["queue_us"]), 100000)  # arrived 1.2 s, dispatched 1.3 s
        self.assertEqual(float(requests[2]["service_us"]), 1000)
        self.assertEqual(requests[5]["completion_ns"], str(305 * S // 100))
        self.assertEqual(sidecar["max_stall"]["request_id"], 2)
        self.assertEqual(sidecar["max_stall"]["response_us"], 101000)
        self.assertEqual((sidecar["completed"], sidecar["completions_in_window"], sidecar["completions_after_window"]),
                         (6, 5, 1))
        self.assertIn("completion time", sidecar["binning"])
        self.assertEqual(read("markers.csv"), [])
        self.assertIn("markers_unavailable", sidecar)
        self.assertEqual(json.loads((output / "series.json").read_text())["max_stall"], sidecar["max_stall"])

    def test_plot_is_written_with_the_stall_point(self):
        try:
            import matplotlib  # noqa: F401
        except ImportError:
            self.skipTest("matplotlib is not installed")
        sidecar, _, output = self.run_fixture("role,level,start_ns,end_ns\ntop_rebuild,3,500000000,1500000000\n", plot=True)
        self.assertTrue((output / "series.png").stat().st_size > 0 and (output / "series.pdf").stat().st_size > 0)
        self.assertEqual(sidecar["plot_points"], 7)

    def test_markers_are_passed_through_when_the_attempt_retains_them(self):
        sidecar, read, _ = self.run_fixture("role,level,start_ns,end_ns\ntop_rebuild,3,500000000,1500000000\n")
        self.assertEqual(read("markers.csv"), [{"start_s": "0.5", "end_s": "1.5", "role": "top_rebuild", "level": "3"}])
        self.assertNotIn("markers_unavailable", sidecar)

    def test_worker_states_why_it_has_no_markers_and_names_its_source(self):
        sidecar, _, _ = self.run_fixture(maintenance={"unavailable": "SONIC's eviction is not instrumented"})
        self.assertEqual(sidecar["markers_unavailable"], "SONIC's eviction is not instrumented")
        # A span that began before the measurement (a top merge prepared ahead) keeps its negative start.
        sidecar, read, _ = self.run_fixture("role,level,start_ns,end_ns\ntop_prepare,4,-3000000,41000000\n",
                                            maintenance={"source": "top_merge_log", "spans": 1})
        self.assertEqual(sidecar["markers_source"], "top_merge_log")
        self.assertEqual(read("markers.csv")[0]["start_s"], "-0.003")

    def test_saturated_trials_are_refused(self):
        reducer = find_reducer()
        if reducer is None:
            self.skipTest("oram_bench_aggregate is not built")
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "0.bin"
            write_chunk(path, 0, [ev(1, 1, S, 2 * S, 100, 10, 2, 1024), ev(6, 0, S, 8),
                                  ev(8, S, S, 8, 8, 8, 0, 100)])
            with self.assertRaisesRegex(ValueError, "saturated"):
                ts.export(ts.raw_events(reducer, [path]), Path(directory) / "requests.csv")

    def test_a_failed_replay_publishes_nothing(self):
        reducer = find_reducer()
        if reducer is None:
            self.skipTest("oram_bench_aggregate is not built")
        with tempfile.TemporaryDirectory() as directory:
            attempt, output = Path(directory) / "attempt", Path(directory) / "out"
            (attempt / "worker/events").mkdir(parents=True)
            write_chunk(attempt / "worker/events/0.bin", 0, EVENTS[:-1])  # no trial end
            (attempt / "worker/worker.json").write_text(json.dumps({"lost_events": 0, "writer_error": ""}))
            manifest = {"trial_id": "t", "attempt_id": "a", "artifacts": [{"path": "worker/events/0.bin"}]}
            with patch.object(ts, "verify", return_value=manifest), self.assertRaisesRegex(ValueError, "trial end"):
                ts.timeseries(reducer, output, attempt=attempt, plot=False)
            self.assertFalse(output.exists())

    def test_multi_chunk_output_matches_the_in_memory_exporter(self):
        reducer = find_reducer()
        if reducer is None:
            self.skipTest("oram_bench_aggregate is not built")
        try:
            import matplotlib  # noqa: F401
        except ImportError:
            self.skipTest("matplotlib is not installed")
        events, boundaries = golden_events()
        ids = [e[2] for e in events if e[0] in (4, 5)]
        self.assertNotEqual(ids, sorted(ids))  # requests end out of id order: the reorder path runs
        with tempfile.TemporaryDirectory() as directory:
            attempt, output = Path(directory) / "attempt", Path(directory) / "out"
            (attempt / "worker/events").mkdir(parents=True)
            artifacts = []
            for first, end in zip((0, 1000, 1001, 4000), (1000, 1001, 4000, len(events))):
                artifacts.append({"path": f"worker/events/{first:020d}.bin"})
                write_chunk(attempt / artifacts[-1]["path"], first, events[first:end])
            (attempt / "worker/worker.json").write_text(json.dumps(
                {"lost_events": 0, "writer_error": "", "clock_origin_steady_ns": 7, "maintenance_coverage": None,
                 "trial_boundaries": boundaries, "maintenance_markers": {"source": "top_merge_log", "spans": 2}}))
            (attempt / "worker/markers.csv").write_text(
                "role,level,start_ns,end_ns\ntop_prepare,4,-3000000,41000000\ntop_merge,4,1500000000,1531000000\n")
            artifacts.append({"path": "worker/markers.csv"})
            manifest = {"trial_id": "t", "attempt_id": "a", "artifacts": artifacts}
            with patch.object(ts, "verify", return_value=manifest), patch.object(ts, "PLOT_POINT_CAP", 100):
                ts.timeseries(reducer, output, attempt=attempt, plot=True)
            digests = {name: hashlib.sha256((output / name).read_bytes()).hexdigest()
                       for name in ("requests.csv", "series.csv", "markers.csv")}
            sidecar = json.loads((output / "series.json").read_text())
            self.assertEqual(sidecar.pop("attempt"), str(attempt.resolve()))
            digests["series.json"] = hashlib.sha256(json.dumps(sidecar, sort_keys=True).encode()).hexdigest()
            self.assertEqual(digests, GOLDEN)
            self.assertEqual(sorted(p.name for p in output.iterdir()),
                             ["markers.csv", "requests.csv", "series.csv", "series.json", "series.pdf", "series.png"])


if __name__ == "__main__":
    unittest.main()
