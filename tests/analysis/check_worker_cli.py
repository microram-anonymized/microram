"""CLI check for the benchmark worker and the raw-event reducer (run by CTest).

Uses only the synthetic `fake`/`noop` schemes, so no ORAM is built: it
round-trips raw events through the reducer, checks that damaged artifacts are
detected, and checks the worker's metadata for unverified, marker-less and
overloaded trials.  Arguments (from analysis/CMakeLists.txt): the fake worker binary
(oram_bench_fake_worker), then the checkpoint reducer (oram_bench_aggregate).
"""
import csv
import json
from pathlib import Path
import subprocess
import sys
import tempfile

worker, reducer = sys.argv[1:]

def run(*args, expected=0):
    result = subprocess.run(args, capture_output=True, text=True)
    assert result.returncode == expected, (args, result.returncode, result.stderr)
    return result.stdout

with tempfile.TemporaryDirectory() as temporary:
    root = Path(temporary)
    for profile in ("fixed", "saturated"):
        for compact in (False, True):
            output = root / f"{profile}-{compact}"
            run(worker, "--scheme", "fake", "--output", str(output),
                "--arrival", profile, "--measurement-ns", "1000000", "--drain-ns", "1000000000",
                "--rate", "10000", "--api", "batch", "--batch-size", "4", "--batch-timeout-ns", "100000",
                "--logging", "histogram_checkpoints" if compact else "full_events",
                "--chunk-bytes", "256", "--max-requests", "1000000", "--minimum-tail-count", "1",
                "--checkpoint-interval-ns", "500000")
            summary = json.loads((output / "summary.json").read_text())
            metadata = json.loads((output / "worker.json").read_text())
            with (output / "memory.csv").open() as source:
                observations = list(csv.DictReader(source))
            phases = [row["phase"] for row in observations]
            assert phases[:3] == ["before_construction", "after_construction", "after_fill"], phases
            assert phases[-2:] == ["after_drain", "after_verify"], phases
            assert "before_measure" in phases and "measure_or_drain" not in phases, phases
            assert set(phases) <= {"before_construction", "after_construction", "after_fill",
                                   "before_measure", "measure", "final_drain", "log_flush",
                                   "phase_transition", "after_drain", "after_verify"}, phases
            times = [int(row["monotonic_ns"]) for row in observations]
            assert times == sorted(times)
            # A cgroup memory limit is a byte limit, "unlimited" (no memory.max up to the root), or blank (unknown).
            assert all(row["cgroup_limit_bytes"] in ("", "unlimited") or row["cgroup_limit_bytes"].isdecimal()
                       for row in observations), observations
            assert metadata["correctness_verified"] and not metadata["lost_events"]
            if compact and profile != "saturated":
                # Compact logging: no event buffer, and one delta checkpoint per block.
                assert not (output / "events").exists() and metadata["event_buffer_records"] == 0
                checkpoints = sorted((output / "checkpoints").glob("*.bin"))
                assert len(checkpoints) == metadata["checkpoints"] >= 1
                replay = json.loads(run(reducer, *map(str, checkpoints)))
                assert replay["completed_requests"] == summary["completed"]
                for name in ("response", "queue", "service"):
                    assert replay[name]["count"] == summary[name]["count"]
                    assert replay[name]["sum_ns"] == summary[name]["sum_ns"]
                bounded = json.loads(run(reducer, "--minimum-tail-count", "1", "--trial-boundaries",
                                         *map(str, metadata["trial_boundaries"]), *map(str, checkpoints)))
                assert bounded == summary, (bounded, summary)
                continue
            assert metadata["post_trial_write_ns"] >= 0 and metadata["clock_origin_steady_ns"] > 0
            chunks = sorted((output / "events").glob("*.bin"))
            replay = json.loads(run(reducer, "--events", *map(str, chunks)))
            assert replay == summary, (replay, summary)
            run(reducer, "--events", "--format", "csv", *map(str, chunks))
            run(reducer, "--events", "--format", "raw-csv", *map(str, chunks))
            run(reducer, "--events", str(chunks[0]), *map(str, chunks), expected=2)
            damaged = root / "damaged.bin"
            raw = bytearray(chunks[0].read_bytes())
            raw[-1] ^= 1
            damaged.write_bytes(raw)
            run(reducer, "--events", str(damaged), expected=2)
            damaged.write_bytes(raw[:15])
            run(reducer, "--events", str(damaged), expected=2)
    # With verification off, the no-op backend runs 2^40 keys x 1 KiB in constant space.
    large = root / "noop-large"
    run(worker, "--scheme", "noop", "--output", str(large), "--capacity", str(2**40), "--key-bytes", "8",
        "--value-bytes", "1024", "--verification", "off", "--api", "batch", "--batch-size", "16",
        "--measurement-ns", "1000000", "--drain-ns", "1000000000")
    metadata = json.loads((large / "worker.json").read_text())
    assert metadata["verification"] == "off" and not metadata["correctness_verified"], metadata
    assert metadata["version_table_bytes"] == 0 and metadata["final_verification_reads"] == 0, metadata
    # A backend without maintenance phases writes no markers and says so.
    assert "unavailable" in metadata["maintenance_markers"] and not (large / "markers.csv").exists(), metadata
    # CPU time over the trial call; the process covers both named threads.
    cpu = metadata["trial_cpu_ns"]
    assert cpu["wall"] > 0 and cpu["process"] >= cpu["caller_thread"] + cpu["telemetry_thread"] > 0, cpu
    # Offered load the backend cannot serve before the drain deadline is censored overload,
    # which the reducer labels overloaded, not an invalid trial (exit 0, unlike a saturated row's overrun).
    overload = root / "noop-overload"
    run(worker, "--scheme", "noop", "--output", str(overload), "--verification", "off", "--arrival", "fixed",
        "--rate", "1000000000", "--measurement-ns", "1000000", "--drain-ns", "1000000",
        "--max-requests", "100000000", "--logging", "histogram_checkpoints")
    summary = json.loads((overload / "summary.json").read_text())
    assert summary["deadline_exceeded"] and summary["outstanding"] > 0 and not summary["uncensored"], summary
    run(worker, "--scheme", "fake", "--output", str(root / "bad"), "--bogus", "1", expected=2)
    run(worker, "--scheme", "fake", "--resolve-only", "1", "--api", "scalar", "--batch-size", "4", expected=2)
print("worker CLI replay tests passed")
