"""End-to-end check of the campaign coordinator (python -m analysis.oram_bench), run by CTest.

Drives plan, resolve, run, reduce and verify on a tiny synthetic campaign with
the fake worker: real raw-data commits, campaign ownership, launch policy,
corruption detection and recovery after the coordinator is killed abruptly.
Arguments: the fake worker binary (oram_bench_fake_worker), then the checkpoint
reducer (oram_bench_aggregate).
"""
import json
import importlib.util
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from analysis.oram_bench.codec import decode, load_json
from analysis.oram_bench.planner import expand, write_plan
from analysis.oram_bench.schema import Campaign
from analysis.oram_bench.store import ownership, verify

worker, reducer = sys.argv[1:]

def configuration(duration=1_000_000):
    # The fixture's trial needs a few MiB. Without a headroom reservation its
    # launch does not depend on how much of the host's memory is free.
    return {"schema_version": 1, "name": "recovery-fixture", "repetitions": 1,
            "resources": {"headroom_ppm": 0},
            "stages": [{"name": "fixture", "kind": "smoke", "capacities": [128],
                "shapes": [{"name": "small", "key_bytes": 4, "value_bytes": 8}],
                "candidates": [{"name": "auto", "overrides": {"scheme": "auto"}}],
                "api_modes": ["scalar"]}],
            "timing": {"warmup_ns": 0, "measurement_ns": duration,
                "drain_deadline_ns": 1_000_000_000, "setup_allowance_ns": 1_000_000_000,
                "max_trial_ns": 5_000_000_000}}

def command(campaign, verb="run"):
    return [sys.executable, "-m", "analysis.oram_bench", verb, "--campaign", str(campaign),
            "--synthetic", "--reducer", reducer]

def run(args, expected=0):
    result = subprocess.run(args, capture_output=True, text=True, cwd=ROOT)
    assert result.returncode == expected, (args, result.returncode, result.stdout, result.stderr)
    return json.loads(result.stdout) if expected == 0 else None

def publish(config, campaign, *extra):
    """plan, then resolve: freezes the worker into campaign/build."""
    write_plan(expand(decode(Campaign, config)), campaign)
    return run([sys.executable, "-m", "analysis.oram_bench", "resolve", "--campaign", str(campaign),
                "--worker", worker, "--synthetic", *extra])

def wait_for(fn):
    deadline = time.monotonic() + 10
    while time.monotonic() < deadline:
        value = fn()
        if value:
            return value
        time.sleep(.01)
    raise AssertionError("timeout waiting for lifecycle state")

with tempfile.TemporaryDirectory() as temporary:
    campaign = Path(temporary) / "campaign"
    resolved = publish(configuration(), campaign)
    assert resolved["status_counts"] == {"runnable": 1}, resolved
    assert (campaign / "build/worker").read_bytes() == Path(worker).read_bytes()
    blocked = run(command(campaign) + ["--min-free-bytes", str(2**63)])
    assert blocked["launched"] == 0 and blocked["coordinator"]["reason"] == "disk_watermark"
    # The watermark persists in launch_policy.json; restoring it is explicit.
    assert run(command(campaign))["coordinator"]["reason"] == "disk_watermark"
    result = run(command(campaign) + ["--min-free-bytes", str(256 * 1024**2), "--update-launch-policy"])
    assert result["counts"] == {"complete": 1}, result
    attempts = list(campaign.glob("trials/*/attempts/*"))
    assert len(attempts) == 1
    manifest = verify(attempts[0])
    assert manifest["status"] == "complete"
    result = run(command(campaign, "resume"))
    assert result["launched"] == 0 and len(list(campaign.glob("trials/*/attempts/*"))) == 1
    # Derived summaries can disappear after raw commit without forcing a retry.
    (attempts[0] / "worker/summary.json").unlink()
    assert run(command(campaign, "resume"))["launched"] == 0
    reduced = Path(temporary) / "reduced"
    reduction = run([sys.executable, "-m", "analysis.oram_bench", "reduce", "--campaign", str(campaign),
                    "--reducer", reducer, "--output", str(reduced)])
    # Reduction writes derived files only under its output.
    assert reduction["repetitions"] == 1 and not (attempts[0] / "worker/summary.json").exists()
    group = load_json(reduced / "summary.json")["groups"][0]
    assert group["runtime"] == "fake" and group["throughput"]["repetitions"] == 1
    assert group["repetitions"][0]["correctness"] == "verified"
    if importlib.util.find_spec("matplotlib"):
        os.environ["MPLCONFIGDIR"] = str(Path(temporary) / "mpl")
        plot = Path(temporary) / "plots"
        run([sys.executable, "-m", "analysis.oram_bench", "plot", "--summary", str(reduced / "summary.json"),
             "--output", str(plot)])
        assert (plot / "campaign.png").stat().st_size > 0 and (plot / "campaign.pdf").stat().st_size > 0
    with ownership(campaign):
        run(command(campaign, "resume"), expected=2)
    # Committed raw data is authoritative; corruption invalidates reuse.
    chunk = next(attempts[0].glob("worker/events/*.bin"))
    raw = chunk.read_bytes()
    # A same-size corruption passes the shallow scheduling check and is
    # found by `verify --deep`; a truncation is found by both.
    chunk.write_bytes(raw[:-1] + bytes([raw[-1] ^ 1]))
    assert run(command(campaign, "resume"))["launched"] == 0
    run([sys.executable, "-m", "analysis.oram_bench", "verify", "--campaign", str(campaign), "--deep"], expected=2)
    chunk.write_bytes(raw[:-1])
    state = run([sys.executable, "-m", "analysis.oram_bench", "status", "--campaign", str(campaign)])
    assert state["counts"] == {"uncommitted": 1}
    result = run(command(campaign, "resume"))
    assert result["counts"] == {"complete": 1} and result["launched"] == 1
    assert chunk.read_bytes() == raw[:-1], "recovery overwrote interrupted/corrupt evidence"
    # Freeze a relative rate from committed raw boundaries even after the
    # source's derived summary disappears. Compact latency replays identically.
    relative = Path(temporary) / "relative"
    config = configuration()
    config["stages"][0]["kind"] = "latency"
    config["stages"][0]["rates"] = {"saturation_fractions_ppm": [500000]}
    config["instrumentation"] = {"logging": "histogram_checkpoints", "minimum_tail_count": 1}
    publish(config, relative)
    source_run = run(command(relative) + ["--limit", "1"])
    assert source_run["counts"] == {"complete": 1, "pending": 1}
    source_attempt = next(relative.glob("trials/*/attempts/*"))
    boundaries = load_json(source_attempt / "worker/worker.json")["trial_boundaries"]
    (source_attempt / "worker/summary.json").unlink()
    assert run(command(relative, "resume"))["counts"] == {"complete": 2}
    frozen = load_json(next(relative.glob("rates/*/*.json")))
    assert frozen["ops_per_second"] == boundaries[1] * 1_000_000_000 // (2 * boundaries[4])
    original = frozen.copy()
    assert run(command(relative, "resume"))["launched"] == 0
    assert load_json(next(relative.glob("rates/*/*.json"))) == original
    compact_reduction = run([sys.executable, "-m", "analysis.oram_bench", "reduce", "--campaign", str(relative),
        "--reducer", reducer, "--output", str(Path(temporary) / "compact-summary")])
    assert compact_reduction["repetitions"] == 2
    # Verification off on the constant-space no-op backend
    # commits a complete trial that is visibly unverified, never a forged claim.
    unverified = Path(temporary) / "unverified"
    config = configuration()
    config["stages"][0]["kind"] = "capacity"
    config["instrumentation"] = {"verification": "off"}
    publish(config, unverified, "--synthetic-backend", "noop")
    assert run(command(unverified))["counts"] == {"complete": 1}
    attempt = next(unverified.glob("trials/*/attempts/*"))
    manifest = verify(attempt)
    assert manifest["status"] == "complete" and manifest["verification"] == "off"
    assert not manifest["correctness_verified"], manifest
    metadata = load_json(attempt / "worker/worker.json")
    assert load_json(attempt / "worker/resolved.json")["scheme"] == "noop"
    assert metadata["version_table_bytes"] == 0 and metadata["verified_reads"] == 0, metadata
    run([sys.executable, "-m", "analysis.oram_bench", "reduce", "--campaign", str(unverified),
         "--reducer", reducer, "--output", str(Path(temporary) / "unverified-summary")])
    repetition = load_json(Path(temporary) / "unverified-summary/summary.json")["groups"][0]["repetitions"][0]
    assert repetition["correctness"] == "unverified"
    assert ",unverified," in (Path(temporary) / "unverified-summary/repetitions.csv").read_text()
    # Several launches in one run, and a launch policy that persists.
    multi = Path(temporary) / "multi"
    config = configuration(); config["repetitions"] = 3
    publish(config, multi)
    result = run(command(multi) + ["--retries", "3"])
    assert result["launched"] == 3 and result["counts"] == {"complete": 3}, result
    assert load_json(multi / "launch_policy.json")["retries"] == 3
    run(command(multi, "resume") + ["--retries", "1"], expected=2)
    assert run(command(multi, "resume") + ["--retries", "1", "--update-launch-policy"])["launched"] == 0
    assert load_json(multi / "launch_policy.json")["retries"] == 1
    # Kill coordinator and its worker without a graceful-shutdown opportunity.
    # With no worker-side retries, the orphaned attempt still reruns: it is a
    # preemption, bounded separately from worker retries.
    interrupted = Path(temporary) / "interrupted"
    publish(configuration(500_000_000), interrupted)
    process = subprocess.Popen(command(interrupted) + ["--retries", "0"], cwd=ROOT,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    def active():
        for path in interrupted.glob("trials/*/attempts/*/state.json"):
            state = load_json(path)
            memory = path.parent / "worker/memory.csv"
            # Events are written only after the trial; the flushed
            # before_measure sample shows the worker has started measuring.
            if state.get("worker_pid") and memory.exists() and "\nbefore_measure," in memory.read_text():
                return state["worker_pid"]
    pid = wait_for(active)
    process.kill()
    process.communicate(timeout=5)
    blocked = False
    try:
        with ownership(interrupted):
            pass
    except ValueError:
        blocked = True
    assert blocked, "orphaned worker did not retain exclusive ownership"
    os.killpg(pid, signal.SIGKILL)
    def released():
        try:
            with ownership(interrupted):
                return True
        except ValueError:
            return False
    wait_for(released)
    result = run(command(interrupted, "resume"))
    assert result["counts"] == {"complete": 1} and result["launched"] == 1, result
    history = sorted(interrupted.glob("trials/*/attempts/*"))
    assert len(history) == 2 and not (history[0] / "COMMITTED.json").exists()
    assert load_json(history[0] / "state.json")["status"] == "interrupted"
    assert run(command(interrupted, "resume"))["launched"] == 0
print("synthetic campaign recovery tests passed")
