"""The SONIC worker end to end. No measurement claims.

    check_sonic_worker.py WORKER

Runs on an 8-core budget, so rows seat Ser with four eviction threads and
batches with four access threads (the paper's Par8 needs 15 cores).
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from analysis.oram_bench.codec import decode  # noqa: E402
from analysis.oram_bench.schema import WorkerResolution  # noqa: E402

BASE = ["--capacity", "65536", "--key-bytes", "4", "--value-bytes", "8", "--key-layout", "dense", "--cores", "8"]
FITS = ["--override.sonic.eviction_threads", "4"]


def run(worker, *args):
    return subprocess.run([str(worker), *args], capture_output=True, text=True, timeout=600)


def main(worker):
    worker = Path(worker)
    info = json.loads(run(worker, "--build-info").stdout)
    assert info["baseline"] == "sonic" and info["side_files"] == [], info
    assert info["fetch_record"]["sources"]["sonic"]["sha256"].startswith("aa02c4fc"), info
    # Refusals, each with its reason.
    for args, reason in (
            (["--scheme", "sonic_zingoram", *BASE], "thread plan needs 8 library cores"),
            (["--scheme", "sonic_zingoram", *BASE, "--api", "batch", "--batch-size", "64"],
             "thread plan needs 15 library cores"),
            (["--scheme", "sonic_zingoram", *BASE[:-4], "--cores", "8", *FITS], "dense keys"),
            (["--scheme", "sonic_zingoram", *BASE, *FITS, "--hit-ppm", "500000", "--read-ppm", "1000000",
              "--miss-keys", "100"], "miss"),
            (["--scheme", "sonic_zingoram", *BASE, *FITS, "--override.sonic.map_branching_factor", "64"],
             "belong to sonic_zingoram_recursive"),
            (["--scheme", "sonic_zingoram", *BASE, *FITS, "--override.sonic.stash_bound", "10"], "unknown override"),
            (["--scheme", "sonic_zingoram", *BASE, "--override.sonic.eviction_threads", "3"], "divide"),
            (["--scheme", "h2o2ram", *BASE, *FITS], "this worker runs")):
        result = run(worker, *args, "--resolve-only", "1")
        assert result.returncode == 2 and reason in result.stderr and result.stdout == "", (args, result.stderr)
    # A resolved envelope: explicit schemes, self-placed pools, no carries.
    resolved = json.loads(run(worker, "--scheme", "sonic_zingoram_recursive", *BASE, *FITS,
                              "--resolve-only", "1").stdout)
    decode(WorkerResolution, resolved)  # what `run`'s attempt check reads
    assert resolved["carry_period_accesses"] == [] and resolved["library_threads"] == 4, resolved
    assert any(c["field"] == "map_tree.1" for c in resolved["choices"]), resolved["choices"]
    # Verified smoke rows for both schemes, scalar and batch.
    with tempfile.TemporaryDirectory() as directory:
        for scheme in ("sonic_zingoram", "sonic_zingoram_recursive"):
            for api in (["--api", "scalar"], ["--api", "batch", "--batch-size", "64",
                                               "--override.sonic.access_threads", "4"]):
                output = Path(directory) / f"{scheme}-{api[1]}"
                result = run(worker, "--scheme", scheme, *BASE, *FITS, *api, "--output", str(output),
                             "--measurement-ns", "300000000", "--placement", "near_far", "--workload-seed", "3")
                assert result.returncode == 0, (scheme, api, result.stderr[-2000:])
                metadata = json.loads((output / "worker.json").read_text())
                assert metadata["correctness_verified"] and metadata["verified_reads"] > 0, metadata
                if api[1] == "batch":
                    assert metadata["verified_old_values"] > 0, metadata
                # Maintenance markers: SONIC's eviction is not instrumented; the row says so.
                assert "eviction" in metadata["maintenance_markers"]["unavailable"], metadata
                assert not (output / "markers.csv").exists()
                placement = json.loads((output / "placement.json").read_text())
                assert placement["all_planned_roles_verified"] and not placement["violations"], placement
                assert json.loads((output / "resolved.json").read_text())["placement_policy"] == "baseline_self_placed"
                print(f"{scheme} {api[1]}: verified {metadata['verified_reads']} reads, "
                      f"{metadata['verified_old_values']} old values")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
