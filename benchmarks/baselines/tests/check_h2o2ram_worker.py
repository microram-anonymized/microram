"""The H2O2RAM workers end to end. No measurement claims.

    check_h2o2ram_worker.py WORKER_PATCHED WORKER_SHIPPED

Needs the planner cache beside the workers for 16, 56 and 1032-byte blocks at
2^16 (check_h2o2ram_census.py, or --prepare-planner 1, writes it).
"""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from analysis.oram_bench.codec import decode  # noqa: E402
from analysis.oram_bench.schema import WorkerResolution  # noqa: E402

SHAPES = {"k4v8": (4, 8, "dense"), "k8v48": (8, 48, "permuted"), "k32v1024": (32, 1024, "permuted")}


def arguments(scheme, shape, *extra):
    key, value, layout = SHAPES[shape]
    return ["--scheme", scheme, "--capacity", "65536", "--key-bytes", str(key), "--value-bytes", str(value),
            "--key-layout", layout, "--cores", "8", *extra]


def run(worker, *args, timeout=600):
    return subprocess.run([str(worker), *args], capture_output=True, text=True, timeout=timeout)


def trial(worker, scheme, shape, output, *extra):
    # The drain deadline covers a top-level rebuild in flight: at 2^16 records of 1 KiB one takes
    # about 1 to 3 s on 7 library cores, longer on a loaded host.
    return run(worker, *arguments(scheme, shape, "--output", str(output), "--measurement-ns", "300000000",
                                  "--drain-ns", "30000000000", "--workload-seed", "9", *extra))


def main(patched, shipped):
    patched, shipped = Path(patched), Path(shipped)
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        # --build-info names the planner cache files a campaign must freeze.
        info = json.loads(run(patched, "--build-info").stdout)
        assert info["baseline"] == "h2o2ram" and info["fetch_record"]["sources"]["h2o2ram"]["commit"].startswith("906eb97")
        assert {"hash_map.bin16", "hash_map.bin56", "hash_map.bin1032"} <= set(info["side_files"]), info
        assert all(name.startswith("hash_map.bin") for name in info["side_files"])
        # Each build serves only its own scheme, and scalar rows only.
        assert run(shipped, *arguments("h2o2ram", "k4v8", "--resolve-only", "1")).returncode == 2
        refused = run(patched, *arguments("h2o2ram", "k4v8", "--resolve-only", "1", "--api", "batch",
                                          "--batch-size", "16"))
        assert refused.returncode == 2 and "batch" in refused.stderr, refused.stderr
        misses = run(patched, *arguments("h2o2ram", "k4v8", "--resolve-only", "1", "--hit-ppm", "500000",
                                         "--read-ppm", "1000000", "--miss-keys", "100"))
        assert misses.returncode == 2 and "miss" in misses.stderr, misses.stderr
        # A planner-cache miss is rejected at resolve, with the missing entries.
        cold = root / "cold" / patched.name
        cold.parent.mkdir()
        shutil.copy2(patched, cold)
        rejected = run(cold, *arguments("h2o2ram", "k4v8", "--resolve-only", "1"))
        assert rejected.returncode == 2 and "has no entry for (n 128" in rejected.stderr, rejected.stderr
        assert rejected.stdout == "", rejected.stdout
        # A cold cache fails a trial instead of timing candidates, and prints
        # nothing to stdout (the worker's JSON channel).
        failed = trial(cold, "h2o2ram", "k4v8", root / "cold-trial")
        assert failed.returncode == 2 and "planner cache" in failed.stderr and failed.stdout == "", failed
        assert not (cold.parent / "hash_map.bin16").exists(), "a trial wrote the planner cache"
        # Verified smoke rows at each shape, on both builds.
        for worker, scheme in ((patched, "h2o2ram"), (shipped, "h2o2ram_shipped")):
            for shape in SHAPES:
                output = root / f"{scheme}-{shape}"
                result = trial(worker, scheme, shape, output, "--placement", "near_far")
                assert result.returncode == 0, (scheme, shape, result.stderr[-2000:])
                metadata = json.loads((output / "worker.json").read_text())
                assert metadata["correctness_verified"] and metadata["verified_reads"] > 0, metadata
                assert metadata["maintenance_coverage"]["counter"] == "buffer_appends", metadata
                # Maintenance markers: bracketed rebuild accesses, on the trial clock.
                markers = (output / "markers.csv").read_text().splitlines()
                assert markers[0] == "role,level,start_ns,end_ns", markers[:1]
                assert metadata["maintenance_markers"] == {
                    "source": "bracketed_buffer_full_access_includes_lookup", "spans": len(markers) - 1}, metadata
                assert all(line.startswith("h2o2ram_rebuild,") for line in markers[1:]), markers[1:3]
                placement = json.loads((output / "placement.json").read_text())
                assert placement["all_planned_roles_verified"] and not placement["violations"], placement
                resolved = json.loads((output / "resolved.json").read_text())
                assert resolved["placement_policy"] == "baseline_self_placed", resolved
                decode(WorkerResolution, resolved)  # what `run`'s attempt check reads
                baseline = json.loads((output / "baseline.json").read_text())
                assert baseline["digest_collisions"] == 0 and baseline["index"] == {
                    "k4v8": "key_value", "k8v48": "key_value_bit63_cleared", "k32v1024": "aes_cmac_63"}[shape]
                print(f"{scheme} {shape}: verified {metadata['verified_reads']} reads")
        # (32, 1024): a planted digest collision fails the row with its count.
        planted = root / "planted"
        result = trial(patched, "h2o2ram", "k32v1024", planted, "--override.h2o2ram.test_digest_bits", "12")
        assert result.returncode == 2 and "fill keys share a 63-bit index digest" in result.stderr, result.stderr
        collisions = json.loads((planted / "baseline.json").read_text())["digest_collisions"]
        assert collisions >= 65536 - 4096, collisions
        assert not (planted / "summary.json").exists(), "an aliased row reached measurement"
        print(f"planted digest collision: {collisions} keys share an index")
        # Both builds return identical results on one request sequence.
        checksums = []
        for worker, scheme in ((patched, "h2o2ram"), (shipped, "h2o2ram_shipped")):
            output = root / f"same-{scheme}"
            result = run(worker, *arguments(scheme, "k8v48", "--output", str(output), "--max-requests", "40000",
                                            "--measurement-ns", "600000000000", "--workload-seed", "4"))
            summary = json.loads((output / "summary.json").read_text())
            assert result.returncode == 3 and summary["request_cap_reached"] and summary["completed"] == 40000, \
                result.stderr
            metadata = json.loads((output / "worker.json").read_text())
            assert metadata["correctness_verified"]
            checksums.append(metadata["checksum"])
        assert checksums[0] == checksums[1], checksums
        print("patched and shipped builds agree on 40000 requests")
    return 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:3]))
