"""CLI check for the checkpoint reducer (oram_bench_aggregate), run by CTest.

oram_bench_statistics_test --write-fixture writes two checkpoint files with
known contents; the reducer's JSON summary (counts, latency sums and
percentiles, censoring flags) must match them exactly, and invalid input must
fail without printing a partial summary.  No clocks, maps, or measurements.
"""
import csv
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile

aggregate, fixture = sys.argv[1:]
with tempfile.TemporaryDirectory() as directory:
    subprocess.run([fixture, "--write-fixture", directory], check=True)
    paths = [str(Path(directory) / f"{i}.bin") for i in range(2)]
    def run(*args, success=True):
        result = subprocess.run([aggregate, *args], capture_output=True, text=True)
        assert result.returncode == (0 if success else 2), result.stderr
        if not success:
            assert not result.stdout, "invalid input published a partial summary"
        return result.stdout
    data = json.loads(run(*paths))
    assert data["offered"] == 8 and data["completed_requests"] == 4
    assert data["completed_batches"] == 2 and data["outstanding"] == 1
    assert data["stable_queue"] is None and not data["uncensored"]
    assert data["response"]["sum_ns"] == 295
    assert data["queue"]["sum_ns"] == 65
    assert data["service"]["sum_ns"] == 110
    assert data["service"]["weighting"] == "batch_call"
    assert data["service"]["count"] == 2 and data["response"]["count"] == 4
    assert data["response"]["p95_ns"] == 90
    assert not data["response"]["p999_sufficient_samples"]
    rows = list(csv.DictReader(io.StringIO(run("--format", "csv", *paths))))
    assert len(rows) == 3 and rows[2]["weighting"] == "batch_call"
    assert int(rows[0]["p95_ns"]) == data["response"]["p95_ns"]
    # --blocks: whole summary unchanged, plus per-block statistics and the across-block spread.
    withblocks = json.loads(run("--blocks", *paths))
    spread = withblocks.pop("block_spread"); blocks = withblocks.pop("blocks")
    assert withblocks == data, "--blocks changed the whole-repetition summary"
    assert [b["interval_id"] for b in blocks] == [0, 1] and blocks[1]["begin_ns"] == blocks[0]["end_ns"] == 100
    assert [b["completed_requests"] for b in blocks] == [3, 1]
    assert [b["throughput_ops_per_second"] for b in blocks] == [3e7, 1e7]
    assert [b["response"]["sum_ns"] for b in blocks] == [240, 55] and blocks[0]["response"]["count"] == 3
    assert blocks[0]["response"]["maximum_ns"] == 90 and blocks[1]["response"]["p50_ns"] == 55
    assert blocks[0]["service"]["sum_ns"] == 60 and blocks[1]["queue"]["mean_ns"] == 5
    assert not blocks[0]["response"]["p999_sufficient_samples"]
    assert "across_time_blocks" in spread["scope"] and "confidence" not in json.dumps(spread)
    tp = spread["throughput_ops_per_second"]
    assert tp["blocks"] == 2 and tp["mean"] == 2e7 and tp["minimum"] == 1e7 and tp["maximum"] == 3e7
    assert abs(tp["stddev"] - 2 ** .5 * 1e7) < 1e-3
    mx = spread["response"]["maximum_ns"]
    assert mx["blocks"] == 2 and mx["minimum"] == 55 and mx["maximum"] == 90 and mx["mean"] == 72.5
    assert spread["service"]["mean_ns"]["mean"] == 55 and spread["response"]["p99_ns"]["sufficient_blocks"] == 0
    single = json.loads(run("--blocks", paths[0]))["block_spread"]["throughput_ops_per_second"]
    assert single["blocks"] == 1 and single["stddev"] is None
    run("--blocks", "--events", paths[0], success=False)
    run("--blocks", "--format", "csv", *paths, success=False)
    run(success=False)
    run("--unknown", success=False)
    run("--format", "yaml", *paths, success=False)
    run(paths[0], paths[0], success=False)
    run(paths[1], paths[0], success=False)
    run(paths[1], success=False)
    broken = Path(directory) / "broken.bin"
    broken.write_bytes(Path(paths[0]).read_bytes()[:-1])
    run(str(broken), success=False)
    broken.write_bytes(Path(paths[0]).read_bytes() + b"extra")
    run(str(broken), success=False)
repetitions = json.loads(run("--repeat", "10", "100", "200", "--repeat", "20", "100", "400"))
assert repetitions["repetitions"] == 2
assert repetitions["caller"]["median_ops_per_second"] == 150_000_000
assert repetitions["drained"]["pooled_ops_per_second"] == 50_000_000
run("--repeat", "1", "0", "2", success=False)
print("Synthetic aggregator CLI fixtures passed")
