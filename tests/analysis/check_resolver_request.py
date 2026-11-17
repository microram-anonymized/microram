"""Cross-language check of the resolver request (run by CTest).

The Python schema (analysis/oram_bench/schema.py) and the C++ worker parser
(benchmarks/support/worker.hpp) must agree on every resolve-only request: the
fixture executable (oram_bench_resolver_request_fixture.cpp) parses the
worker's command line and prints the request, which must decode in Python.
The fixture builds no backend and reads no clock.
"""
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from analysis.oram_bench.codec import decode
from analysis.oram_bench.schema import ResolverRequest


def check(executable):
    for scheme in ("auto", "tree", "hierarchical_incremental", "hierarchical_synchronous"):
        for key, value in ((4, 8), (8, 48), (32, 1024)):
            for mode, count in (("scalar", 1), ("batch", 16)):
                args = ["--scheme", scheme, "--resolve-only", "1", "--cores", "4", "--api", mode,
                        "--batch-size", str(count), "--key-bytes", str(key), "--value-bytes", str(value),
                        "--override.tree.payload_monitor_wait", "false", "--override.tree.payload_spin_us", "0"]
                result = subprocess.run([executable, *args], check=True, capture_output=True, text=True)
                request = decode(ResolverRequest, json.loads(result.stdout))
                assert (request.scheme, request.key_bytes, request.value_bytes, request.api_mode,
                        request.caller_batch_size) == (scheme, key, value, mode, count)
                assert [(o.field, o.value) for o in request.overrides] == [
                    ("tree.payload_monitor_wait", "false"), ("tree.payload_spin_us", "0")]
    # The key layout is a resolver input: an index ORAM reads the dense key as its index.
    for layout in ("permuted", "dense"):
        extra = [] if layout == "permuted" else ["--key-layout", layout]
        result = subprocess.run([executable, "--resolve-only", "1", "--scheme", "tree", *extra],
                                check=True, capture_output=True, text=True)
        assert decode(ResolverRequest, json.loads(result.stdout)).key_layout == layout, layout
    bad = subprocess.run([executable, "--resolve-only", "1", "--key-layout", "sorted"], capture_output=True, text=True)
    assert bad.returncode != 0 and "key layout" in bad.stderr, bad.stderr
    # Transport-only controls and the offered rate are not resolver inputs.
    base = [executable, "--resolve-only", "1", "--scheme", "tree"]
    first = subprocess.run(base, check=True, capture_output=True, text=True).stdout
    for extra in (["--output", "/never-created"], ["--arrival", "fixed", "--rate", str(2**64 - 1)]):
        second = subprocess.run(base + extra, check=True, capture_output=True, text=True).stdout
        assert first == second, extra


if __name__ == "__main__":
    check(sys.argv[1])
