#!/usr/bin/env python3
"""Exercise the benchmark CLI and accounting against its real ORAM backends."""

import json
import math
import re
import subprocess
import sys


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def invoke(executable, args):
    return subprocess.run([executable, *args], text=True, capture_output=True, timeout=30)


def close(actual, expected, name):
    require(math.isclose(actual, expected, rel_tol=1e-10, abs_tol=1e-12), name)


def run_case(executable, **overrides):
    config = dict(accounts=8, storage_entries=2, q=2, k=2, account_top=0,
                  storage_top=0, top_backend="tree", mode="batch", warmup=1, samples=2)
    config.update(overrides)
    args = []
    for key, value in config.items():
        args.extend(["--" + key.replace("_", "-"), str(value)])
    process = invoke(executable, args)
    require(process.returncode == 0, f"{args}: {process.stderr}")
    require(not process.stderr, f"unexpected benchmark stderr: {process.stderr}")
    data = json.loads(process.stdout)
    require(data["schema"] == "ethereum_mpt_read_benchmark_v1", "JSON schema")
    for key in config.keys() - {"warmup", "samples"}:
        require(data[key] == config[key], f"configuration echo: {key}")
    require(data["page_bytes"] in (768, 1024, 2048), "supported page width")
    require(re.fullmatch(r"0x[0-9a-f]{64}", data["state_root"]), "canonical root encoding")
    require(data["bulk_backend"] == "tree", "bulk backend")
    require(data["caller_threads"] == 1 and data["worker_threads"] == 0, "worker budget")
    require(data["request_horizon_per_map"] == 2**32, "request horizon")
    require(data["queue_fill_latency_ns"] is None and
            data["physical_oram_traffic_bytes"] is None, "unmeasured quantities")
    require(data["warmup_batches"] == config["warmup"] and
            data["measured_batches"] == config["samples"] and
            data["verified_batches"] == config["warmup"] + config["samples"],
            "every warmup and measured response must pass canonical proof verification")

    q, k = config["q"], config["k"]
    account_top, storage_top = config["account_top"], config["storage_top"]
    rounds = [account_top, storage_top if k else 0,
              65 - account_top + (65 - storage_top if k else 0)]
    reads = [q * account_top, q * k * storage_top,
             q * (65 - account_top) + q * k * (65 - storage_top)]
    require(data["round_calls_per_batch"] == rounds, "fixed per-tier round schedule")
    require(data["page_reads_per_batch"] == reads, "fixed per-tier page schedule")
    require(data["oram_calls_per_batch"] == (reads if config["mode"] == "scalar" else rounds),
            "scalar/batch ORAM call distinction")
    require(sum(reads) == 65 * q * (1 + k), "total lane schedule")
    require(data["logical_page_read_bytes_per_batch"] == sum(reads) * data["page_bytes"],
            "logical page traffic")
    require(data["node_hash_permutations_per_batch"] == 4 * sum(reads), "fixed Keccak work")
    require(data["proof_slot_bytes"] == 34840 * q * (1 + k), "fixed proof allocation")
    require(data["request_frame_bytes"] == 128 + q * (20 + 32 * k), "request frame width")
    require(data["response_frame_bytes"] == 128 + q * (34980 + 34920 * k),
            "response frame width")

    samples = data["samples"]
    require(len(samples) == config["samples"], "warmups excluded from measured samples")
    scalar_fields = ("batch_service_ns", "request_decode_hash_ns", "traversal_ns",
                     "local_traversal_ns", "response_encode_ns")
    for sample in samples:
        require(all(isinstance(sample[key], int) and sample[key] >= 0 for key in scalar_fields),
                "nonnegative integral sample times")
        require(sample["batch_service_ns"] > 0, "nonzero service time")
        require(len(sample["page_read_ns"]) == 3 and
                all(isinstance(value, int) and value >= 0 for value in sample["page_read_ns"]),
                "three nonnegative per-tier read times")
        require(sample["batch_service_ns"] == sample["request_decode_hash_ns"] +
                sample["traversal_ns"] + sample["response_encode_ns"], "service time partition")
        require(sample["traversal_ns"] == sample["local_traversal_ns"] +
                sum(sample["page_read_ns"]), "local/ORAM traversal partition")
        for tier, count in enumerate(reads):
            require(count != 0 or sample["page_read_ns"][tier] == 0, "inactive tier timing")
    for key in scalar_fields:
        require(data["total_" + key] == sum(sample[key] for sample in samples),
                "sample aggregate: " + key)
    require(data["total_page_read_ns"] ==
            [sum(sample["page_read_ns"][tier] for sample in samples) for tier in range(3)],
            "per-tier timing aggregates")
    times = sorted(sample["batch_service_ns"] for sample in samples)
    for percentile in (50, 95, 99):
        rank = (len(times) * percentile + 99) // 100
        require(data[f"batch_service_p{percentile}_ns"] == times[rank - 1],
                f"nearest-rank p{percentile}")
    close(data["requests_per_service_second"],
          1e9 * q * len(samples) / data["total_batch_service_ns"], "service throughput")

    tiers = data["tiers"]
    require([tier["name"] for tier in tiers] == ["account_top", "storage_top", "bulk"],
            "tier identity and order")
    enabled = [account_top != 0, storage_top != 0, True]
    for index, tier in enumerate(tiers):
        backend = config["top_backend"] if index < 2 else "tree"
        require(tier["backend"] == (backend if enabled[index] else "disabled"),
                "configured backend selection")
        require(tier["R"] == tier["S"] + 8 * tier["N"] + 12 * (tier["E"] + tier["A"]),
                "record metadata accounting")
        require(tier["requested_capacity"] == tier["P"] + int(enabled[index]),
                "one dummy page for each enabled tier")
        require(tier["allocated_capacity"] >= tier["requested_capacity"], "allocated capacity")
        require(tier["R"] <= tier["P"] * data["page_bytes"], "packed records fit")
        close(tier["utilization"], tier["R"] / (tier["P"] * data["page_bytes"])
              if tier["P"] else 0, "packing utilization")
        if not enabled[index]:
            require(tier["arena_bytes"] == 0 and tier["allocated_capacity"] == 0,
                    "disabled tier has no map allocation")
    require(data["oram_arena_bytes"] == sum(tier["arena_bytes"] for tier in tiers),
            "total ORAM arena")
    require(data["packed_page_value_bytes"] ==
            sum(tier["requested_capacity"] for tier in tiers) * data["page_bytes"],
            "total packed page bytes including dummies")
    require(data["packing_slack_bytes"] ==
            sum(tier["P"] * data["page_bytes"] - tier["R"] for tier in tiers), "packing slack")
    close(data["oram_arena_to_page_value_ratio"],
          data["oram_arena_bytes"] / data["packed_page_value_bytes"], "ORAM expansion ratio")
    require(data["process_peak_rss_bytes"] > 0, "process peak RSS")
    require(isinstance(data["final_drain_ns"], int) and data["final_drain_ns"] >= 0,
            "pending backend work completes before a successful result")
    return data


def main(executable):
    # Q=2 includes one nonempty-storage account and one empty-storage account;
    # K=2 includes one present slot and one absent slot for the first account.
    batch = run_case(executable)
    scalar = run_case(executable, mode="scalar")
    tiered = run_case(executable, account_top=2, storage_top=1, top_backend="hierarchical")
    accounts_only = run_case(executable, k=0, samples=1)
    empty = run_case(executable, accounts=0, storage_entries=0, samples=1,
                     account_top=2, storage_top=1, top_backend="hierarchical")
    # Success means the executable checked every returned account/storage proof
    # byte-for-byte against the canonical reference, outside its timed region.
    for result in (scalar, tiered, accounts_only):
        require(result["state_root"] == batch["state_root"], "backend/mode-independent root")
        for field in ("S", "N", "E", "A", "R"):
            require(sum(tier[field] for tier in result["tiers"]) ==
                    sum(tier[field] for tier in batch["tiers"]), "same canonical packed records")
    require(empty["state_root"] ==
            "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421",
            "canonical Ethereum empty state root")
    require(all(tier["N"] == 0 and tier["P"] == 0 for tier in empty["tiers"]),
            "empty dataset uses only dummy pages")
    require(accounts_only["round_calls_per_batch"] == [0, 0, 65], "K=0 omits storage phase")

    invalid = (["--q", "0"], ["--samples", "0"], ["--samples", "1000001"],
               ["--accounts", "1000001"], ["--warmup", "-1"], ["--q", "1x"],
               ["--k", "184467440737095516160"], ["--k", "1000000"],
               ["--account-top", "5"], ["--storage-top", "5"],
               ["--mode", "parallel"], ["--top-backend", "auto"],
               ["--unknown", "1"], ["--q"])
    for args in invalid:
        process = invoke(executable, args)
        require(process.returncode != 0 and "ethereum_mpt_benchmark:" in process.stderr and
                not process.stdout, f"invalid arguments accepted or emitted result: {args}")
    help_result = invoke(executable, ["--help"])
    require(help_result.returncode == 0 and "Usage:" in help_result.stdout, "CLI help")
    print("Benchmark CLI/JSON checks passed: five verified ORAM scenarios and invalid inputs")


if __name__ == "__main__":
    require(len(sys.argv) == 2, "usage: benchmark_test.py /path/to/ethereum_mpt_benchmark")
    main(sys.argv[1])
