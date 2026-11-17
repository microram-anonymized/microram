#!/usr/bin/env python3
"""Check the update benchmark's real ORAM workloads and published accounting."""

import json
import math
import re
import subprocess
import sys


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def close(actual, expected, name):
    require(math.isclose(actual, expected, rel_tol=1e-10, abs_tol=1e-12), name)


def invoke(executable, args):
    return subprocess.run([executable, *args], text=True, capture_output=True, timeout=60)


def unsigned(value, name):
    require(type(value) is int and value >= 0, name + " must be a nonnegative integer")


def canonical_hash(value, name):
    require(isinstance(value, str) and re.fullmatch(r"0x[0-9a-f]{64}", value),
            name + " must use canonical hash encoding")


def counts(value, name):
    require(isinstance(value, list) and len(value) == 3, name + " must have three tiers")
    for item in value:
        unsigned(item, name)


def run_case(executable, **overrides):
    config = dict(accounts=8, storage_entries=2, q=2, k=1, blocks=3,
                  read_batches_per_block=1, delta_accounts=1, storage_changes=1,
                  retained_blocks=2, page_headroom=16, compact_after_updates=0,
                  compact_at_fullness_percent=0, compact_at_dead_bytes_percent=0,
                  account_top=3, storage_top=0, top_backend="tree",
                  update_mode="incremental")
    config.update(overrides)
    args = []
    for key, value in config.items():
        args.extend(["--" + key.replace("_", "-"), str(value)])
    process = invoke(executable, args)
    require(process.returncode == 0, f"{args}: {process.stderr}")
    require(not process.stderr, f"unexpected benchmark stderr: {process.stderr}")
    data = json.loads(process.stdout)
    require(data["schema"] == "ethereum_mpt_update_benchmark_v1", "JSON schema")
    for key, value in config.items():
        require(data[key] == value, f"configuration echo: {key}")
    validate_result(data, config)
    return data


def validate_result(data, config):
    # Detailed timing and publication checks are kept in one place so every
    # backend and update policy is held to the same accounting contract.
    require(data["page_bytes"] in (768, 1024, 2048), "supported page width")
    require(data["canonical_builder"] ==
            ("path_copy" if config["update_mode"] == "incremental" else "full_rebuild"),
            "canonical preparation strategy is explicit alongside page publication mode")
    require(data["caller_threads"] == 1 and data["worker_threads"] == 0, "worker budget")
    require(data["queue_fill_latency_ns"] is None and
            data["physical_oram_traffic_bytes"] is None, "unmeasured quantities")
    q, k = config["q"], config["k"]
    account_top, storage_top = config["account_top"], config["storage_top"]
    rounds = [account_top, storage_top if k else 0,
              65 - account_top + (65 - storage_top if k else 0)]
    reads = [q * account_top, q * k * storage_top,
             q * (65 - account_top) + q * k * (65 - storage_top)]
    require(data["round_calls_per_batch"] == rounds, "fixed per-tier round schedule")
    require(data["page_reads_per_batch"] == reads, "fixed per-tier page schedule")
    require(sum(reads) == 65 * q * (1 + k), "complete lane schedule")
    require(data["request_frame_bytes"] == 128 + q * (20 + 32 * k), "request frame width")
    require(data["response_frame_bytes"] == 128 + q * (34980 + 34920 * k),
            "response frame width")

    samples = data["samples"]
    require(len(samples) == config["blocks"], "one sample per published block")
    batch_times = []
    enabled = [account_top != 0, storage_top != 0, True]
    for index, sample in enumerate(samples, 1):
        require(sample["block_number"] == index, "sequential block numbers")
        canonical_hash(sample["block_id"], "block ID")
        canonical_hash(sample["state_root"], "state root")
        require(sample["publication"] in ("append", "replacement"), "publication kind")
        require(type(sample["compaction"]) is bool, "public compaction flag")
        require(not sample["compaction"] or sample["publication"] == "replacement",
                "compaction constructs fresh maps")
        require(sample["generation"] >= 1, "published generation identifier")
        if index > 1:
            previous = samples[index - 2]
            require(sample["block_id"] != previous["block_id"], "distinct block identities")
            require(sample["generation"] == previous["generation"]
                    if sample["publication"] == "append" else
                    sample["generation"] > previous["generation"],
                    "appends preserve generation; replacements advance it")
        scalar_fields = ("prepare_ns", "publish_ns", "update_pause_ns", "fresh_load_ns",
                         "completion_ns", "read_service_total_ns", "scheduled_service_lag_ns",
                         "arrival_to_publish_wall_ns", "overlap_oram_arena_bytes",
                         "oram_arena_bytes", "packed_page_value_bytes", "packing_slack_bytes",
                         "builder_payload_bytes_staged", "builder_payload_bytes_published")
        for key in scalar_fields:
            unsigned(sample[key], key)
        require(sample["update_pause_ns"] == sample["prepare_ns"] + sample["publish_ns"],
                "complete serialized update pause")
        require(sample["update_pause_ns"] > 0, "nonzero update pause")
        require(len(sample["read_service_ns"]) == config["read_batches_per_block"],
                "configured old-head read workload")
        for value in sample["read_service_ns"]:
            unsigned(value, "read service duration")
            require(value > 0, "nonzero read service duration")
        batch_times.extend(sample["read_service_ns"])
        require(sample["read_service_total_ns"] == sum(sample["read_service_ns"]),
                "per-block read time total")
        require(sample["scheduled_service_lag_ns"] == sample["update_pause_ns"] +
                sample["read_service_total_ns"], "scheduled lag includes updates and old-head reads")
        require(sample["arrival_to_publish_wall_ns"] >= sample["scheduled_service_lag_ns"],
                "wall lag includes timed service intervals")
        require(sample["pending_block_lag"] == 1 and sample["published_block_lag"] == 0,
                "new observed head remains pending until publication")
        retained = min(config["retained_blocks"], index + 1)
        require(sample["retained_blocks"] == retained and sample["validation_batches"] == retained,
                "every retained root gets a post-publication proof check")
        require(sample["overlap_oram_arena_bytes"] >= sample["oram_arena_bytes"] > 0,
                "overlapping arenas include the published maps")
        require(sample["packed_page_value_bytes"] > 0 and
                sample["packing_slack_bytes"] <= sample["packed_page_value_bytes"],
                "packing slack is bounded by packed page values")

        for key in ("append_write_ns", "page_read_ns", "fresh_loaded_pages", "appended_pages",
                    "append_oram_calls", "allocated_pages", "page_capacities",
                    "live_record_bytes", "dead_record_bytes"):
            counts(sample[key], key)
        require(sample["packed_page_value_bytes"] ==
                sum(sample["allocated_pages"]) * data["page_bytes"],
                "published allocated pages include dummy pages and exclude unused capacity")
        require(sample["packing_slack_bytes"] == sum(
            (sample["allocated_pages"][tier] - int(active)) * data["page_bytes"] -
            sample["live_record_bytes"][tier] - sample["dead_record_bytes"][tier]
            for tier, active in enumerate(enabled)),
            "dead bytes are physical unreachable records, excluding packing slack and dummy pages")
        for tier in range(3):
            require(sample["allocated_pages"][tier] <= sample["page_capacities"][tier],
                    "published pages fit requested capacity")
        if sample["publication"] == "replacement":
            require(sample["dead_record_bytes"] == [0, 0, 0],
                    "fresh generations contain only retained reachable records")
        require(sample["append_oram_calls"] ==
                [(pages + 15) // 16 for pages in sample["appended_pages"]],
                "append uploads use public tiles of at most sixteen pages")
        require(sum(sample["page_read_ns"]) <= sample["read_service_total_ns"],
                "adapter read timing fits inside read service")
        require(sample["fresh_load_ns"] <= sample["prepare_ns"],
                "fresh map loading occurs during preparation")
        require(sum(sample["append_write_ns"]) + sample["completion_ns"] <=
                sample["update_pause_ns"], "write and completion timing fits inside update pause")
        if sample["publication"] == "append":
            require(sample["fresh_load_ns"] == 0 and sample["fresh_loaded_pages"] == [0, 0, 0],
                    "append publication does not construct fresh maps")
        else:
            require(sample["appended_pages"] == [0, 0, 0] and
                    sample["append_oram_calls"] == [0, 0, 0] and
                    sample["append_write_ns"] == [0, 0, 0],
                    "replacement pages are counted as fresh loads")
            require(sample["fresh_load_ns"] > 0 and sum(sample["fresh_loaded_pages"]) > 0,
                    "replacement performs a fresh load")
        for tier, active in enumerate(enabled):
            if not active:
                require(all(sample[key][tier] == 0 for key in
                            ("append_write_ns", "page_read_ns", "fresh_loaded_pages",
                             "appended_pages", "append_oram_calls", "allocated_pages",
                             "page_capacities", "live_record_bytes", "dead_record_bytes")),
                        "disabled tier accounting")
            if reads[tier] == 0 or config["read_batches_per_block"] == 0:
                require(sample["page_read_ns"][tier] == 0, "no workload reads means no read timing")

    require(data["final_state_root"] == samples[-1]["state_root"], "final published root")
    require(data["measured_batches"] == len(batch_times) ==
            config["blocks"] * config["read_batches_per_block"], "measured workload batch count")
    require(data["validation_batches"] == sum(sample["validation_batches"] for sample in samples),
            "retained-root probes are counted separately")
    require(data["verified_batches"] == data["measured_batches"] + data["validation_batches"],
            "all workload and validation responses are verified")
    require(data["total_read_service_ns"] == sum(batch_times), "total read service time")
    require(data["total_update_pause_ns"] == sum(sample["update_pause_ns"] for sample in samples),
            "total update pause")
    require(data["total_scheduled_service_ns"] ==
            data["total_read_service_ns"] + data["total_update_pause_ns"], "scheduled service total")
    require(data["total_compaction_pause_ns"] ==
            sum(sample["update_pause_ns"] for sample in samples if sample["compaction"]),
            "compaction pause includes preparation and publication")
    close(data["compaction_duty_cycle"],
          data["total_compaction_pause_ns"] / data["total_scheduled_service_ns"],
          "compaction duty cycle denominator")
    close(data["requests_per_scheduled_service_second"],
          1e9 * q * len(batch_times) / data["total_scheduled_service_ns"],
          "throughput includes the complete update pause")
    for percentile in (50, 95, 99):
        expected = (sorted(batch_times)[(len(batch_times) * percentile + 99) // 100 - 1]
                    if batch_times else None)
        require(data[f"read_service_p{percentile}_ns"] == expected,
                f"nearest-rank p{percentile}, or null for no measured reads")
    require(data["incremental_publications"] ==
            sum(sample["publication"] == "append" for sample in samples), "append count")
    require(data["replacement_publications"] ==
            sum(sample["publication"] == "replacement" for sample in samples), "replacement count")
    require(data["compactions"] == sum(sample["compaction"] for sample in samples),
            "compaction count")
    for key in ("appended_pages", "fresh_loaded_pages"):
        counts(data[key], key)
        require(data[key] == [sum(sample[key][tier] for sample in samples) for tier in range(3)],
                "update-only page aggregate: " + key)
    counts(data["initial_loaded_pages"], "initial_loaded_pages")
    require(all((count > 0) == active for count, active in zip(data["initial_loaded_pages"], enabled)),
            "initial loading covers exactly the enabled maps")
    require(data["logical_update_write_bytes"] == data["page_bytes"] *
            (sum(data["fresh_loaded_pages"]) + sum(data["appended_pages"])),
            "logical update writes include fresh pages and appended pages")

    builder = data["builder_payload"]
    payload_fields = ("public_state_bytes", "canonical_trie_rlp_bytes", "packed_image_bytes",
                      "staged_upload_bytes", "identity_bytes")
    for key in (*payload_fields, "payload_bytes", "retained_versions"):
        unsigned(builder[key], "builder " + key)
    require(builder["payload_bytes"] == sum(builder[key] for key in payload_fields),
            "builder payload components sum without arena bytes")
    require(builder["payload_bytes"] == samples[-1]["builder_payload_bytes_published"],
            "final builder payload matches the final publication")
    require(builder["retained_versions"] == min(config["retained_blocks"], config["blocks"] + 1),
            "final builder counts only current retained versions")
    require(builder["staged_upload_bytes"] == 0, "publication releases staged uploads")
    require(builder["identity_bytes"] == (config["blocks"] + 1) * (64 + 32),
            "public identity tombstones survive state retention pruning")
    unsigned(data["sampled_peak_builder_payload_bytes"], "sampled peak builder payload")
    require(data["sampled_peak_builder_payload_bytes"] >= max(
        sample[key] for sample in samples
        for key in ("builder_payload_bytes_staged", "builder_payload_bytes_published")),
        "sampled builder peak includes every observed preparation and publication")

    tiers = data["tiers"]
    require([tier["name"] for tier in tiers] == ["account_top", "storage_top", "bulk"],
            "final tier identity and order")
    for index, tier in enumerate(tiers):
        backend = config["top_backend"] if index < 2 else "tree"
        require(tier["backend"] == (backend if enabled[index] else "disabled"),
                "final configured backend selection")
        require(tier["R"] == tier["S"] + 8 * tier["N"] + 12 * (tier["E"] + tier["A"]),
                "final packed record metadata identity")
        require(tier["R"] <= tier["P"] * data["page_bytes"], "final records fit packed pages")
        require(tier["R"] == tier["live_record_bytes"] + tier["dead_record_bytes"],
                "final packed records partition into live and dead bytes")
        require(tier["allocated_pages"] == tier["P"] + int(enabled[index]),
                "final allocated pages include dummy pages")
        require(tier["allocated_capacity"] >= tier["requested_capacity"] >=
                tier["P"] + int(enabled[index]), "final capacity contains every packed page and dummy")
        if not enabled[index]:
            require(tier["requested_capacity"] == tier["allocated_capacity"] ==
                    tier["arena_bytes"] == tier["P"] == 0, "disabled final tier has no allocation")
    last = samples[-1]
    for key in ("allocated_pages", "live_record_bytes", "dead_record_bytes"):
        require(last[key] == [tier[key] for tier in tiers], "final occupancy matches samples: " + key)
    require(last["page_capacities"] == [tier["requested_capacity"] for tier in tiers],
            "occupancy capacities are requested usable capacities")
    require(last["oram_arena_bytes"] == sum(tier["arena_bytes"] for tier in tiers),
            "final arena equals the sum of tier arenas")
    require(last["packed_page_value_bytes"] == data["page_bytes"] *
            sum(tier["P"] + int(enabled[index]) for index, tier in enumerate(tiers)),
            "final page values include one dummy per enabled map")
    require(last["packing_slack_bytes"] ==
            sum(tier["P"] * data["page_bytes"] - tier["R"] for tier in tiers),
            "final packing slack excludes dummy pages and unused capacity")
    require(builder["packed_image_bytes"] == last["packed_page_value_bytes"],
            "final public packed image matches published page values")
    require(data["peak_oram_arena_bytes"] >=
            max(sample["overlap_oram_arena_bytes"] for sample in samples), "peak arena accounting")
    require(data["peak_page_value_bytes"] >=
            max(sample["packed_page_value_bytes"] for sample in samples), "peak page-value accounting")
    require(data["process_peak_rss_bytes"] > 0, "process peak RSS")


def main(executable):
    append = run_case(executable)
    replacement = run_case(executable, update_mode="replacement")
    capacity = run_case(executable, page_headroom=0)
    periodic = run_case(executable, compact_after_updates=1)
    no_op = run_case(executable, delta_accounts=0)
    accounts_only = run_case(executable, k=0, read_batches_per_block=0)
    hierarchical = run_case(executable, storage_top=1, top_backend="hierarchical")
    fullness = run_case(executable, compact_at_fullness_percent=1)
    dead_bytes = run_case(executable, retained_blocks=1, compact_at_dead_bytes_percent=1)
    unchanged_full = run_case(executable, delta_accounts=0, page_headroom=0,
                              compact_at_fullness_percent=1, compact_at_dead_bytes_percent=1)

    expected_roots = [sample["state_root"] for sample in append["samples"]]
    for result in (replacement, capacity, periodic, accounts_only, hierarchical, fullness, dead_bytes):
        require([sample["state_root"] for sample in result["samples"]] == expected_roots,
                "identical deltas have backend, publication-policy and read-independent roots")
    require(append["incremental_publications"] == 3 and append["compactions"] == 0 and
            append["replacement_publications"] == 0, "ample headroom permits every append")
    require(sum(append["appended_pages"]) > 0 and append["fresh_loaded_pages"] == [0, 0, 0],
            "changed-state appends write pages without a fresh map")
    require(replacement["replacement_publications"] == 3 and replacement["compactions"] == 0
            and replacement["incremental_publications"] == 0, "replacement baseline")
    require(capacity["replacement_publications"] == 3 and capacity["compactions"] == 3 and
            capacity["incremental_publications"] == 0, "zero headroom forces capacity compactions")
    require([sample["compaction"] for sample in periodic["samples"]] == [False, True, False]
            and periodic["incremental_publications"] == 2, "public append-count compaction interval")
    require(no_op["appended_pages"] == [0, 0, 0] and no_op["compactions"] == 0 and
            no_op["incremental_publications"] == 3, "no-op deltas publish without page uploads")
    require(len({sample["state_root"] for sample in no_op["samples"]}) == 1,
            "no-op blocks preserve the state root")
    require(no_op["final_state_root"] != append["final_state_root"], "changed workload changes state")
    require(accounts_only["measured_batches"] == 0 and accounts_only["verified_batches"] > 0,
            "ingestion-only workloads still verify retained proofs")
    require(fullness["compactions"] == 3 and fullness["incremental_publications"] == 0,
            "public fullness threshold compacts growing tiers before capacity exhaustion")
    require(dead_bytes["compactions"] == 3 and dead_bytes["incremental_publications"] == 0,
            "dead-byte threshold measures roots after retention pruning")
    require(unchanged_full["compactions"] == 0 and unchanged_full["incremental_publications"] == 3,
            "unchanged full tiers do not cause repeated compaction")

    invalid = (["--accounts", "0"], ["--blocks", "0"], ["--retained-blocks", "0"],
               ["--q", "0"], ["--blocks", "1000001"], ["--accounts", "1000001"],
               ["--read-batches-per-block", "-1"], ["--q", "1x"],
               ["--accounts", "1", "--delta-accounts", "2"],
               ["--blocks", "1000000", "--read-batches-per-block", "2"],
               ["--blocks", "1000000", "--retained-blocks", "1000000",
                "--read-batches-per-block", "0"],
               ["--k", "184467440737095516160"], ["--k", "1000000"],
               ["--account-top", "5"], ["--storage-top", "5"],
               ["--compact-at-fullness-percent", "101"],
               ["--compact-at-dead-bytes-percent", "101"],
               ["--compact-at-fullness-percent", "-1"],
               ["--compact-at-dead-bytes-percent", "1.5"],
               ["--update-mode", "async"], ["--top-backend", "auto"],
               ["--unknown", "1"], ["--q"])
    for args in invalid:
        process = invoke(executable, args)
        require(process.returncode != 0 and "ethereum_mpt_update_benchmark:" in process.stderr
                and not process.stdout, f"invalid arguments accepted or emitted result: {args}")
    help_result = invoke(executable, ["--help"])
    require(help_result.returncode == 0 and "Usage:" in help_result.stdout, "CLI help")
    print("Update benchmark checks passed: ten verified ORAM scenarios and invalid inputs")


if __name__ == "__main__":
    require(len(sys.argv) == 2, "usage: update_benchmark_test.py /path/to/benchmark")
    main(sys.argv[1])
