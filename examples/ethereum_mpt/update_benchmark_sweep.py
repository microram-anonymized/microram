#!/usr/bin/env python3
"""Compare public MPT update workloads in fresh processes, writing JSONL."""

import argparse
import itertools
import json
from pathlib import Path
import subprocess
import sys

from benchmark_sweep import bounded_count, integer_list, reject_constant, validate_binaries


SCHEMA = "ethereum_mpt_update_benchmark_v1"


def update_mode_list(text):
    values = text.split(",")
    if any(value not in ("incremental", "replacement") for value in values):
        raise argparse.ArgumentTypeError("update modes must be incremental or replacement")
    if len(set(values)) != len(values):
        raise argparse.ArgumentTypeError("update modes must be unique")
    return values


def cutoff(text):
    value = bounded_count(text)
    if value > 4:
        raise argparse.ArgumentTypeError("expected a tier cutoff in 0..4")
    return value


def percentage(text):
    value = bounded_count(text)
    if value > 100:
        raise argparse.ArgumentTypeError("expected a percentage in 0..100")
    return value


def make_parser():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", action="append", required=True, metavar="PATH",
                        help="update benchmark executable; repeat for separate builds")
    parser.add_argument("--q", type=lambda text: integer_list(text, 1, 1000000),
                        default=[4], help="comma-separated request counts (default: 4)")
    parser.add_argument("--k", type=lambda text: integer_list(text, 0, 1000000),
                        default=[1], help="comma-separated storage slot counts (default: 1)")
    parser.add_argument("--read-batches-per-block",
                        type=lambda text: integer_list(text, 0, 1000000), default=[2],
                        help="comma-separated read batch counts (default: 2)")
    parser.add_argument("--delta-accounts",
                        type=lambda text: integer_list(text, 0, 1000000), default=[1],
                        help="comma-separated changed account counts (default: 1)")
    parser.add_argument("--storage-changes",
                        type=lambda text: integer_list(text, 0, 1000000), default=[1],
                        help="comma-separated slot changes per changed account (default: 1)")
    parser.add_argument("--update-mode", type=update_mode_list,
                        default=["incremental", "replacement"],
                        help="comma-separated update modes (default: incremental,replacement)")
    parser.add_argument("--accounts", type=lambda text: bounded_count(text, 1), default=64)
    parser.add_argument("--storage-entries", type=bounded_count, default=8)
    parser.add_argument("--blocks", type=lambda text: bounded_count(text, 1), default=4)
    parser.add_argument("--retained-blocks", type=lambda text: bounded_count(text, 1), default=2)
    parser.add_argument("--page-headroom", type=bounded_count, default=16)
    parser.add_argument("--compact-after-updates", type=bounded_count, default=0)
    parser.add_argument("--compact-at-fullness-percent", type=percentage, default=0)
    parser.add_argument("--compact-at-dead-bytes-percent", type=percentage, default=0)
    parser.add_argument("--account-top", type=cutoff, default=3)
    parser.add_argument("--storage-top", type=cutoff, default=0)
    parser.add_argument("--top-backend", choices=("tree", "hierarchical"), default="tree")
    parser.add_argument("--output", type=Path,
                        help="write a new JSONL file exclusively; existing files are rejected")
    parser.add_argument("--dry-run", action="store_true",
                        help="emit command argument arrays without executing benchmarks")
    return parser


def configurations(options):
    """Use the same public workloads for incremental and replacement runs."""
    for binary, q, k, reads, delta, storage, mode in itertools.product(
            options.binary, options.q, options.k, options.read_batches_per_block,
            options.delta_accounts, options.storage_changes, options.update_mode):
        yield [str(binary), "--accounts", str(options.accounts),
               "--storage-entries", str(options.storage_entries),
               "--q", str(q), "--k", str(k), "--blocks", str(options.blocks),
               "--read-batches-per-block", str(reads), "--delta-accounts", str(delta),
               "--storage-changes", str(storage), "--retained-blocks", str(options.retained_blocks),
               "--page-headroom", str(options.page_headroom),
               "--compact-after-updates", str(options.compact_after_updates),
               "--compact-at-fullness-percent", str(options.compact_at_fullness_percent),
               "--compact-at-dead-bytes-percent", str(options.compact_at_dead_bytes_percent),
               "--account-top", str(options.account_top), "--storage-top", str(options.storage_top),
               "--top-backend", options.top_backend, "--update-mode", mode]


def validate_workload(parser, options):
    if any(delta > options.accounts for delta in options.delta_accounts):
        parser.error("delta-accounts must not exceed accounts")
    if any(options.blocks * reads > 1000000 for reads in options.read_batches_per_block):
        parser.error("blocks * read-batches-per-block must be at most 1000000")
    # Public client framing v1 constants from client.hpp/traversal.hpp. Both
    # complete frames and padded proofs have a default 64 MiB limit.
    limit, proof = 64 * 1024 * 1024, 65 * 536
    probe_bound = options.blocks * min(options.retained_blocks, options.blocks + 1)
    for q, k in itertools.product(options.q, options.k):
        if (128 + q * (20 + 32 * k) > limit or
                128 + q * (140 + proof + k * (80 + proof)) > limit or
                q * (1 + k) * proof > limit):
            parser.error("Q={}, K={} exceeds the benchmark's 64 MiB client/proof limits".format(q, k))
        # Match the executable's conservative whole-run read bound, including
        # retained-root probes even when no measured read batches are requested.
        # Actual maps also check initial and append writes before each access.
        for reads in options.read_batches_per_block:
            batches = options.blocks * reads + probe_bound
            if batches * 65 * q * (1 + k) >= 1 << 32:
                parser.error("Q={}, K={} exceeds the conservative 2^32 request horizon".format(q, k))


def run(options, output):
    for command in configurations(options):
        if options.dry_run:
            line = json.dumps(command, separators=(",", ":"))
        else:
            # No shell: spaces and metacharacters in executable paths are literal.
            completed = subprocess.run(command, check=True, stdout=subprocess.PIPE, text=True)
            try:
                row = json.loads(completed.stdout, parse_constant=reject_constant)
                if not isinstance(row, dict):
                    raise ValueError("expected exactly one JSON object")
                if row.get("schema") != SCHEMA:
                    raise ValueError("expected schema " + SCHEMA)
                line = json.dumps(row, separators=(",", ":"), allow_nan=False)
            except ValueError as error:
                raise ValueError("invalid benchmark output from {}: {}".format(
                    json.dumps(command), error)) from error
        output.write(line + "\n")
        output.flush()


def main(argv=None):
    parser = make_parser()
    options = parser.parse_args(argv)
    validate_workload(parser, options)
    validate_binaries(parser, options)
    output = None
    try:
        output = options.output.open("x", encoding="utf-8") if options.output else sys.stdout
        run(options, output)
    except subprocess.CalledProcessError as error:
        print("update_benchmark_sweep: command failed (exit {}): {}".format(
            error.returncode, json.dumps(error.cmd)), file=sys.stderr)
        return 1
    except (OSError, ValueError) as error:
        print("update_benchmark_sweep: " + str(error), file=sys.stderr)
        return 1
    finally:
        if output is not None and options.output:
            output.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
