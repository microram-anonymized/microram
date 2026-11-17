#!/usr/bin/env python3
"""Run public MPT benchmark configurations in separate processes, writing JSONL."""

import argparse
import itertools
import json
import os
from pathlib import Path
import subprocess
import sys


def nonnegative(text):
    try:
        value = int(text)
    except ValueError as error:
        raise argparse.ArgumentTypeError("expected an integer") from error
    if value < 0:
        raise argparse.ArgumentTypeError("expected a nonnegative integer")
    return value


def bounded_count(text, minimum=0):
    value = nonnegative(text)
    if not minimum <= value <= 1000000:
        raise argparse.ArgumentTypeError("expected an integer in {}..1000000".format(minimum))
    return value


def integer_list(text, minimum=0, maximum=None):
    try:
        values = [int(part) for part in text.split(",")]
    except ValueError as error:
        raise argparse.ArgumentTypeError("expected a comma-separated integer list") from error
    if any(value < minimum or (maximum is not None and value > maximum)
           for value in values):
        bound = "at least {}".format(minimum) if maximum is None else "in {}..{}".format(minimum, maximum)
        raise argparse.ArgumentTypeError("list values must be " + bound)
    if len(set(values)) != len(values):
        raise argparse.ArgumentTypeError("list values must be unique")
    return values


def backend_list(text):
    values = text.split(",")
    if any(value not in ("tree", "hierarchical") for value in values):
        raise argparse.ArgumentTypeError("backends must be tree or hierarchical")
    if len(set(values)) != len(values):
        raise argparse.ArgumentTypeError("backends must be unique")
    return values


def make_parser():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", action="append", required=True, metavar="PATH",
                        help="benchmark executable; repeat for separately built page widths")
    parser.add_argument("--q", type=lambda text: integer_list(text, 1), default=[1, 8, 19],
                        help="comma-separated request counts (default: 1,8,19)")
    parser.add_argument("--k", type=integer_list, default=[0, 1, 2],
                        help="comma-separated storage slot counts (default: 0,1,2)")
    parser.add_argument("--account-top", type=lambda text: integer_list(text, 0, 4),
                        default=[1, 2, 3, 4], help="account cutoffs (default: 1,2,3,4)")
    parser.add_argument("--storage-top", type=lambda text: integer_list(text, 0, 4),
                        default=[0, 3], help="storage cutoffs for K > 0 (default: 0,3)")
    parser.add_argument("--top-backend", type=backend_list, default=["tree", "hierarchical"],
                        help="top backends (default: tree,hierarchical)")
    parser.add_argument("--accounts", type=bounded_count, default=256)
    parser.add_argument("--storage-entries", type=bounded_count, default=64)
    parser.add_argument("--warmup", type=bounded_count, default=1)
    parser.add_argument("--samples", type=lambda text: bounded_count(text, 1), default=5)
    parser.add_argument("--output", type=Path,
                        help="write a new JSONL file exclusively; existing files are rejected")
    parser.add_argument("--dry-run", action="store_true",
                        help="emit command argument arrays without executing benchmarks")
    return parser


def configurations(options):
    """Keep scalar/batched baselines, omitting equivalent disabled-tier choices."""
    for binary, q, k in itertools.product(options.binary, options.q, options.k):
        common = [str(binary), "--accounts", str(options.accounts),
                  "--storage-entries", str(options.storage_entries),
                  "--q", str(q), "--k", str(k), "--warmup", str(options.warmup),
                  "--samples", str(options.samples)]
        profiles = [("scalar", 0, 0, "tree"), ("batch", 0, 0, "tree")]
        for account, storage, backend in itertools.product(
                options.account_top, options.storage_top if k else [0], options.top_backend):
            if account or storage:
                profiles.append(("batch", account, storage, backend))
        # The two baselines are independent of requested tier/backend sweeps.
        for mode, account, storage, backend in profiles:
            yield common + ["--mode", mode, "--account-top", str(account),
                            "--storage-top", str(storage), "--top-backend", backend]


def validate_binaries(parser, options):
    resolved = []
    for supplied in options.binary:
        try:
            binary = Path(supplied).expanduser().resolve(strict=True)
        except (OSError, RuntimeError) as error:
            parser.error("cannot resolve benchmark binary {}: {}".format(supplied, error))
        if not binary.is_file() or not os.access(binary, os.X_OK):
            parser.error("benchmark binary is not an executable file: {}".format(binary))
        if binary in resolved:
            parser.error("benchmark binaries must be distinct: {}".format(binary))
        resolved.append(binary)
    options.binary = resolved


def validate_workload(parser, options):
    # Public client framing v1 constants from client.hpp/traversal.hpp. Both
    # complete frames and the padded proofs have a default 64 MiB limit.
    limit, proof = 64 * 1024 * 1024, 65 * 536
    for q, k in itertools.product(options.q, options.k):
        if (128 + q * (20 + 32 * k) > limit or
                128 + q * (140 + proof + k * (80 + proof)) > limit or
                q * (1 + k) * proof > limit):
            parser.error("Q={}, K={} exceeds the benchmark's 64 MiB client/proof limits".format(q, k))
        # Every sweep includes an untiered baseline. This rejects a read-only
        # horizon violation upfront; the binary checks the exact initial page
        # loading cost as well, after constructing its public packed image.
        if 65 * q * (1 + k) * (options.warmup + options.samples) >= 1 << 32:
            parser.error("Q={}, K={} exceeds the untiered 2^32 access horizon".format(q, k))


def reject_constant(value):
    raise ValueError("non-finite JSON number: " + value)


def run(options, output):
    for command in configurations(options):
        if options.dry_run:
            row = command
        else:
            # No shell: spaces and metacharacters in executable paths are literal.
            completed = subprocess.run(command, check=True, stdout=subprocess.PIPE,
                                       text=True)
            try:
                row = json.loads(completed.stdout, parse_constant=reject_constant)
                if not isinstance(row, dict):
                    raise ValueError("expected exactly one JSON object")
            except ValueError as error:
                raise ValueError("invalid benchmark output from {}: {}".format(
                    json.dumps(command), error)) from error
        output.write(json.dumps(row, separators=(",", ":"), allow_nan=False) + "\n")
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
        print("benchmark_sweep: command failed (exit {}): {}".format(
            error.returncode, json.dumps(error.cmd)), file=sys.stderr)
        return 1
    except (OSError, ValueError) as error:
        print("benchmark_sweep: " + str(error), file=sys.stderr)
        return 1
    finally:
        if output is not None and options.output:
            output.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
