"""Campaign planning, local evidence, native/tdx/snp runs and synthetic recovery rehearsal."""

import argparse
from collections import Counter
import json
import sys

from .codec import ValidationError, decode, json_schema, load_json
from .planner import expand, write_plan
from .schema import Campaign, SCHEMAS


def main(argv=None):
    parser = argparse.ArgumentParser(description="ORAM campaign preparation, native, tdx and snp runs, and local synthetic rehearsal.")
    commands = parser.add_subparsers(dest="command", required=True)
    plan = commands.add_parser("plan", help="validate and expand a bounded immutable campaign")
    plan.add_argument("--config", required=True)
    plan.add_argument("--output", help="campaign directory; omitted for dry expansion")
    plan.add_argument("--dry-run", action="store_true", help="validate/expand without writing files")
    schema = commands.add_parser("schema", help="print a structural JSON schema")
    schema.add_argument("kind", choices=sorted(SCHEMAS))
    rates = commands.add_parser("rate-grid", help="print a common geometric offered-rate block for matched latency stages")
    rates.add_argument("--minimum", required=True, type=int, help="lowest integer offered rate (ops/s)")
    rates.add_argument("--maximum", required=True, type=int, help="highest integer offered rate (ops/s), included")
    rates.add_argument("--factor", default="2", help="geometric growth factor, default 2; final interval may be shorter")
    validate = commands.add_parser("validate", help="validate structural and cross-field contracts")
    validate.add_argument("kind", choices=sorted(SCHEMAS))
    validate.add_argument("path")
    doctor = commands.add_parser("doctor", help="capture local evidence; never infer protected attestation")
    doctor.add_argument("--execution", choices=("native", "fake", "tdx", "snp"), default="native",
                        help="the runtime label; refused unless the guest kernel shows it (native: no TEE)")
    doctor.add_argument("--worker", required=True)
    doctor.add_argument("--output", required=True)
    doctor.add_argument("--require-physical-cores", type=int, help="require this exact exposed physical-core count")
    doctor.add_argument("--require-cache-domains", type=int, help="require this exact exposed unified-L3 count")
    attest = commands.add_parser("attest", help="as root, once per boot: fetch a tdx/snp report for the campaign")
    attest.add_argument("--campaign", required=True)
    verdict = commands.add_parser("verdict", help="record an offline verifier's result for a capture")
    verdict.add_argument("--campaign", required=True)
    verdict.add_argument("--capture", required=True, help="attestations/<binding>.json, as attest printed it")
    verdict.add_argument("--verifier", required=True, help="tool and version, e.g. 'snpguest 0.9.1 verify'")
    verdict.add_argument("--result", required=True, choices=("verified", "failed"))
    verdict.add_argument("--reference", required=True, help="the verifier's reference, e.g. a token ID")
    verdict.add_argument("--verifier-output", help="the verifier's log, kept beside the capture")
    tune = commands.add_parser("fit-rebuild", help="fit the rebuild cost model to this machine")
    tune.add_argument("--rows", required=True, help="JSON-lines fit rows; with --benchmark, the grid appends here first")
    tune.add_argument("--benchmark", help="the level-arena benchmark to run the grid with (built with --fit-rows)")
    tune.add_argument("--grid", choices=("quick", "target"), default="target")
    tune.add_argument("--owners", type=int, default=3, help="owner threads for the grid's runs")
    tune.add_argument("--no-place", action="store_true", help="do not pin near/far (a guest hiding its L3)")
    tune.add_argument("--output", required=True, help="fit JSON: the override block, the model and the report")
    pilot = commands.add_parser("fit-trial-time", help="fit baseline trial_time models from pilot campaigns")
    pilot.add_argument("--campaign", required=True, action="append", help="a run pilot campaign; repeatable")
    pilot.add_argument("--margin-ppm", type=int, default=250_000,
                       help="added to every fitted time (default 25%%: spread, coverage phase, a slower target)")
    pilot.add_argument("--apply", action="append", default=[],
                       help="a campaign preset whose candidates take the fitted models, in place; repeatable")
    resolve = commands.add_parser("resolve", help="freeze the worker build and resolve every row (needs the worker)")
    resolve.add_argument("--campaign", required=True)
    resolve.add_argument("--worker", required=True, help="built worker; copied into campaign/build")
    resolve.add_argument("--synthetic", action="store_true", help="fake-backend worker for a local rehearsal")
    resolve.add_argument("--synthetic-backend", choices=("fake", "noop"), default="fake",
                         help="with --synthetic: fake stores values; noop stores nothing (caller overhead)")
    prepare = commands.add_parser("prepare-h2o2ram",
                                  help="time H2O2RAM's planner for each h2o2ram row, before resolve freezes its cache")
    prepare.add_argument("--campaign", required=True)
    prepare.add_argument("--worker", required=True, help="the patched build, oram_baseline_h2o2ram")
    prepare.add_argument("--timeout", type=float,
                         help="seconds per row (default: none); a row past it is killed and the others go on")
    prepare.add_argument("--job-timeout", type=float,
                         help="seconds for the whole job (default: none); later rows are not attempted")
    preflight = commands.add_parser("preflight", help="check topology, memory and resolution against saved evidence")
    preflight.add_argument("--campaign", required=True)
    preflight.add_argument("--environment", required=True, help="saved doctor JSON; no host discovery")
    preflight.add_argument("--trial-id", help="with --resolved: check one worker's resolved.json")
    preflight.add_argument("--resolved", help="a worker's saved resolved.json")
    state = commands.add_parser("status", help="verify committed attempts and report durable state")
    state.add_argument("--campaign", required=True)
    for name in ("run", "resume"):
        run = commands.add_parser(name, help="run/resume a campaign: native, tdx, snp or a --synthetic rehearsal")
        run.add_argument("--campaign", required=True)
        run.add_argument("--reducer", required=True)
        run.add_argument("--synthetic", action="store_true",
                         help="the campaign was resolved with --synthetic (fake/no-op backend)")
        run.add_argument("--limit", type=int)
        # Omitted values come from the campaign's launch_policy.json.
        run.add_argument("--retries", type=int, help="worker-side failure retries (default 1)")
        run.add_argument("--preemption-retries", type=int, help="coordinator-stop/orphan retries (default 20)")
        run.add_argument("--min-free-bytes", type=int, help="disk watermark (default 5 GiB; existing campaigns use stored policy)")
        run.add_argument("--update-launch-policy", action="store_true",
                         help="replace stored launch-policy values that differ from these options")
    check = commands.add_parser("verify", help="verify every committed attempt; --deep re-hashes all raw bytes")
    check.add_argument("--campaign", required=True)
    check.add_argument("--deep", action="store_true")
    reduce = commands.add_parser("reduce", help="verify commits and reduce per repetition with the C++ reducer")
    reduce.add_argument("--campaign", required=True)
    reduce.add_argument("--reducer", required=True)
    reduce.add_argument("--output", required=True)
    record = commands.add_parser("validation-record",
                                 help="turn a reduced control/instrumented pair into harness gate records")
    record.add_argument("--control", required=True, help="the reduced summary.json of the lighter (control) arm")
    record.add_argument("--instrumented", required=True, help="the reduced summary.json of the bound arm")
    record.add_argument("--output", required=True)
    record.add_argument("--comparison", choices=("logging_mode", "identical_arms"), default="logging_mode")
    record.add_argument("--harness-ns", type=int, help="closed-loop no-op harness ns/request")
    record.add_argument("--noop", help="a reduced saturated no-op summary.json, by API mode and batch size")
    memory = commands.add_parser("memory-summary", help="reduce a retained memory CSV offline; no host sampling")
    memory.add_argument("--input", required=True)
    memory.add_argument("--interval-ns", type=int, help="declared sampling interval, if known")
    plot = commands.add_parser("plot", help="plot per-repetition campaign summaries offline")
    plot.add_argument("--summary", required=True, action="append",
                      help="a reduced summary.json; repeat to compare campaigns (series stay per campaign and build)")
    plot.add_argument("--output", required=True)
    series = commands.add_parser("timeseries", help="1-second throughput/latency series from one full-event attempt")
    series.add_argument("--reducer", required=True)
    series.add_argument("--output", required=True)
    series.add_argument("--attempt", help="a committed attempt directory")
    series.add_argument("--campaign", help="with --trial-id: the campaign whose complete attempt is used")
    series.add_argument("--trial-id")
    series.add_argument("--environment-class")
    series.add_argument("--interval-ns", type=int, default=1_000_000_000)
    series.add_argument("--no-plot", action="store_true")
    args = parser.parse_args(argv)
    try:
        if args.command == "rate-grid":
            from .codec import plain
            from .rates import geometric_rate_grid
            print(json.dumps(plain(geometric_rate_grid(args.minimum, args.maximum, args.factor)), indent=2))
        elif args.command == "preflight":
            from .admission import preflight as check
            result = check(args.campaign, args.environment, args.trial_id, args.resolved)
            print(json.dumps(result, indent=2))
            return 0 if result["status"] == "compatible" else 2
        elif args.command == "resolve":
            from .resolution import resolve_campaign
            print(json.dumps(resolve_campaign(args.campaign, args.worker, synthetic=args.synthetic,
                                              synthetic_backend=args.synthetic_backend), indent=2))
        elif args.command == "fit-trial-time":
            from .pilots import fit_campaigns
            print(json.dumps(fit_campaigns(args.campaign, args.margin_ppm, args.apply), indent=2))
        elif args.command == "prepare-h2o2ram":
            from .baselines import prepare_h2o2ram
            result = prepare_h2o2ram(args.campaign, args.worker, args.timeout, args.job_timeout)
            print(json.dumps(result, indent=2))
            return 0 if set(result["counts"]) <= {"prepared"} else 2
        elif args.command == "memory-summary":
            from .memory import reduce_memory
            print(json.dumps(reduce_memory(args.input, interval_ns=args.interval_ns), indent=2))
        elif args.command == "validation-record":
            from .validation import write_records
            print(json.dumps(write_records(args.control, args.instrumented, args.output, args.comparison,
                                           args.harness_ns, args.noop), indent=2))
        elif args.command == "reduce":
            from .reduction import reduce_campaign
            print(json.dumps(reduce_campaign(args.campaign, args.reducer, args.output), indent=2))
        elif args.command == "plot":
            from .reduction import plot_summary
            print(json.dumps(plot_summary(args.summary, args.output), indent=2))
        elif args.command == "timeseries":
            from .timeseries import timeseries
            print(json.dumps(timeseries(args.reducer, args.output, attempt=args.attempt, campaign=args.campaign,
                                        trial_id=args.trial_id, environment_class=args.environment_class,
                                        interval_ns=args.interval_ns, plot=not args.no_plot), indent=2))
        elif args.command == "doctor":
            from .doctor import inspect
            from .store import atomic_json
            evidence = inspect(args.worker, args.execution, physical_cores=args.require_physical_cores,
                               cache_domains=args.require_cache_domains)
            atomic_json(args.output, evidence)
            print(json.dumps(evidence, indent=2))
            return 2 if any(reason.startswith(("topology_contract:", "isa:not_exposed:", "runtime:"))
                            for reason in evidence["missing_evidence"]) else 0
        elif args.command == "fit-rebuild":
            from .doctor import file_hash
            from .store import atomic_json
            from .tuner import fit_record, load_rows, run_grid
            if args.benchmark:
                run_grid(args.benchmark, args.grid, args.rows, owners=args.owners, place=not args.no_place)
            record = fit_record(load_rows(args.rows), {"rows_sha256": file_hash(args.rows),
                                                       "grid": args.grid if args.benchmark else None})
            atomic_json(args.output, record)
            print(json.dumps({k: record[k] for k in ("rows", "override", "cost", "fitted")}, indent=2))
        elif args.command == "attest":
            from .attestation import attest_campaign
            print(json.dumps(attest_campaign(args.campaign), indent=2))
        elif args.command == "verdict":
            from .attestation import record_verdict
            print(json.dumps(record_verdict(args.campaign, args.capture, args.verifier, args.result,
                                            args.reference, args.verifier_output), indent=2))
        elif args.command == "status":
            from .campaign import status
            print(json.dumps(status(args.campaign), indent=2))
        elif args.command in ("run", "resume"):
            from .campaign import run_campaign
            print(json.dumps(run_campaign(args.campaign, args.reducer,
                synthetic=args.synthetic, limit=args.limit, retries=args.retries,
                preemption_retries=args.preemption_retries, min_free_bytes=args.min_free_bytes,
                update_launch_policy=args.update_launch_policy), indent=2))
        elif args.command == "verify":
            from .campaign import verify_campaign
            result = verify_campaign(args.campaign, deep=args.deep)
            print(json.dumps(result, indent=2))
            return 0 if not result["failed"] else 2
        elif args.command == "schema":
            print(json.dumps(json_schema(SCHEMAS[args.kind]), indent=2, sort_keys=True))
        elif args.command == "validate":
            document = load_json(args.path)
            decode(SCHEMAS[args.kind], document)
            version = document.get("worker_schema_version", document.get("schema_version", 1))
            print(f"valid {args.kind} schema v{version}")
        else:
            require_output = args.output is not None and args.dry_run
            if require_output:
                raise ValidationError("--dry-run and --output are mutually exclusive")
            result = expand(decode(Campaign, load_json(args.config)))
            if args.output:
                write_plan(result, args.output)
            statuses = Counter(row["planning_status"] for row in result["trials"])
            reasons = Counter(reason for row in result["trials"] for reason in row["skip_reasons"])
            print(json.dumps({"plan_id": result["plan_id"], "status_counts": dict(statuses),
                              "skip_reasons": dict(reasons), "cost": result["cost"],
                              "output": args.output,
                              "note": "Planning only. No library resolution or measurements performed."}, indent=2))
        return 0
    except (ValidationError, OSError, ValueError) as error:
        print(f"oram_bench: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
