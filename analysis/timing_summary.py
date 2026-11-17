#!/usr/bin/env python3
"""Paper summaries and identity checks for avx512_constant_time_test results.

Input, per target (one CPU/microcode/build/environment):
  cert    JSON from `avx512_constant_time_test --certify --json`
  null    JSON from `--certify --null-test --json` (the JSON does not record
          which of the two a file is; the role comes from this argument)
  census  optional text output of tests/timing/instruction_census.py
  build   optional build identity (commit / source hash), free text; the
          test's JSON does not carry one, so it is "unavailable" unless given
  env     optional environment identity (free text, e.g. environment class)

    python3 analysis/timing_summary.py \
        --target 'C4 TDX:cert=a/certify.json,null=a/certify-null.json,census=a/census.txt,build=abc123' \
        --csv out.csv --markdown out.md [--latex out.tex]

Outputs: a CSV with one row per (target, variant), Markdown (and optionally a
LaTeX per-target table), and an identity check.  Files of one target must agree
on CPU, microcode, kernel, hypervisor, guest flags, pinned CPU, test
configuration and variant list; a disagreement is an error (exit status 1).
Fields a file does not carry are listed as "unavailable", never filled in.
"""

import argparse
import csv
import json
import math
import re
import statistics
import sys
from pathlib import Path

UNAVAILABLE = "unavailable"

# platform fields that every file of one target must share
PLATFORM_FIELDS = ("vendor", "brand", "family", "model", "stepping", "microcode",
                   "kernel", "hypervisor", "guest_flags", "cpu")
# test configuration that must agree between a certify run and its null run
# (the seed differs by design)
CONFIG_FIELDS = ("mode", "iters", "min_rounds", "max_rounds", "tolerance_cycles_per_op",
                 "alpha", "comparisons", "z")

METHOD = """\
**Method, as `tests/timing/avx512_constant_time_test` implements it** (not Welch's t-test
and not dudect). For every instruction form and secret-operand role the test builds a
set of operand classes: hardcoded special cases, a random reference class, and a
`#null` class drawn independently from the reference's distribution. One sample is the
TSC time of a hand-written asm block that runs the instruction 128 times (latency form,
one dependency chain) or 192 times (throughput form, independent copies), with the
operand held at the class's value. A round times every class once in a fresh random order
(a randomized block design), so drift and interrupts fall on all classes alike; operands
are placed at random pool slots so addresses do not depend on the class.

*Censoring.* After the rounds are collected, one outlier cut is computed for the whole
variant: the pooled median of all classes' samples plus max(0.25 * median, 8 TSC
quanta). A sample above the cut is an outlier.

*Location statistic.* For each non-reference class, the per-round difference
(class minus reference) is averaged over the rounds in which neither sample is an outlier
(`rounds_kept`). The statistic is t = mean / SE, with SE the sample standard error of
those paired differences. It is compared with a two-sided *normal* threshold z, not a
Student-t quantile. A class is flagged if |t| > z.

*Tail statistic.* An exact two-sided binomial test (p = 1/2) of the class's outlier count
against the reference's. A class is flagged if its p-value is below alpha divided by the
number of comparisons.

*Threshold.* The run makes `comparisons` tests (location and tail for every class
except the reference, null class included); each uses alpha / comparisons (Bonferroni, so
the family-wise false-alarm rate is alpha = 1e-3), giving z in the table (about 5.3).

*Difference bound.* bound = |mean difference| + z * SE, converted to core cycles per
instruction (ticks / instructions per sample / ticks per cycle from an ADD ruler). A
class is *certified* if it is not flagged and its bound is at most the tolerance (0.05
cycles/instruction). A variant is certified if every real class and the null class are
certified; it is INVALID if the null class is flagged. Rounds are added (minimum 100,000;
maximum 2,000,000) until every class is certified. Statistic and bound columns below are
the maximum over the variant's real classes (the `#null` class excluded); the null-run
column is the same maximum over the null-test run, in which every class is drawn like the
reference.

*Controls.* `control.one-cycle` (two kernels one chained ADD per loop iteration apart,
a known difference of `iters` cycles per sample) must be detected, measured near that
value, and with z * SE at most 0.5 cycles, so that one cycle per sample is resolved
(diff column: cycles per sample); `control.div64` (64-bit DIV) is expected to be
flagged on cores whose divider is data dependent, and its absence is reported, not a
failure of the run.
"""


def load_json(path):
    with open(path) as f:
        return json.load(f)


def parse_target(spec):
    label, _, rest = spec.partition(":")
    if not rest:
        raise SystemExit(f"--target needs LABEL:cert=...,null=...: {spec!r}")
    fields = {}
    for part in rest.split(","):
        key, _, value = part.partition("=")
        if key not in ("cert", "null", "census", "build", "env") or not value:
            raise SystemExit(f"bad --target field {part!r} in {spec!r}")
        fields[key] = value
    if "cert" not in fields:
        raise SystemExit(f"--target {label!r} needs cert=")
    return label, fields


def present(value):
    """A platform value counts as carried only if it is informative."""
    return value not in (None, "", "0xffffffff")


def shown(value):
    if value in (None, ""):
        return UNAVAILABLE
    if value == "0xffffffff":
        return f"{UNAVAILABLE} (reported 0xffffffff)"
    return str(value)


def parse_census(path):
    text = Path(path).read_text()
    info = {"keys": None, "covered": None, "uncovered": None, "unreviewed": None}
    m = re.search(r"^# (\d+) distinct instruction keys in library code, (\d+) covered", text, re.M)
    if m:
        info["keys"], info["covered"] = int(m.group(1)), int(m.group(2))
    m = re.search(r"^== uncovered \((\d+)\)", text, re.M)
    if m:
        info["uncovered"] = int(m.group(1))
    m = re.search(r"^== masked-mem, UNREVIEWED[^(\n]*\((\d+)\)", text, re.M)
    if m:
        info["unreviewed"] = int(m.group(1))
    m = re.search(r"^== variable \((\d+)\)", text, re.M)
    info["variable"] = int(m.group(1)) if m else None
    return info


def split_name(name):
    """'vpermb.ctrl.lat' -> ('vpermb', 'ctrl', 'lat'); controls have two parts."""
    parts = name.split(".")
    if name.startswith("control."):
        return name.rsplit(".", 1)[0], "", parts[-1]
    return parts[0], parts[1], parts[-1]


def real_classes(variant):
    """Non-reference, non-null classes."""
    return [c for c in variant["classes"][1:] if not c["name"].endswith("#null")]


def null_class(variant):
    return next((c for c in variant["classes"] if c["name"].endswith("#null")), None)


def max_abs_t(classes):
    return max((abs(c["t"]) for c in classes), default=float("nan"))


def parse_skipped(entries):
    out = []
    for s in entries:
        m = re.match(r"(\S+) \(no (.+)\)$", s)
        out.append((m.group(1), m.group(2)) if m else (s, "unspecified"))
    return out


def check_identity(label, files):
    """files: {role: (path, json)}. Returns (errors, rows).

    rows: (field, value-per-role dict) for the identity table."""
    errors, rows = [], []
    roles = list(files)
    for field in PLATFORM_FIELDS:
        values = {r: files[r][1].get("platform", {}).get(field) for r in roles}
        rows.append((f"platform.{field}", {r: shown(v) if field == "microcode" else (UNAVAILABLE if v is None else str(v))
                                           for r, v in values.items()}))
        distinct = {json.dumps(v) for v in values.values()}
        if len(distinct) > 1:
            errors.append(f"{label}: platform.{field} differs between files: "
                          + ", ".join(f"{r}={values[r]!r}" for r in roles))
    for field in CONFIG_FIELDS:
        values = {r: files[r][1].get("config", {}).get(field) for r in roles}
        rows.append((f"config.{field}", {r: UNAVAILABLE if v is None else str(v) for r, v in values.items()}))
        if len({json.dumps(v) for v in values.values()}) > 1:
            errors.append(f"{label}: config.{field} differs between files: "
                          + ", ".join(f"{r}={values[r]!r}" for r in roles))
    names = {r: [v["name"] for v in files[r][1]["variants"]] for r in roles}
    if len({tuple(n) for n in names.values()}) > 1:
        errors.append(f"{label}: variant lists differ between files")
    skipped = {r: files[r][1].get("skipped", []) for r in roles}
    if len({tuple(s) for s in skipped.values()}) > 1:
        errors.append(f"{label}: skipped lists differ between files")
    if len(roles) > 1 and len({files[r][1]["config"].get("seed") for r in roles}) < len(roles):
        errors.append(f"{label}: cert and null runs have the same seed (same file twice?)")
    return errors, rows


def summarize_target(label, fields):
    cert_path = fields["cert"]
    files = {"cert": (cert_path, load_json(cert_path))}
    if "null" in fields:
        files["null"] = (fields["null"], load_json(fields["null"]))
    errors, ident_rows = check_identity(label, files)
    cert = files["cert"][1]
    null = files["null"][1] if "null" in files else None
    nullby = {v["name"]: v for v in null["variants"]} if null else {}
    plat, cfg, clk = cert["platform"], cert["config"], cert["clock"]

    missing = []
    for field in ("microcode",):
        if not present(plat.get(field)):
            missing.append(f"platform.{field} ({shown(plat.get(field))})")
    missing.append("build identity (not in the JSON)" if "build" not in fields else None)
    missing.append("environment identity (not in the JSON)" if "env" not in fields else None)
    missing.append("test binary compiler/flags/source hash (not in the JSON)")
    if null is None:
        missing.append("null-test JSON (not given)")
    else:
        missing.append("the null JSON does not record that it is a null run (config.mode is 'certify' in both)")
    if "census" not in fields:
        missing.append("census output (not given)")
    missing = [m for m in missing if m]

    identity = {
        "target": label,
        "vendor": shown(plat.get("vendor")), "brand": shown(plat.get("brand")),
        "family": plat.get("family"), "model": plat.get("model"), "stepping": plat.get("stepping"),
        "microcode": shown(plat.get("microcode")), "kernel": shown(plat.get("kernel")),
        "hypervisor": shown(plat.get("hypervisor")), "guest_flags": shown(plat.get("guest_flags")),
        "pinned_cpu": plat.get("cpu"), "build": fields.get("build", UNAVAILABLE),
        "environment": fields.get("env", UNAVAILABLE),
        "tsc_ghz": clk.get("tsc_ghz"), "tsc_quantum_ticks": clk.get("tsc_quantum"),
        "cert_file": cert_path, "null_file": fields.get("null", UNAVAILABLE),
        "census_file": fields.get("census", UNAVAILABLE),
    }

    rows = []
    for v in cert["variants"]:
        key, role, form = split_name(v["name"])
        is_control = v["name"].startswith("control.")
        real = real_classes(v)
        nv = nullby.get(v["name"])
        worst_t = max(real, key=lambda c: abs(c["t"])) if real else None
        worst_b = max(real, key=lambda c: c["bound_cycles_per_op"]) if real else None
        nulls = [c for c in nv["classes"][1:]] if nv else []
        nullc = null_class(v)
        rows.append({
            **{k: identity[k] for k in ("target", "vendor", "brand", "family", "model", "stepping",
                                        "microcode", "kernel", "hypervisor", "guest_flags", "pinned_cpu",
                                        "build", "environment")},
            "variant": v["name"], "instruction": key, "role": role, "form": form,
            "kind": "control" if is_control else "instruction",
            "support": "supported",
            "classes": len(real), "ops_per_sample": v["ops_per_sample"],
            "rounds": v["rounds"],
            "rounds_kept_min": min((c["rounds_kept"] for c in real), default=""),
            "executions_per_class": v["rounds"] * v["ops_per_sample"],
            "statistic_t_max_abs": worst_t and abs(worst_t["t"]),
            "threshold_z": cfg["z"],
            "bound_cycles_per_instruction": worst_b and worst_b["bound_cycles_per_op"],
            "tolerance_cycles_per_instruction": cfg["tolerance_cycles_per_op"],
            "worst_class_by_bound": worst_b and worst_b["name"],
            "min_tail_p": min((c["tail_p"] for c in real), default=""),
            "null_class_t": nullc["t"] if nullc else "",
            "null_run_t_max_abs": max_abs_t(nulls) if nv else UNAVAILABLE,
            "null_run_bound_cycles_per_instruction": max((c["bound_cycles_per_op"] for c in nulls), default="") if nv else UNAVAILABLE,
            "null_run_status": nv["status"] if nv else UNAVAILABLE,
            "verdict": v["status"],
        })
    for name, feature in parse_skipped(cert.get("skipped", [])):
        key, role, form = split_name(name)
        rows.append({
            **{k: identity[k] for k in ("target", "vendor", "brand", "family", "model", "stepping",
                                        "microcode", "kernel", "hypervisor", "guest_flags", "pinned_cpu",
                                        "build", "environment")},
            "variant": name, "instruction": key, "role": role, "form": form,
            "kind": "instruction", "support": f"unsupported (no {feature})",
            "verdict": "unsupported",
        })

    # family-wide statistics as the test prints them (constant kind, null class included)
    ts = [c["t"] for v in cert["variants"] if not v["name"].startswith("control.") for c in v["classes"][1:]]
    nts = ([c["t"] for v in null["variants"] if not v["name"].startswith("control.") for c in v["classes"][1:]]
           if null else [])
    bounds = [(c["bound_cycles_per_op"], v["name"], c["name"])
              for v in cert["variants"] if not v["name"].startswith("control.") for c in v["classes"][1:]]

    def spread(x):
        return (len(x), statistics.fmean(x), statistics.stdev(x), max(abs(a) for a in x)) if len(x) > 1 else None

    stats = {"cert_t": spread(ts), "null_t": spread(nts) if nts else None,
             "max_bound": max(bounds) if bounds else None,
             "null_max_bound": max((c["bound_cycles_per_op"], v["name"], c["name"])
                                   for v in null["variants"] if not v["name"].startswith("control.")
                                   for c in v["classes"][1:]) if null else None}
    controls = []
    for v in cert["variants"]:
        if not v["name"].startswith("control."):
            continue
        c = v["classes"][1]
        controls.append({"control": v["name"], "status": v["status"],
                         "null_run_status": nullby[v["name"]]["status"] if v["name"] in nullby else UNAVAILABLE,
                         "t": c["t"], "diff_cycles_per_sample": c["diff_cycles_per_sample"],
                         "rounds_kept": c["rounds_kept"]})
    census = parse_census(fields["census"]) if "census" in fields else None
    if census:
        for k, label_ in (("uncovered", "uncovered count"), ("unreviewed", "unreviewed masked-mem count")):
            if census[k] is None:
                missing.append(f"census {label_} (section not in the census output)")
    return {"label": label, "identity": identity, "rows": rows, "errors": errors, "ident_rows": ident_rows,
            "missing": missing, "stats": stats, "controls": controls, "census": census,
            "verdict": {"cert": cert["verdict"], "null": null["verdict"] if null else UNAVAILABLE},
            "z": cfg["z"], "comparisons": cfg["comparisons"], "config": cfg}


CSV_COLUMNS = [
    "target", "variant", "instruction", "role", "form", "kind", "support", "verdict",
    "rounds", "rounds_kept_min", "ops_per_sample", "executions_per_class", "classes",
    "statistic_t_max_abs", "threshold_z", "bound_cycles_per_instruction",
    "tolerance_cycles_per_instruction", "worst_class_by_bound", "min_tail_p",
    "null_class_t", "null_run_t_max_abs", "null_run_bound_cycles_per_instruction", "null_run_status",
    "vendor", "brand", "family", "model", "stepping", "microcode", "kernel", "hypervisor",
    "guest_flags", "pinned_cpu", "build", "environment",
]


def fmt(x, digits=3):
    if x is None or x == "":
        return "-"
    if isinstance(x, float):
        return f"{x:.{digits}g}"
    return str(x)


def md_table(header, body):
    out = ["| " + " | ".join(header) + " |", "|" + "|".join("---" for _ in header) + "|"]
    out += ["| " + " | ".join(str(c) for c in r) + " |" for r in body]
    return "\n".join(out)


def per_instruction(rows):
    """Aggregate variant rows by instruction key (roles and forms together)."""
    agg = {}
    for r in rows:
        if r["kind"] == "control":
            continue
        a = agg.setdefault(r["instruction"], {"variants": 0, "unsupported": 0, "rounds": [], "t": [], "nt": [],
                                              "b": [], "verdicts": set()})
        a["variants"] += 1
        a["verdicts"].add(r["verdict"])
        if r["support"] != "supported":
            a["unsupported"] += 1
            continue
        a["rounds"].append(r["rounds"])
        a["t"].append(r["statistic_t_max_abs"])
        a["b"].append(r["bound_cycles_per_instruction"])
        if isinstance(r["null_run_t_max_abs"], float):
            a["nt"].append(r["null_run_t_max_abs"])
    return agg


def markdown(results, errors):
    out = ["# Constant-time instruction timing: per-form summary", "", METHOD, ""]
    out += ["## Targets and verdicts", ""]
    head = ["target", "CPU (family/model/step)", "microcode", "pinned CPU", "kernel", "hypervisor / guest flags",
            "build", "variants (cert / unsupported)", "z (unitless)", "comparisons", "max bound (cyc/instr)",
            "t sd / max |t| (cert)", "t sd / max |t| (null)", "verdict (cert / null)"]
    body = []
    for t in results:
        i, s = t["identity"], t["stats"]
        sup = [r for r in t["rows"] if r["kind"] == "instruction" and r["support"] == "supported"]
        cert = sum(1 for r in sup if r["verdict"] == "certified")
        uns = sum(1 for r in t["rows"] if r["support"] != "supported")
        ct, nt = s["cert_t"], s["null_t"]
        body.append([i["target"], f"{i['brand']} ({i['family']}/{i['model']}/{i['stepping']})", i["microcode"],
                     i["pinned_cpu"], i["kernel"], f"{i['hypervisor']} / {i['guest_flags']}", i["build"],
                     f"{cert}/{len(sup)} / {uns}", fmt(t["z"], 4), t["comparisons"],
                     f"{s['max_bound'][0]:.4f} ({s['max_bound'][1]} / {s['max_bound'][2]})" if s["max_bound"] else "-",
                     f"{ct[2]:.2f} / {ct[3]:.2f}" if ct else "-", f"{nt[2]:.2f} / {nt[3]:.2f}" if nt else "-",
                     f"{t['verdict']['cert']} / {t['verdict']['null']}"])
    out += [md_table(head, body), "", "## Controls, census and unsupported forms", ""]
    for t in results:
        out += [f"### {t['label']}", ""]
        out += [md_table(["control", "certify status", "null-run status", "t", "diff (cycles/sample)", "rounds kept"],
                         [[c["control"], c["status"], c["null_run_status"], fmt(c["t"], 4),
                           fmt(c["diff_cycles_per_sample"], 4), c["rounds_kept"]] for c in t["controls"]]), ""]
        c = t["census"]
        if c:
            out += [f"Census: {c['keys']} instruction keys in library code, {c['covered']} covered by the timing "
                    f"test; uncovered {fmt(c['uncovered'])}, unreviewed masked-memory operations "
                    f"{fmt(c['unreviewed']) if c['unreviewed'] is not None else UNAVAILABLE}; "
                    f"variable-latency forms {fmt(c['variable'])} (public operands only).", ""]
        else:
            out += [f"Census: {UNAVAILABLE} (no census file given).", ""]
        uns = [r for r in t["rows"] if r["support"] != "supported"]
        if uns:
            out += ["Unsupported (not run, so not certified): "
                    + "; ".join(f"`{r['variant']}`: {r['support']}" for r in uns) + ".", ""]
        else:
            out += ["Unsupported forms: none.", ""]
        out += ["Fields unavailable in the retained evidence: " + "; ".join(t["missing"]) + ".", ""]
    out += ["## Identity check", ""]
    if errors:
        out += ["**ERRORS**", ""] + [f"- {e}" for e in errors] + [""]
    else:
        out += ["All files within each target agree on every platform and configuration field listed below.", ""]
    for t in results:
        roles = list(t["ident_rows"][0][1]) if t["ident_rows"] else []
        out += [f"### {t['label']}", "", md_table(["field"] + roles, [[f] + [v[r] for r in roles] for f, v in t["ident_rows"]]), ""]
    out += ["## Per-instruction table", "",
            "Maximum over roles, forms (latency and throughput) and classes. `max |t|` and `max bound` are from "
            "the certification run; `null max |t|` from the null-test run. t is unitless, bound is in core "
            "cycles per instruction, `min rounds` is the smallest sample count per class (one sample = "
            "128 or 192 instructions).", ""]
    for t in results:
        out += [f"### {t['label']}", ""]
        body = []
        for key, a in sorted(per_instruction(t["rows"]).items()):
            if a["rounds"]:
                v = "certified" if a["verdicts"] <= {"certified", "unsupported"} else "/".join(sorted(a["verdicts"]))
                if a["unsupported"]:
                    v += f" ({a['unsupported']} of {a['variants']} variants unsupported)"
                body.append([key, a["variants"], min(a["rounds"]), fmt(max(a["t"]), 3), fmt(max(a["nt"], default=None), 3),
                             fmt(max(a["b"]), 3), v])
            else:
                body.append([key, a["variants"], "-", "-", "-", "-", "unsupported"])
        out += [md_table(["instruction", "variants", "min rounds", "max |t|", "null max |t|", "max bound", "verdict"], body), ""]
    return "\n".join(out)


def latex(results):
    esc = lambda s: str(s).replace("_", r"\_").replace("#", r"\#").replace("&", r"\&")
    out = []
    for t in results:
        out += [f"% {t['label']}", r"\begin{tabular}{lrrrrrl}", r"\hline",
                r"instruction & variants & min rounds & max $|t|$ & null max $|t|$ & max bound & verdict \\", r"\hline"]
        for key, a in sorted(per_instruction(t["rows"]).items()):
            if a["rounds"]:
                v = "certified" if a["verdicts"] <= {"certified", "unsupported"} else "/".join(sorted(a["verdicts"]))
                if a["unsupported"]:
                    v += f" ({a['unsupported']}/{a['variants']} unsupp.)"
                out.append(" & ".join([esc(key), str(a["variants"]), str(min(a["rounds"])), fmt(max(a["t"]), 3),
                                       fmt(max(a["nt"], default=None), 3), fmt(max(a["b"]), 3), esc(v)]) + r" \\")
            else:
                out.append(" & ".join([esc(key), str(a["variants"]), "-", "-", "-", "-", "unsupported"]) + r" \\")
        out += [r"\hline", r"\end{tabular}", ""]
    return "\n".join(out)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--target", action="append", required=True, metavar="LABEL:cert=P,null=P[,census=P,build=ID,env=ID]")
    ap.add_argument("--csv")
    ap.add_argument("--markdown")
    ap.add_argument("--latex")
    args = ap.parse_args(argv)
    results = [summarize_target(*parse_target(s)) for s in args.target]
    errors = [e for t in results for e in t["errors"]]
    if args.csv:
        with open(args.csv, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=CSV_COLUMNS, extrasaction="ignore", restval="")
            w.writeheader()
            for t in results:
                w.writerows(t["rows"])
    text = markdown(results, errors)
    if args.markdown:
        Path(args.markdown).write_text(text + "\n")
    if args.latex:
        Path(args.latex).write_text(latex(results))
    if not (args.markdown or args.csv or args.latex):
        print(text)
    for e in errors:
        print("IDENTITY ERROR:", e, file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
