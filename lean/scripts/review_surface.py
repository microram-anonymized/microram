#!/usr/bin/env python3
"""Generate a source navigation guide for the explicit Lean review root sets.

Declaration spans are navigation metrics, not standalone specifications or a
compilable subset. The declaration walk excludes theorem proofs and reports
project sources; it does not audit Lean/Mathlib or prove native correspondence.
"""

import argparse
import csv
from dataclasses import dataclass
from datetime import datetime, timezone
import io
from pathlib import Path
import re
import subprocess
import sys


LABELS = ("baseline", "adaptive", "headlines", "native", "all", "complete")
KINDS = {"def", "thm", "axiom", "opaque", "ind", "ctor", "rec", "quot"}


@dataclass(frozen=True)
class Declaration:
    module: str
    kind: str
    name: str
    start: int
    end: int

    @property
    def file(self):
        return self.module.replace(".", "/") + ".lean"


def parse_closure(raw, *, allow_legacy_counts=False):
    """Reject malformed, incomplete or duplicate output instead of dropping it."""
    counts = {}
    declaration_counts = {}
    declarations = {label: {} for label in LABELS}
    for line_number, line in enumerate(raw.splitlines(), 1):
        if not line.strip():
            continue
        fields = line.split("\t")
        try:
            record, label = fields[:2]
            if label not in LABELS:
                raise ValueError("unknown root-set label")
            if record == "COUNT" and (len(fields) == 4 or
                                      (allow_legacy_counts and len(fields) == 3)):
                count = int(fields[2])
                if label in counts or count <= 0:
                    raise ValueError("duplicate or invalid module count")
                counts[label] = count
                if len(fields) == 4:
                    declaration_count = int(fields[3])
                    if declaration_count <= 0:
                        raise ValueError("invalid declaration count")
                    declaration_counts[label] = declaration_count
            elif record == "DECL" and len(fields) == 7:
                _, _, module, kind, name, first, last = fields
                start, end = int(first), int(last)
                if not re.fullmatch(r"RebuildBound(?:\.[A-Za-z0-9_]+)+", module):
                    raise ValueError("invalid project module")
                if kind not in KINDS or not name or any(c.isspace() for c in name):
                    raise ValueError("invalid declaration kind or name")
                if (start, end) != (0, 0) and not (1 <= start <= end):
                    raise ValueError("invalid source range")
                if label not in counts or name in declarations[label]:
                    raise ValueError("declaration precedes count or is duplicated")
                declarations[label][name] = Declaration(module, kind, name, start, end)
            else:
                raise ValueError("unexpected output record")
        except (ValueError, TypeError) as error:
            raise ValueError(f"closure output line {line_number}: {error}: {line!r}") from error
    if set(counts) != set(LABELS):
        raise ValueError("closure output is missing one or more root sets")
    for label in LABELS:
        modules = {d.module for d in declarations[label].values()}
        if len(modules) != counts[label]:
            raise ValueError(f"{label}: module count does not match declaration records")
        if label in declaration_counts and len(declarations[label]) != declaration_counts[label]:
            raise ValueError(f"{label}: declaration count does not match records (truncated output)")
    return {label: list(declarations[label].values()) for label in LABELS}


def merge_ranges(declarations):
    ranges = sorted((d.start, d.end) for d in declarations if d.start)
    merged = []
    for start, end in ranges:
        if merged and start <= merged[-1][1] + 1:
            merged[-1] = (merged[-1][0], max(merged[-1][1], end))
        else:
            merged.append((start, end))
    return merged


def validate_headlines(closures):
    """Keep compatibility restrictions out of the current statement closure.

    Inspect reached declarations, not whole imported modules: shared modules
    may still contain unused compatibility helpers. This is a navigation guard,
    not a proof that every possible key-domain restriction has been excluded.
    """
    legacy_modules = ("KeyUniverse", "KeyRelabel", "KeyRelabelStructure", "KeyIndex")
    legacy_names = ("RebuildBound.Model.LogicalKey.toNat",
                    "RebuildBound.Model.LogicalKey.ofNat",
                    "RebuildBound.Spec.FamilyTape")
    for declaration in closures["headlines"]:
        module, name = declaration.module, declaration.name
        if (any(module == f"RebuildBound.Spec.{part}" or
                module.startswith(f"RebuildBound.Spec.{part}.") for part in legacy_modules)
                or module == "RebuildBound.Numerics"
                or module.startswith(("RebuildBound.Numerics.", "RebuildBound.Proofs.Numerics"))
                or (module.startswith("RebuildBound.Spec.") and
                    any(part.endswith("31") for part in module.split(".")))
                or any(name == prefix or name.startswith(prefix + ".") for prefix in legacy_names)):
            raise ValueError(f"headlines: compatibility or numerical dependency: {name} ({module})")
    # Selecting fewer roots must not accidentally remove their coverage from
    # the complete guide or the comparison union.
    for group in ("headlines", "native"):
        names = {d.name for d in closures[group]}
        for label in ("all", "complete"):
            if not names <= {d.name for d in closures[label]}:
                raise ValueError(f"{label}: missing {group} declarations")


def measure_sources(closures, lean_dir):
    """Every reported module must exist, and every nonzero range must fit it."""
    line_counts = {}
    for declarations in closures.values():
        for declaration in declarations:
            if declaration.file not in line_counts:
                source = lean_dir / declaration.file
                if not source.resolve().is_relative_to(lean_dir):
                    raise ValueError(f"source path escapes the Lean directory: {source}")
                line_counts[declaration.file] = len(source.read_text(encoding="utf-8").splitlines())
            if declaration.end > line_counts[declaration.file]:
                raise ValueError(f"source range exceeds {declaration.file}: {declaration.name}")
    return line_counts


def render_summary(closures, line_counts, head, spec_hash, build_mode):
    lines = [
        "Source declaration closure report", "",
        f"Generated (UTC): {datetime.now(timezone.utc).isoformat()}",
        f"Git HEAD: {head}",
        f"Working Spec tree: {spec_hash}",
        f"Build: {build_mode}", "",
        "Root sets: scripts/review_surface.lean.",
        "headlines: current arbitrary-key API and generic geometry endpoints (headlines.tsv).",
        "baseline/adaptive: historical compatibility endpoints, not the current headline.",
        "native: production matching/routing, conditional error/normalization, and native compatibility endpoints.",
        "all: current headlines plus historical headlines/native; complete: all listed review roots.",
        "Headline guard rejects known legacy key-universe, numeric-key-encoding, finite-family-tape,",
        "geometry31 and numerical-certificate dependencies in the declaration closure.",
        "Walk: constant types, definition/opaque values and inductive machinery; no theorem proofs.",
        "Scope: RebuildBound modules only; Lean and Mathlib are external foundations.",
        "Source spans include attached declaration comments, but exclude imports, file prose",
        "and unrelated declarations. Overlapping spans are merged. These are navigation",
        "metrics, not standalone specifications or a compilable subset. The complete TSV",
        "retains every declaration, including generated auxiliaries with 0/0 source ranges.", "",
    ]
    for label in LABELS:
        declarations = closures[label]
        modules = sorted({d.module for d in declarations})
        span_lines = sum(end - start + 1 for module in modules
                         for start, end in merge_ranges(d for d in declarations if d.module == module))
        whole_lines = sum(line_counts[module.replace(".", "/") + ".lean"] for module in modules)
        missing = sum(d.start == 0 for d in declarations)
        lines += [f"{label}: {len(declarations)} declarations, {len(modules)} modules, "
                  f"{whole_lines} whole-file lines, {span_lines} lines in merged declaration spans; "
                  f"{missing} generated/auxiliary declarations without source ranges.", ""]
        if label not in ("headlines", "complete"):
            continue
        lines.append("Whole-file lines | Span lines | No range | File | Merged source line ranges")
        for module in modules:
            selected = [d for d in declarations if d.module == module]
            ranges = merge_ranges(selected)
            path = module.replace(".", "/") + ".lean"
            count = sum(end - start + 1 for start, end in ranges)
            no_range = sum(d.start == 0 for d in selected)
            locations = ", ".join(str(start) if start == end else f"{start}-{end}"
                                  for start, end in ranges) or "none"
            lines.append(f"{line_counts[path]:4} | {count:4} | {no_range:3} | {path} | {locations}")
        lines.append("")
    return "\n".join(lines)


def render_tsv(declarations):
    output = io.StringIO(newline="")
    writer = csv.writer(output, delimiter="\t", lineterminator="\n")
    writer.writerow(("file", "start_line", "end_line", "kind", "declaration"))
    for d in sorted(declarations, key=lambda d: (d.file, d.start == 0, d.start, d.end, d.name)):
        writer.writerow((d.file, d.start, d.end, d.kind, d.name))
    return output.getvalue()


def capture(command, lean_dir):
    result = subprocess.run(command, cwd=lean_dir, check=True, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return result.stdout.strip()


def identity(lean_dir):
    head = capture(["git", "rev-parse", "HEAD"], lean_dir)
    spec_hash = capture(["bash", "scripts/spec_tree.sh"], lean_dir)
    if not all(re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", value) for value in (head, spec_hash)):
        raise ValueError("invalid git HEAD or Spec tree hash")
    return head, spec_hash


def run_logged(command, lean_dir, output_path):
    print("Running: " + " ".join(command), flush=True)
    with output_path.open("w", encoding="utf-8") as output:
        result = subprocess.run(command, cwd=lean_dir, text=True, stdout=output,
                                stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"command failed ({result.returncode}); see {output_path}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True,
                        help="destination for source-closure.txt, headlines.tsv, declarations.tsv and Closure.out")
    parser.add_argument("--no-build", action="store_true",
                        help="use already-built Lean artifacts; caller must ensure they match sources")
    args = parser.parse_args()
    lean_dir = Path(__file__).resolve().parent.parent
    destination = args.output_dir.resolve()
    try:
        if destination.is_relative_to(lean_dir / "RebuildBound" / "Spec"):
            raise ValueError("output directory must be outside the trusted Spec source tree")
        destination.mkdir(parents=True, exist_ok=True)
        for filename in ("source-closure.txt", "headlines.tsv", "declarations.tsv", "Closure.out", "Build.out"):
            if (destination / filename).is_symlink():
                raise ValueError(f"refusing symlink output: {destination / filename}")
        # A failed regeneration must not leave an old guide appearing current.
        for filename in ("source-closure.txt", "headlines.tsv", "declarations.tsv"):
            (destination / filename).unlink(missing_ok=True)
        head, spec_hash = identity(lean_dir)
        if not args.no_build:
            run_logged(["lake", "build", "RebuildBound"], lean_dir, destination / "Build.out")
        run_logged(["lake", "env", "lean", "scripts/review_surface.lean"], lean_dir,
                   destination / "Closure.out")
        closures = parse_closure((destination / "Closure.out").read_text(encoding="utf-8"))
        validate_headlines(closures)
        line_counts = measure_sources(closures, lean_dir)
        if identity(lean_dir) != (head, spec_hash):
            raise ValueError("git HEAD or Spec sources changed while generating the guide")
        build_mode = ("skipped (--no-build; caller asserts artifacts match sources)" if args.no_build
                      else "lake build RebuildBound succeeded")
        summary = render_summary(closures, line_counts, head, spec_hash, build_mode)
        (destination / "headlines.tsv").write_text(render_tsv(closures["headlines"]), encoding="utf-8")
        (destination / "declarations.tsv").write_text(render_tsv(closures["complete"]), encoding="utf-8")
        (destination / "source-closure.txt").write_text(summary, encoding="utf-8")
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"review_surface: FAIL: {error}", file=sys.stderr)
        return 1
    print(f"Review guide: {destination / 'source-closure.txt'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
