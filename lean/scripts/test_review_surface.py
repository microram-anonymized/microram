#!/usr/bin/env python3
"""Regress closure parsing and the arbitrary-key headline boundary.

Run from lean/: python3 scripts/test_review_surface.py
Synthetic closure records keep these checks independent of a Lake build.
"""

import csv
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import review_surface as review


MODEL = "RebuildBound.Spec.Model.Key"
KEY = "RebuildBound.Model.LogicalKey"


def declaration(module=MODEL, name=KEY, start=2, end=4):
    return review.Declaration(module, "def", name, start, end)


def closures(*headlines):
    result = {label: [declaration()] for label in review.LABELS}
    result["headlines"] = list(headlines) or [declaration()]
    for label in ("all", "complete"):
        result[label] = list(result["headlines"])
    return result


def records():
    return "\n".join(
        f"COUNT\t{label}\t1\t1\n"
        f"DECL\t{label}\t{MODEL}\tdef\t{KEY}\t2\t4"
        for label in review.LABELS
    )


class ClosureParsingTest(unittest.TestCase):
    def test_complete_counts_and_generated_ranges(self):
        parsed = review.parse_closure(records())
        self.assertEqual(tuple(parsed), review.LABELS)
        self.assertEqual(parsed["headlines"], [declaration()])
        generated = records().replace(f"{KEY}\t2\t4", f"{KEY}\t0\t0")
        self.assertTrue(all(d.start == d.end == 0
                            for ds in review.parse_closure(generated).values()
                            for d in ds))

    def test_missing_or_truncated_output_is_rejected(self):
        raw = records()
        malformed = (
            raw.rsplit("\n", 1)[0],
            "\n".join(raw.splitlines()[:-2]),
            raw.replace("COUNT\theadlines\t1\t1", "COUNT\theadlines\t1\t2"),
            raw.replace("COUNT\theadlines\t1\t1", "COUNT\theadlines\t2\t1"),
        )
        for output in malformed:
            with self.subTest(output=output), self.assertRaises(ValueError):
                review.parse_closure(output)

    def test_malformed_records_are_rejected(self):
        raw = records()
        malformed = (
            raw.replace("COUNT\theadlines\t1\t1", "COUNT\theadlines\t0\t1"),
            raw.replace("COUNT\theadlines\t1\t1", "COUNT\theadlines\t1\tbad"),
            raw.replace("headlines", "unknown"),
            raw.replace("\tdef\t", "\tbogus\t", 1),
            raw.replace(f"{KEY}\t2\t4", f"{KEY}\t4\t2", 1),
            raw.replace(MODEL, "../escape", 1),
            raw + "\n" + raw.splitlines()[0],
            raw + "\n" + raw.splitlines()[1],
            raw.splitlines()[1] + "\n" + raw,
        )
        for output in malformed:
            with self.subTest(output=output), self.assertRaises(ValueError):
                review.parse_closure(output)

    def test_legacy_counts_require_explicit_opt_in(self):
        raw = "\n".join(line.rsplit("\t", 1)[0] if line.startswith("COUNT\t")
                        else line for line in records().splitlines())
        with self.assertRaises(ValueError):
            review.parse_closure(raw)
        self.assertEqual(review.parse_closure(raw, allow_legacy_counts=True),
                         review.parse_closure(records()))


class HeadlineBoundaryTest(unittest.TestCase):
    def test_logical_keys_and_canonical_tape_are_allowed(self):
        review.validate_headlines(closures(
            declaration(),
            declaration("RebuildBound.Spec.IdealKeyLaw",
                        "RebuildBound.Spec.IdealKey.Tape"),
            declaration("RebuildBound.Spec.IdealGeometry",
                        "RebuildBound.Spec.IdealGeometryCapacity_statement"),
        ))

    def test_legacy_modules_and_submodules_are_rejected(self):
        modules = (
            "RebuildBound.Spec.KeyUniverse",
            "RebuildBound.Spec.KeyRelabel",
            "RebuildBound.Spec.KeyRelabelStructure",
            "RebuildBound.Spec.KeyIndex",
            "RebuildBound.Numerics",
            "RebuildBound.Proofs.Numerics",
            "RebuildBound.Proofs.NumericsTopPreparation",
            "RebuildBound.Spec.HierarchyChunk31",
            "RebuildBound.Spec.Adaptive31",
        )
        for module in modules:
            for suffix in ("", ".Helper"):
                with self.subTest(module=module + suffix), self.assertRaises(ValueError):
                    review.validate_headlines(closures(declaration(module + suffix)))

    def test_legacy_names_are_rejected_in_other_modules(self):
        # Actual old names: module-only checks miss encodings in Model.Key and
        # the finite tape abbreviation in the shared HierarchyBase module.
        names = (
            "RebuildBound.Model.LogicalKey.toNat",
            "RebuildBound.Model.LogicalKey.ofNat",
            "RebuildBound.Spec.FamilyTape",
        )
        for name in names:
            for suffix in ("", ".match_1"):
                with self.subTest(name=name + suffix), self.assertRaises(ValueError):
                    review.validate_headlines(closures(declaration(name=name + suffix)))

    def test_historical_sets_may_retain_legacy_dependencies(self):
        old = declaration("RebuildBound.Spec.KeyUniverse",
                          "RebuildBound.Spec.FamilyTape")
        fixture = {label: [old] for label in review.LABELS}
        fixture["headlines"] = [declaration()]
        for label in ("all", "complete"):
            fixture[label].append(declaration())
        review.validate_headlines(fixture)

    def test_comparison_and_complete_sets_must_include_headlines(self):
        for label in ("all", "complete"):
            fixture = closures()
            fixture[label] = []
            with self.subTest(label=label), self.assertRaises(ValueError):
                review.validate_headlines(fixture)

    def test_native_roots_must_remain_in_comparison_and_complete_sets(self):
        native = declaration("RebuildBound.Spec.NativeNormalize",
                             "RebuildBound.Spec.NativeNormalizeBound_statement")
        fixture = closures()
        fixture["native"].append(native)
        fixture["all"].append(native)
        fixture["complete"].append(native)
        review.validate_headlines(fixture)
        for label in ("all", "complete"):
            incomplete = {group: list(items) for group, items in fixture.items()}
            incomplete[label].remove(native)
            with self.subTest(label=label), self.assertRaises(ValueError):
                review.validate_headlines(incomplete)


class RenderingTest(unittest.TestCase):
    def test_headline_table_preserves_merged_spans_and_generated_declarations(self):
        fixture = closures(declaration(start=2, end=4),
                           declaration(name=KEY + ".helper", start=4, end=6),
                           declaration(name=KEY + ".generated", start=0, end=0))
        report = review.render_summary(fixture, {declaration().file: 10},
                                       "head", "spec", "synthetic")
        headline = report[report.index("headlines: 3 declarations"):].split("\nnative:", 1)[0]
        self.assertIn("3 declarations, 1 modules, 10 whole-file lines, 5 lines", headline)
        self.assertIn("1 generated/auxiliary declarations", headline)
        self.assertIn("Whole-file lines | Span lines | No range | File", headline)
        self.assertIn(declaration().file + " | 2-6", headline)

    def test_tsv_keeps_zero_ranges_and_orders_by_source(self):
        supplied = [declaration(name=KEY + ".generated", start=0, end=0),
                    declaration(start=2, end=4)]
        rows = list(csv.DictReader(io.StringIO(review.render_tsv(supplied)), delimiter="\t"))
        self.assertEqual([row["declaration"] for row in rows],
                         [KEY, KEY + ".generated"])
        self.assertEqual(rows[1]["start_line"], "0")
        self.assertEqual(rows[1]["end_line"], "0")
        self.assertEqual(rows[0]["file"], declaration().file)

    def test_generator_exports_current_and_complete_guides(self):
        fixture = closures()
        old = declaration("RebuildBound.Spec.KeyUniverse", "RebuildBound.Spec.Legacy")
        fixture["complete"].append(old)
        raw = []
        for label, selected in fixture.items():
            raw.append(f"COUNT\t{label}\t{len({d.module for d in selected})}\t{len(selected)}")
            raw.extend(f"DECL\t{label}\t{d.module}\t{d.kind}\t{d.name}\t{d.start}\t{d.end}"
                       for d in selected)

        def emit_closure(command, lean_dir, output_path):
            output_path.write_text("\n".join(raw), encoding="utf-8")

        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory)
            with patch.object(review.sys, "argv", ["review_surface.py", "--no-build",
                                                   "--output-dir", directory]), \
                    patch.object(review, "identity", return_value=("head", "spec")), \
                    patch.object(review, "run_logged", side_effect=emit_closure), \
                    patch.object(review, "measure_sources", return_value={
                        declaration().file: 10, old.file: 10}), \
                    patch.object(review.sys, "stdout", new=io.StringIO()):
                self.assertEqual(review.main(), 0)
            headline = (destination / "headlines.tsv").read_text(encoding="utf-8")
            complete = (destination / "declarations.tsv").read_text(encoding="utf-8")
            self.assertIn(KEY, headline)
            self.assertNotIn(old.name, headline)
            self.assertIn(old.name, complete)
            self.assertTrue((destination / "source-closure.txt").is_file())


if __name__ == "__main__":
    unittest.main()
