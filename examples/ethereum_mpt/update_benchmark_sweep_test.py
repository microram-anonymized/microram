#!/usr/bin/env python3
"""Check update sweep comparison, isolation, admission and fail-fast JSONL."""

import contextlib
import io
import itertools
import json
from pathlib import Path
import sys
import tempfile
import unittest

import update_benchmark_sweep as sweep


class UpdateSweepTest(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.binary = self.root / "update benchmark with spaces; literal"
        self.binary.write_text(
            "#!{}\nimport json, os, sys\n"
            "print(json.dumps({{'schema': {!r}, 'pid': os.getpid(), 'args': sys.argv[1:]}}))\n"
            .format(sys.executable, sweep.SCHEMA), encoding="utf-8")
        self.binary.chmod(0o755)

    def args(self, *extra):
        return ["--binary", str(self.binary), *extra]

    def invoke(self, arguments):
        output, errors = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
            status = sweep.main(arguments)
        return status, output.getvalue(), errors.getvalue()

    def test_defaults_and_separate_processes(self):
        status, output, errors = self.invoke(self.args())
        self.assertEqual((status, errors), (0, ""))
        rows = [json.loads(line) for line in output.splitlines()]
        self.assertEqual(len(rows), 2)
        self.assertEqual(len({row["pid"] for row in rows}), len(rows))
        defaults = {"--accounts": "64", "--storage-entries": "8", "--q": "4", "--k": "1",
                    "--blocks": "4", "--read-batches-per-block": "2", "--delta-accounts": "1",
                    "--storage-changes": "1", "--retained-blocks": "2", "--page-headroom": "16",
                    "--compact-after-updates": "0", "--account-top": "3", "--storage-top": "0",
                    "--compact-at-fullness-percent": "0", "--compact-at-dead-bytes-percent": "0",
                    "--top-backend": "tree"}
        for row, mode in zip(rows, ("incremental", "replacement")):
            arguments = dict(zip(row["args"][::2], row["args"][1::2]))
            self.assertEqual(arguments, dict(defaults, **{"--update-mode": mode}))

    def test_full_comparison_matrix_and_multiple_binaries(self):
        second = self.root / "second benchmark"
        second.write_bytes(self.binary.read_bytes())
        second.chmod(0o755)
        status, output, errors = self.invoke(self.args(
            "--binary", str(second), "--q", "1,4", "--k", "0,2",
            "--read-batches-per-block", "0,3", "--delta-accounts", "0,2",
            "--storage-changes", "0,4", "--account-top", "2", "--storage-top", "4",
            "--top-backend", "hierarchical", "--dry-run"))
        self.assertEqual((status, errors), (0, ""))
        commands = [json.loads(line) for line in output.splitlines()]
        expected = set(itertools.product((str(self.binary), str(second)), ("1", "4"),
                                         ("0", "2"), ("0", "3"), ("0", "2"), ("0", "4"),
                                         ("incremental", "replacement")))
        actual = []
        for command in commands:
            args = dict(zip(command[1::2], command[2::2]))
            self.assertEqual((args["--account-top"], args["--storage-top"], args["--top-backend"]),
                             ("2", "4", "hierarchical"))
            actual.append((command[0], *(args[flag] for flag in (
                "--q", "--k", "--read-batches-per-block", "--delta-accounts",
                "--storage-changes", "--update-mode"))))
        self.assertEqual(set(actual), expected)
        self.assertEqual(len(actual), len(expected))

    def test_zero_reads_empty_storage_and_zero_delta(self):
        status, output, errors = self.invoke(self.args(
            "--accounts", "1", "--storage-entries", "0", "--k", "0",
            "--read-batches-per-block", "0", "--delta-accounts", "0", "--storage-changes", "0",
            "--page-headroom", "0", "--retained-blocks", "1", "--update-mode", "replacement"))
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual(len(output.splitlines()), 1)

    def test_public_compaction_percentages_reach_both_update_modes(self):
        status, output, errors = self.invoke(self.args(
            "--compact-at-fullness-percent", "100", "--compact-at-dead-bytes-percent", "1",
            "--dry-run"))
        self.assertEqual((status, errors), (0, ""))
        commands = [json.loads(line) for line in output.splitlines()]
        self.assertEqual(len(commands), 2)
        for command in commands:
            args = dict(zip(command[1::2], command[2::2]))
            self.assertEqual(args["--compact-at-fullness-percent"], "100")
            self.assertEqual(args["--compact-at-dead-bytes-percent"], "1")

    def test_rejects_invalid_configuration_before_output(self):
        invalid = [
            ("--q", "0"), ("--q", "1,1"), ("--q", "1,"), ("--k", "-1"),
            ("--account-top", "5"), ("--storage-top", "-1"),
            ("--top-backend", "other"), ("--update-mode", "scalar"),
            ("--update-mode", "incremental,incremental"), ("--accounts", "0"),
            ("--blocks", "0"), ("--retained-blocks", "0"),
            ("--delta-accounts", "1,65"), ("--read-batches-per-block", "0,0"),
            ("--storage-changes", "1,1"), ("--page-headroom", "-1"),
            ("--compact-after-updates", "-1"), ("--storage-entries", "-1"),
            ("--compact-at-fullness-percent", "101"), ("--compact-at-dead-bytes-percent", "101"),
            ("--compact-at-fullness-percent", "-1"), ("--compact-at-dead-bytes-percent", "1.5"),
            ("--q", "1,2000"), ("--k", "2000"),
            ("--blocks", "1001", "--read-batches-per-block", "1000"),
            ("--binary", str(self.binary)), ("--binary", str(self.root / "missing")),
            ("--binary", str(self.root)),
        ]
        for flag in ("--q", "--k", "--accounts", "--storage-entries", "--blocks",
                     "--read-batches-per-block", "--delta-accounts", "--storage-changes",
                     "--retained-blocks", "--page-headroom", "--compact-after-updates"):
            invalid.append((flag, "1000001"))
        nonexecutable = self.root / "nonexecutable"
        nonexecutable.write_text("not executable", encoding="utf-8")
        invalid.append(("--binary", str(nonexecutable)))
        for extra in invalid:
            with self.subTest(extra=extra):
                output = self.root / "must-not-exist.jsonl"
                with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                    sweep.main(self.args("--output", str(output), *extra))
                self.assertFalse(output.exists())

    def test_read_batch_cap_boundary(self):
        status, output, errors = self.invoke(self.args(
            "--blocks", "1000", "--read-batches-per-block", "1000", "--dry-run"))
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual(len(output.splitlines()), 2)

    def test_rejects_read_or_retained_probe_horizon_before_output(self):
        for extra in (("--q", "33", "--blocks", "1000", "--read-batches-per-block", "1000"),
                      ("--q", "1", "--k", "0", "--blocks", "10000",
                       "--retained-blocks", "10000", "--read-batches-per-block", "0")):
            with self.subTest(extra=extra):
                output = self.root / "must-not-exist.jsonl"
                errors = io.StringIO()
                with contextlib.redirect_stderr(errors), self.assertRaises(SystemExit):
                    sweep.main(self.args("--output", str(output), *extra))
                self.assertIn("conservative 2^32 request horizon", errors.getvalue())
                self.assertFalse(output.exists())

    def test_probe_bound_caps_retention_at_available_roots(self):
        status, output, errors = self.invoke(self.args(
            "--retained-blocks", "1000000", "--read-batches-per-block", "0", "--dry-run"))
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual(len(output.splitlines()), 2)

    def test_does_not_overwrite_output(self):
        output = self.root / "existing.jsonl"
        output.write_text("original\n", encoding="utf-8")
        status, stdout, errors = self.invoke(self.args("--output", str(output)))
        self.assertEqual((status, stdout), (1, ""))
        self.assertIn("File exists", errors)
        self.assertEqual(output.read_text(encoding="utf-8"), "original\n")

    def test_failure_retains_completed_rows_and_stops(self):
        self.binary.write_text(
            "#!{}\nimport json, sys\n"
            "if sys.argv[sys.argv.index('--update-mode') + 1] == 'replacement': sys.exit(7)\n"
            "print(json.dumps({{'schema': {!r}, 'completed': True}}))\n"
            .format(sys.executable, sweep.SCHEMA), encoding="utf-8")
        output = self.root / "partial.jsonl"
        status, stdout, errors = self.invoke(self.args("--q", "1,2", "--output", str(output)))
        self.assertEqual((status, stdout), (1, ""))
        self.assertIn("exit 7", errors)
        self.assertEqual([json.loads(line) for line in output.read_text().splitlines()],
                         [{"schema": sweep.SCHEMA, "completed": True}])

    def test_rejects_invalid_json_or_schema(self):
        prefix = '{"schema":' + json.dumps(sweep.SCHEMA)
        for value in ("[]", "null", '{}\n{}', "{}", '{"schema":"other"}',
                      prefix + ',"value":NaN}', prefix + ',"value":Infinity}',
                      prefix + ',"value":1e309}'):
            with self.subTest(value=value):
                self.binary.write_text("#!{}\nprint({!r})\n".format(sys.executable, value),
                                       encoding="utf-8")
                status, output, errors = self.invoke(self.args())
                self.assertEqual((status, output), (1, ""))
                self.assertIn("invalid benchmark output", errors)


if __name__ == "__main__":
    unittest.main()
