#!/usr/bin/env python3
"""Check sweep isolation, profile selection, fail-fast output and admission."""

import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

import benchmark_sweep as sweep


class SweepTest(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.binary = self.root / "benchmark with spaces"
        self.binary.write_text(
            "#!{}\nimport json, os, sys\n"
            "print(json.dumps({{'pid': os.getpid(), 'args': sys.argv[1:]}}))\n".format(sys.executable),
            encoding="utf-8")
        self.binary.chmod(0o755)

    def args(self, *extra):
        return ["--binary", str(self.binary), "--q", "1", "--k", "0",
                "--account-top", "0,2", "--storage-top", "0,3",
                "--top-backend", "tree,hierarchical", *extra]

    def invoke(self, arguments):
        output, errors = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
            status = sweep.main(arguments)
        return status, output.getvalue(), errors.getvalue()

    def test_profiles_and_separate_processes(self):
        status, output, errors = self.invoke(self.args("--k", "0,2"))
        self.assertEqual((status, errors), (0, ""))
        rows = [json.loads(line) for line in output.splitlines()]
        # K=0: 2 baselines + 2 account-top choices; K=2: 2 + 6 tier choices.
        self.assertEqual(len(rows), 12)
        self.assertEqual(len({row["pid"] for row in rows}), len(rows))
        profiles = []
        for row in rows:
            arguments = dict(zip(row["args"][::2], row["args"][1::2]))
            if arguments["--k"] == "0":
                self.assertEqual(arguments["--storage-top"], "0")
            if arguments["--account-top"] == arguments["--storage-top"] == "0":
                self.assertEqual(arguments["--top-backend"], "tree")
            profiles.append(tuple(sorted(arguments.items())))
        self.assertEqual(len(set(profiles)), len(profiles))

    def test_dry_run_and_multiple_binaries(self):
        second = self.root / "second benchmark"
        second.write_bytes(self.binary.read_bytes())
        second.chmod(0o755)
        status, output, errors = self.invoke(self.args("--binary", str(second), "--dry-run"))
        self.assertEqual((status, errors), (0, ""))
        commands = [json.loads(line) for line in output.splitlines()]
        self.assertEqual(len(commands), 8)
        self.assertEqual({command[0] for command in commands}, {str(self.binary), str(second)})

    def test_rejects_duplicate_or_invalid_configuration_before_output(self):
        for extra in (("--q", "1,1"), ("--k", "-1"), ("--account-top", "5"),
                      ("--samples", "0"), ("--top-backend", "tree,tree"),
                      ("--accounts", "1000001"), ("--storage-entries", "1000001"),
                      ("--warmup", "1000001"), ("--samples", "1000001"),
                      ("--q", "1,2000"), ("--k", "2000"),
                      ("--q", "100", "--samples", "1000000"),
                      ("--binary", str(self.binary)), ("--binary", str(self.root / "missing"))):
            with self.subTest(extra=extra):
                output = self.root / "must-not-exist.jsonl"
                with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                    sweep.main(self.args("--output", str(output), *extra))
                self.assertFalse(output.exists())

    def test_allows_empty_state_and_storage(self):
        status, output, errors = self.invoke(self.args(
            "--accounts", "0", "--storage-entries", "0", "--dry-run"))
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual(len(output.splitlines()), 4)

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
            "if sys.argv[sys.argv.index('--mode') + 1] == 'batch': sys.exit(7)\n"
            "print(json.dumps({{'completed': True}}))\n".format(sys.executable),
            encoding="utf-8")
        output = self.root / "partial.jsonl"
        status, stdout, errors = self.invoke(self.args("--output", str(output)))
        self.assertEqual((status, stdout), (1, ""))
        self.assertIn("exit 7", errors)
        self.assertEqual([json.loads(line) for line in output.read_text().splitlines()],
                         [{"completed": True}])

    def test_rejects_nonobject_or_multiple_json_results(self):
        for value in ("[]", '{}\n{}', '{"value": NaN}'):
            with self.subTest(value=value):
                self.binary.write_text("#!{}\nprint({!r})\n".format(sys.executable, value),
                                       encoding="utf-8")
                status, output, errors = self.invoke(self.args())
                self.assertEqual((status, output), (1, ""))
                self.assertIn("invalid benchmark output", errors)


if __name__ == "__main__":
    unittest.main()
