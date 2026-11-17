"""The arena benchmark's harness-overhead gate (analysis/arena_harness_gate.py) against a
fake benchmark: instrumented/control pairs and the gate verdict, with no measurement."""
import io
import json
from pathlib import Path
import stat
import sys
import tempfile
import unittest
from contextlib import redirect_stdout

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from analysis import arena_harness_gate as gate  # noqa: E402

FAKE = """#!/usr/bin/env python3
import json, sys
args = sys.argv[1:]
on = args[args.index("--attribution") + 1] == "1"
scale = float(args[args.index("--scale") + 1]) if on else 1.0
row = {"fit_row": "run", "offered_kops": 500, "backpressure_measured": on, "response_count": 10**6,
       **{f"response_{q}_ns": round(v * scale) for q, v in (("p50", 1000), ("p99", 5000), ("p999", 9000))},
       "response_max_ns": 40000}
print("FIT_ROW " + json.dumps({"fit_row": "level"}))
print("FIT_ROW " + json.dumps(row))
"""


class ArenaGateTest(unittest.TestCase):
    def gate(self, *args):
        with tempfile.TemporaryDirectory() as directory:
            fake = Path(directory) / "bench"
            fake.write_text(FAKE)
            fake.chmod(fake.stat().st_mode | stat.S_IEXEC)
            out = io.StringIO()
            with redirect_stdout(out):
                code = gate.main(["--benchmark", str(fake), "--pairs", "3", *args])
            return code, json.loads(out.getvalue())

    def test_gate(self):
        for scale, status, failures in (("1.0", "passed", []), ("1.04", "passed", []), ("0.8", "passed", []),
                                        ("1.06", "failed", ["p50_over_gate", "p99_over_gate", "p999_over_gate"])):
            with self.subTest(scale=scale):
                code, report = self.gate("--", "--rate", "500", "--scale", scale)
                self.assertEqual((code, report["status"], report["failures"]), (int(bool(failures)), status, failures))
                self.assertEqual([p["order"] for p in report["pairs"]],
                                 ["instrumented_first", "control_first", "instrumented_first"])
        code, report = self.gate("--null", "--", "--rate", "500", "--scale", "1.06")
        self.assertEqual((report["comparison"], report["status"]), ("identical_arms", "passed"))


if __name__ == "__main__":
    unittest.main()
