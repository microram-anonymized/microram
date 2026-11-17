"""`doctor` host evidence (analysis/oram_bench/doctor.py): the worker's shared-library
dependency closure and the TSC cross-check, from fixtures."""
import json
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from unittest.mock import patch

from analysis.oram_bench.codec import decode
from analysis.oram_bench.doctor import (CLOCK_READ_NS, clock_check_missing, dependency_closure, inspect,
                                        parse_ldd)
from analysis.oram_bench.schema import ClockCheck, Environment

# What the development host's worker printed (trimmed to two CPUs).
HEALTHY = {
    "schema": "clock-check-v1", "tsc_hz": 3799914677.2, "window_ms": 200,
    "window_hz": [3799914665.2, 3799914656.7, 3799914663.0, 3799914653.5, 3799914747.4],
    "rate_spread_ppm": 0.025, "monotonic_slew_ppm": 12.346, "read_ns": 17.88,
    "cpu_offsets_ns": [{"cpu": 1, "low_ns": -55.0, "high_ns": 45.0}],
    "reference_cpu": 0, "max_cpu_offset_ns": 55.0, "proven_skews": 0, "backwards_on_migration": 0,
    "unplaced_cpus": 0,
    "ntp": {"state": "ok", "synchronized": True, "frequency_ppm": 8.247, "max_error_us": 7,
            "estimated_error_us": 0},
}

LDD = """\tlinux-vdso.so.1 (0x00007ffd1a3f2000)
\tlibstdc++.so.6 => /lib/x86_64-linux-gnu/libstdc++.so.6 (0x00007f2c3c200000)
\tlibmissing.so.1 => not found
\t/lib64/ld-linux-x86-64.so.2 (0x00007f2c3c6a1000)
"""


class DependencyClosureTests(unittest.TestCase):
    def test_ldd_lines_name_objects_and_their_files(self):
        self.assertEqual(parse_ldd(LDD), [
            ("linux-vdso.so.1", None),
            ("libstdc++.so.6", "/lib/x86_64-linux-gnu/libstdc++.so.6"),
            ("libmissing.so.1", None),
            ("ld-linux-x86-64.so.2", "/lib64/ld-linux-x86-64.so.2"),
        ])
        self.assertEqual(parse_ldd("\tstatically linked\n"), [])

    def test_closure_hashes_what_the_loader_resolves(self):
        with tempfile.TemporaryDirectory() as directory:
            library = Path(directory) / "libx.so.1"
            library.write_bytes(b"library bytes")
            output = f"\tlinux-vdso.so.1 (0x1)\n\tlibx.so.1 => {library} (0x2)\n\tliby.so => not found\n"
            done = type("Done", (), {"returncode": 0, "stdout": output, "stderr": ""})
            with patch("analysis.oram_bench.doctor.subprocess.run", return_value=done):
                closure = dependency_closure(library)
        self.assertEqual([o.name for o in closure], ["libx.so.1", "liby.so"])  # no vDSO
        self.assertEqual(len(closure[0].sha256), 64)
        self.assertIsNone(closure[1].sha256)


class ClockCheckTests(unittest.TestCase):
    def test_the_worker_output_decodes_and_passes(self):
        check = decode(ClockCheck, json.loads(json.dumps(HEALTHY)))
        self.assertEqual(clock_check_missing(check), [])
        self.assertEqual(check.ntp.state, "ok")

    def test_each_failure_is_named(self):
        check = decode(ClockCheck, HEALTHY)
        cases = {
            "clock:tsc_rate_unstable": replace(check, rate_spread_ppm=25.0),
            "clock:monotonic_slewed": replace(check, monotonic_slew_ppm=-800.0),
            "clock:slow_clock_read": replace(check, read_ns=CLOCK_READ_NS * 10),
            "clock:tsc_skew_across_cpus": replace(check, proven_skews=1),
            "clock:tsc_backwards_on_migration": replace(check, backwards_on_migration=2),
            "clock:skew_unmeasured_on_some_cpus": replace(check, unplaced_cpus=1),
        }
        for reason, failing in cases.items():
            self.assertEqual(clock_check_missing(failing), [reason])
        self.assertEqual(clock_check_missing(None), ["clock:cross_validation_unavailable"])

    def test_only_a_clean_invariant_tsc_is_validated(self):
        memory = {"guest_total_bytes": 1024, "ancestors": [], "missing_evidence": []}
        flags = "flags\t: constant_tsc nonstop_tsc tsc_known_freq avx512f"
        texts = {"/proc/cpuinfo": flags, "/sys/devices/system/clocksource/clocksource0/current_clocksource": "tsc"}
        healthy = decode(ClockCheck, HEALTHY)
        with tempfile.TemporaryDirectory() as directory:
            worker = Path(directory) / "worker"
            worker.write_bytes(b"synthetic binary identity")
            def observe(check, clocksource="tsc"):
                values = dict(texts)
                values["/sys/devices/system/clocksource/clocksource0/current_clocksource"] = clocksource
                with patch("analysis.oram_bench.doctor._text", side_effect=lambda path: values.get(str(path))), \
                     patch("analysis.oram_bench.doctor.memory_evidence", return_value=memory), \
                     patch("analysis.oram_bench.doctor.source_identity", return_value="synthetic-source"), \
                     patch("analysis.oram_bench.doctor.compiled_isa", return_value=["avx512f"]), \
                     patch("analysis.oram_bench.doctor.clock_check", return_value=check), \
                     patch("analysis.oram_bench.doctor.dependency_closure", return_value=[]):
                    return decode(Environment, inspect(worker, "fake"))
            self.assertEqual(observe(healthy).clock, "tsc_validated")
            self.assertEqual(observe(healthy).clock_check, healthy)
            self.assertEqual(observe(replace(healthy, proven_skews=1)).clock, "monotonic")
            self.assertEqual(observe(None).clock, "monotonic")
            self.assertEqual(observe(healthy, clocksource="hpet").clock, "monotonic")
            # The measured values are evidence, never the class.
            self.assertEqual(observe(healthy).environment_class,
                             observe(replace(healthy, read_ns=20.0)).environment_class)


if __name__ == "__main__":
    unittest.main()
