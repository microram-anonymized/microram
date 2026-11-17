"""`doctor`'s confidential-guest memory evidence (analysis/oram_bench/guest_memory.py):
private vs. shared (swiotlb) and unaccepted memory, from fixtures (no guest needed)."""
import subprocess
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).parent))
from analysis.oram_bench.codec import decode, plain
from analysis.oram_bench.guest_memory import (GuestMemory, assess_guest_memory, capture_guest_memory,
                                              read_dmesg)
from test_oram_bench_tee import PLAIN, snp_guest, tdx_guest

MIB = 1024**2
MEMINFO = "MemTotal:       16777216 kB\nMemFree: 1 kB\nHugePages_Total:       0\nHugepagesize:       2048 kB\n"
UNACCEPTED = "Unaccepted:      1048576 kB\n"
DMESG = "[0.1] x\n[0.5] software IO TLB: mapped [mem 0x00000000bbfff000-0x00000000bffff000] (64MB)\n"


class GuestMemoryTests(unittest.TestCase):
    def test_tdx_guest_with_dmesg_pool(self):
        g = assess_guest_memory("tdx", tdx_guest(), MEMINFO + UNACCEPTED, "ro quiet", DMESG, None, {"debugfs": "permission"})
        self.assertEqual((g.private_memory, g.guest_ram_bytes, g.unaccepted_bytes), ("applicable", 16 * 1024 * MIB, 1024 * MIB))
        self.assertEqual((g.shared_bounce_bytes, g.shared_bounce_source), (64 * MIB, "dmesg"))
        self.assertEqual(g.private_bytes_estimate, (16 * 1024 - 1024 - 64) * MIB)
        self.assertIn("estimate", g.private_estimate_basis)
        self.assertEqual(g.unavailable, ["swiotlb_debugfs:permission"])
        self.assertEqual((g.hugetlb_pages, g.hugetlb_page_bytes), (0, 2 * MIB))
        self.assertEqual(decode(GuestMemory, plain(g)), g)

    def test_snp_guest_debugfs_wins_and_cmdline_is_a_request(self):
        g = assess_guest_memory("snp", snp_guest(), MEMINFO + "Unaccepted: 0 kB\n", "swiotlb=65536,4", DMESG, 32768)
        self.assertEqual((g.shared_bounce_bytes, g.shared_bounce_source), (64 * MIB, "debugfs"))
        self.assertEqual(g.unavailable, [])
        g = assess_guest_memory("snp", snp_guest(), MEMINFO + "Unaccepted: 0 kB\n", "swiotlb=65536,4", None, None,
                                {"debugfs": "permission", "dmesg": "permission"})
        self.assertEqual((g.shared_bounce_bytes, g.shared_bounce_source), (128 * MIB, "cmdline_request"))
        self.assertEqual(g.unavailable, ["swiotlb_debugfs:permission", "swiotlb_dmesg:permission"])

    def test_native_host_is_not_applicable(self):
        g = assess_guest_memory("native", PLAIN, MEMINFO, "ro", DMESG, None)
        self.assertEqual(g.private_memory, "not_applicable")
        self.assertEqual((g.unaccepted_bytes, g.shared_bounce_bytes, g.private_bytes_estimate), (None, None, None))
        self.assertEqual(g.guest_ram_bytes, 16 * 1024 * MIB)
        self.assertEqual(g.unavailable, ["unaccepted_bytes:not_applicable", "shared_bounce_bytes:not_applicable",
                                         "private_bytes_estimate:not_applicable"])

    def test_missing_evidence_is_named_never_inferred(self):
        g = assess_guest_memory("tdx", tdx_guest(), MEMINFO, "ro", None, None,
                                {"debugfs": "permission", "dmesg": "permission"})
        self.assertEqual((g.unaccepted_bytes, g.shared_bounce_bytes, g.private_bytes_estimate), (None, None, None))
        self.assertEqual(g.unavailable, ["unaccepted_bytes:no_meminfo_line", "swiotlb_debugfs:permission",
                                         "swiotlb_dmesg:permission", "swiotlb_cmdline:no_swiotlb_parameter",
                                         "shared_bounce_bytes:not_reported", "private_bytes_estimate:inputs_missing"])
        g = assess_guest_memory("tdx", None, None, None, None, None, {"meminfo": "missing"})
        self.assertIsNone(g.guest_ram_bytes)
        self.assertIn("guest_ram_bytes:missing", g.unavailable)
        self.assertEqual(g.private_memory, "applicable")  # the label alone makes it applicable

    def test_dmesg_failure_is_permission_and_needs_no_root(self):
        def failing(command, **kw):
            return subprocess.CompletedProcess(command, 1, "", "dmesg: read kernel buffer failed: Operation not permitted")
        self.assertEqual(read_dmesg(failing), (None, "permission"))
        def absent(command, **kw):
            raise FileNotFoundError
        self.assertEqual(read_dmesg(absent), (None, "missing"))
        ok = lambda command, **kw: subprocess.CompletedProcess(command, 0, DMESG, "")
        self.assertEqual(read_dmesg(ok), (DMESG, None))

    def test_capture_threads_reasons(self):
        files = {"/proc/meminfo": MEMINFO + UNACCEPTED, "/proc/cmdline": "ro"}
        read = lambda path: (files[path], None) if path in files else (None, "permission")
        g = capture_guest_memory("tdx", tdx_guest(), read, lambda: (None, "permission"))
        self.assertEqual(g.unavailable[:2], ["swiotlb_debugfs:permission", "swiotlb_dmesg:permission"])
        self.assertEqual(g.unaccepted_bytes, 1024 * MIB)


if __name__ == "__main__":
    unittest.main()
