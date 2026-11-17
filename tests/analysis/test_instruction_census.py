"""tests/timing/instruction_census.py on synthetic objdump listings: library
attribution through real paths, failure when nothing is attributed, the
listing without line tables, register forms of masked memory operations, and
allowlist entries that match one source line only."""
import contextlib
import io
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tests" / "timing"))
import instruction_census  # noqa: E402

HEADER = "x:     file format elf64-x86-64\n\nDisassembly of section .text:\n\n"
COVERED = "# keys\nvmovdqu8{k}{z}\nvpermt2b{k}{z}\nvpaddq\n"


def listing(src, lines_tables=True):
    """A masked load on line 2 of src/core/k.hpp, one on line 3, and a
    memory-table permute whose register form is not covered."""
    def at(n):
        return "%s:%d\n" % (src, n) if lines_tables else ""
    return (HEADER + "0000000000001000 <f>:\n" + ("f():\n" if lines_tables else "") +
            at(2) + "    1000:\tvmovdqu8 zmm0{k1}{z},ZMMWORD PTR [rdi]\n" +
            at(3) + "    1006:\tvmovdqu8 zmm1{k2}{z},ZMMWORD PTR [rsi]\n" +
            at(4) + "    100c:\tvpermd zmm1{k1}{z},zmm0,ZMMWORD PTR [rsi]\n" +
            "    1012:\tvpaddq zmm1,zmm1,zmm0\n")


class CensusTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.repo = root / "repo"
        (self.repo / "src" / "core").mkdir(parents=True)
        (self.repo / "src" / "core" / "k.hpp").write_text(
            "// header\n"
            "  a = _mm512_maskz_loadu_epi8(lane, p);\n"
            "  b = _mm512_maskz_loadu_epi8(secret, q);\n"
            "  c = _mm512_maskz_permutexvar_epi32(secret, idx, t);\n")
        self.link = root / "link"
        os.symlink(self.repo, self.link)
        self.other = root / "other"
        (self.other / "src").mkdir(parents=True)
        self.allow = root / "allow.txt"
        self.allow.write_text("src/core/k.hpp | _mm512_maskz_loadu_epi8(lane, | tail mask\n")
        self.covered = root / "covered.txt"
        self.covered.write_text(COVERED)

    def tearDown(self):
        self.tmp.cleanup()

    def run_census(self, text, repo):
        fake = subprocess.CompletedProcess([], 0, stdout=text, stderr="")
        argv = ["instruction_census.py", "bin", "--covered-file", str(self.covered),
                "--allowlist", str(self.allow), "--repo", str(repo)]
        out = io.StringIO()
        with mock.patch.object(instruction_census.subprocess, "run", return_value=fake), \
                mock.patch.object(sys, "argv", argv), contextlib.redirect_stdout(out):
            status = instruction_census.main()
        return status, out.getvalue()

    def section(self, out, title):
        body = out.split("== " + title, 1)[1].split("\n\n", 1)[0]
        return body.splitlines()[1:]

    def test_symlinked_checkout_is_attributed(self):
        # The binary names the symlink; the census runs on the real path.
        status, out = self.run_census(listing(str(self.link / "src/core/k.hpp")), self.repo)
        self.assertIn("bin: 4 instructions in library code", out)
        self.assertNotIn("ERROR", out)
        self.assertEqual(status, 1)  # the mutations below are reported

    def test_other_checkout_fails(self):
        status, out = self.run_census(listing(str(self.repo / "src/core/k.hpp")), self.other)
        self.assertEqual(status, 1)
        self.assertIn("# ERROR bin: no instruction is attributed", out)

    def test_library_from_another_checkout_fails(self):
        # The binary's own file is in the checkout, its library code is not.
        own = "%s:1\n" % (self.repo / "tests" / "t.cpp")
        text = listing(str(self.other / "src/core/k.hpp")).replace("f():\n", "f():\n" + own)
        status, out = self.run_census(text, self.repo)
        self.assertEqual(status, 1)
        self.assertIn("# ERROR bin: no instruction is attributed", out)

    def test_binary_without_library_code_is_noted(self):
        text = (HEADER + "0000000000001000 <f>:\nf():\n" +
                "%s:3\n" % (self.repo / "benchmarks" / "b.cpp") +
                "    1000:\tvpaddq zmm1,zmm1,zmm0\n")
        status, out = self.run_census(text, self.repo)
        self.assertEqual(status, 0)
        self.assertIn("bin: 0 instructions in library code (its sources include none)", out)

    def test_relative_paths_fail(self):
        status, out = self.run_census(listing("src/core/k.hpp"), self.repo)
        self.assertEqual(status, 1)
        self.assertIn("relative paths", out)

    def test_allowlist_matches_the_named_line_only(self):
        _, out = self.run_census(listing(str(self.repo / "src/core/k.hpp")), self.repo)
        reviewed = self.section(out, "masked-mem, allowlisted")
        unreviewed = self.section(out, "masked-mem, UNREVIEWED")
        self.assertEqual(len(reviewed), 1)
        self.assertTrue(reviewed[0].endswith("src/core/k.hpp:2"))
        self.assertEqual(len(unreviewed), 1)
        self.assertTrue(unreviewed[0].endswith("src/core/k.hpp:3"))

    def test_memory_table_permute_needs_its_register_form(self):
        _, out = self.run_census(listing(str(self.repo / "src/core/k.hpp")), self.repo)
        self.assertTrue(any(l.startswith("vpermd{k}{z} mem") for l in self.section(out, "uncovered")))

    def test_without_line_tables_lists_the_whole_binary(self):
        status, out = self.run_census(listing("unused", lines_tables=False), self.repo)
        self.assertEqual(status, 1)
        self.assertIn("no line tables", out)
        self.assertEqual(self.section(out, "masked-mem, UNREVIEWED"),
                         ["vmovdqu8{k}{z} mem            2  ?"])


if __name__ == "__main__":
    unittest.main()
