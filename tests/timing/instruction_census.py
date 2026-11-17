#!/usr/bin/env python3
"""Instruction census for the constant-time timing test.

Disassembles compiled binaries, keeps the instructions that came from the
library's own headers (src/ and include/), and compares the data-processing
mnemonics among them with the list the timing test covers
(`avx512_constant_time_test --list`).

The key is the mnemonic, plus {k} or {k}{z} for a masked form (and " mem"
when that masked form has a memory operand).  Operand widths and kinds are not
part of it: an xmm or ymm form, a memory source operand, a shift count in a
register or an immediate, and a broadcast from a register or from memory all
count as the mnemonic the timing test measures in one form (see the timing
test's README).

Library attribution needs line tables.  Build with -g1 (the timing test's
README shows the two commands).  An intrinsic's instruction is attributed to
the innermost inlined frame outside the compiler's headers (objdump
--inlines), so `_mm512_maskz_compress_epi8` counts where the library called
it.  A frame is library code when its real path (symlinks resolved) lies under
the real path of --repo's src/ or include/; the roots are printed, and so is
the count attributed per binary.  A binary with line tables that attributes no
instruction to library code is an error when they name a file outside the
checkout and the system directories, or no file of the checkout (it was built
from another checkout, or its paths were remapped); one whose files all lie in
the checkout outside src/ and include/ (a benchmark of the host alone) is
noted.  A line table that names relative paths is an error.  Without line
tables every instruction
in the binary is counted, test and benchmark code included, which over-reports
but never misses anything; its masked memory operations then have no source
line to match an allowlist entry, so all of them are UNREVIEWED and the census
fails.  That listing is a preview; rebuild with -g1 for a verdict.

The census must be re-run on every target: the library is compiled with
-march=native, so the instructions it contains differ by host (no
VP2INTERSECT on Intel servers selects the xor + unsigned-min fallback, for
example).

Output sections:
  uncovered   data-processing instructions in library code that the timing
              test does not measure.  Should be empty; otherwise add a
              variant or record why the instruction cannot see a secret.  A
              masked form with a memory operand needs its register form
              measured (`vpermd{k}{z} mem` needs `vpermd{k}{z}`), except
              gathers and scatters, which have none.
  variable    instructions whose latency is known to depend on operand values
              on some x86 cores: integer divide and floating-point
              arithmetic (add, multiply, divide, square root, compares,
              conversions, ...).  They are acceptable only on public
              operands; each is listed with its source lines for review.
              The census does not check that their operands are public, and
              this section does not affect the exit status.  FP-domain
              shuffles, blends and bitwise operations (vshufps, vinsertps,
              vxorpd, ...) are not in it: they have no operand-dependent
              latency, GCC also uses them on integer data, and the timing test
              measures the ones the library emits.
  masked-mem  memory operations under a write/read mask.  The mask must be
              public (a tail length, a constant), never a secret selection:
              GCC folds `secret & cmp(x, load)` into a compare that reads
              memory under the secret mask (src/core/DESIGN.md).  Every site
              must match an entry of masked_memory_allowlist.txt, which records
              why its mask is public: the entry's text must appear on the very
              source line the line table names; permutes with a memory table
              are exempt (no fault suppression, the whole table is read).
              Gathers and scatters appear here too (they always take a mask):
              for them the INDEX vector is an address and must be public as
              well.

Exit status: 0 when `uncovered` is empty, every masked memory operation is
allowlisted and no binary failed attribution (above); 1 otherwise.
"""

import argparse
import collections
import os
import re
import subprocess
import sys

# Mnemonics whose timing does not depend on operand values on the targets, or
# that never see ORAM data: control flow, scalar integer ALU, moves, fences,
# feature detection.  Masked vector forms are never exempt (the key carries
# a "{k}" suffix and does not match these patterns).
EXEMPT_PATTERNS = [
    # control flow, stack, padding, traps
    r"j[a-z]+", r"call", r"ret", r"push", r"pop", r"leave", r"endbr64",
    r"nop[wl]?", r"xchg ax,ax", r"ud2", r"int3", r"hlt", r"cs", r"ds",
    r"data16",
    # scalar integer ALU (Intel's data-operand-independent-timing list
    # covers these; AMD documents no operand-dependent timing for them)
    r"add", r"adc", r"sub", r"sbb", r"and", r"or", r"xor", r"not", r"neg",
    r"inc", r"dec", r"lea", r"cmp", r"test", r"sh[lr]", r"sa[lr]", r"ro[lr]",
    r"shld", r"shrd", r"rc[lr]", r"set[a-z]+", r"mov", r"movzx", r"movsx",
    r"movsxd", r"movabs", r"movbe", r"cdqe", r"cqo", r"cdq", r"cwde", r"cbw",
    r"cwd", r"xchg",
    r"bswap", r"bt[crs]?", r"xadd", r"cmpxchg", r"cmpxchg16b", r"lock",
    r"rep", r"repz", r"repnz", r"stos[bwdq]?", r"movs[bwdq]?",
    # fences, timing, feature detection, cache and wait hints
    r"[lsm]fence", r"pause", r"rdtscp?", r"cpuid", r"xgetbv", r"prefetch.*",
    r"clflush(opt)?", r"clwb", r"monitorx", r"mwaitx", r"umonitor", r"umwait",
    r"tpause", r"syscall", r"rdpid", r"rdrand", r"rdseed",
    # unmasked vector moves, loads, stores; memory-only broadcasts
    r"vmovdq[au](8|16|32|64)?", r"vmov[qdw]", r"vmovntdq(a)?", r"vmov[au]p[sd]",
    r"vbroadcasti(32x4|64x2|32x8|64x4|128)",
    r"vmov[su][sd]", r"vmov[hl]p[sd]", r"vmovddup", r"vzeroupper", r"vzeroall",
    r"movdq[au]", r"mov[qd]", r"movap[sd]", r"movup[sd]", r"movs[sd]",
    r"vmovntdqa",
    # Cache residency hint at a public start/progress/reply address.
    # No secret operand; arrival/content timing is outside instruction timing.
    r"cldemote",
]
EXEMPT_RE = re.compile(r"^(?:" + "|".join(EXEMPT_PATTERNS) + r")$")

# Instructions with operand-dependent latency on at least one x86 core:
# integer divide, FP arithmetic (subnormal operands), x87.  FP-domain
# shuffles, blends and bitwise operations are not: they must be measured.
VARIABLE_RE = re.compile(
    r"^(?:i?div|v?(?:div|sqrt|rsqrt|rcp)[sp][sd]|"
    r"v?(?:add|sub|mul|min|max|cmp[a-z]*|comi|ucomi|fn?m(?:add|sub)\d*|round|"
    r"rndscale|getexp|getmant|cvt[a-z0-9]*)[sp][sd]|"
    r"v?cvt[a-z0-9]+|vfn?m(?:add|sub)[a-z0-9]*|f[a-z]+)$")

# Gathers and scatters only exist with a memory operand and a mask; their
# index vector is an address, reviewed under masked-mem.
GATHER_SCATTER_RE = re.compile(r"^vp?(?:gather|scatter)[a-z0-9]*\{")

# vpcmp{pred}{type} and vcmp{pred}{type} print the predicate in the mnemonic.
VPCMP_PRED_RE = re.compile(
    r"^vpcmp(eq|neq|lt|le|nlt|nle|false|true)(u?[bwdq])$")

# Permutes with a memory table: exception class E4NF, no fault suppression,
# so the whole table is read whatever the mask.
FULL_READ_RE = re.compile(r"^vperm(i2|t2)?[bwdq]\{")

INSN_RE = re.compile(r"^\s*[0-9a-f]+:\s+(\S.*)$")
# Relative paths are matched too, so that they are seen (and refused) rather
# than skipped while the previous frame stays current.
LINE_RE = re.compile(r"^(\S+?):(\d+)(?: \(discriminator \d+\))?$")
INLINED_RE = re.compile(r"^inlined by (\S+?):(\d+)(?: \(discriminator \d+\))?")
SYSTEM_PREFIXES = ("/usr/", "/opt/")
PREFIXES = {"lock", "rep", "repz", "repnz", "repe", "repne", "bnd",
            "notrack", "data16", "addr32", "cs", "ds", "es", "ss", "{evex}",
            "{vex}"}


def normalize(text):
    """(key, masked_memory) for one disassembled instruction."""
    text = text.split("#")[0].split("<")[0].strip()
    parts = text.split(None, 1)
    while parts and parts[0] in PREFIXES:
        parts = parts[1].split(None, 1) if len(parts) > 1 else []
    if not parts:
        return None, False
    mnemonic = parts[0]
    operands = parts[1] if len(parts) > 1 else ""
    if mnemonic.startswith("cmov"):
        mnemonic = "cmovcc"  # one flag read; the timing test covers ZF, CF|ZF, SF
    m = VPCMP_PRED_RE.match(mnemonic)
    if m and m.group(1) != "eq":
        mnemonic = "vpcmp" + m.group(2)
    elif m and m.group(2).startswith("u"):
        mnemonic = "vpcmp" + m.group(2)
    masked = re.search(r"\{k[1-7]\}", operands) is not None
    zeroing = "{z}" in operands
    memory = "[" in operands
    if masked and memory:
        return mnemonic + ("{k}{z}" if zeroing else "{k}") + " mem", True
    if masked:
        return mnemonic + ("{k}{z}" if zeroing else "{k}"), False
    return mnemonic, False


class Library:
    """Which source paths are library code: real paths under the real path of
    the checkout's src/ and include/."""

    def __init__(self, repo):
        self.repo = os.path.realpath(repo)
        self.roots = [os.path.join(self.repo, d) + os.sep for d in ("src", "include")]
        self._cache = {}
        self._inside = {}

    def relative(self, path):
        """The repository-relative path of a library file, else None."""
        if path not in self._cache:
            real = os.path.realpath(path) if os.path.isabs(path) else ""
            self._cache[path] = (os.path.relpath(real, self.repo)
                                 if real.startswith(tuple(self.roots)) else None)
        return self._cache[path]

    def inside(self, path):
        """Whether an absolute path lies in the checkout (library or not)."""
        if path not in self._inside:
            self._inside[path] = os.path.realpath(path).startswith(self.repo + os.sep)
        return self._inside[path]


def census(binary, library):
    """Per-key counts and example source locations for one binary, whether it
    has line tables, how many instructions it attributes to library code, the
    relative paths its line tables name, whether they name a file of the
    checkout, and one file outside the checkout and the system directories
    that they name (None if there is none)."""
    proc = subprocess.run(
        ["objdump", "-d", "-l", "--inlines", "--no-show-raw-insn", "-Mintel",
         binary], check=True, capture_output=True, text=True)
    lines = proc.stdout.splitlines()
    has_lines = any(LINE_RE.match(l) or INLINED_RE.match(l) for l in lines)
    counts = collections.Counter()
    where = collections.defaultdict(collections.Counter)
    masked_mem = collections.defaultdict(collections.Counter)
    chain = []       # innermost frame first
    current = None   # innermost frame outside the compiler's headers
    attributed = 0
    relative = set()
    inside = False
    outside = None
    for line in lines:
        lm = LINE_RE.match(line)
        im = INLINED_RE.match(line) if not lm else None
        if lm or im:
            m = lm or im
            if lm:
                chain = []
            path = m.group(1)
            if not os.path.isabs(path):
                relative.add(path)
            elif library.inside(path):
                inside = True
            elif not path.startswith(SYSTEM_PREFIXES) and (
                    outside is None or ("/src/" in path or "/include/" in path)
                    and not ("/src/" in outside or "/include/" in outside)):
                outside = path  # preferably one that looks like library code
            chain.append((path, int(m.group(2))))
            current = next((f for f in chain
                            if library.relative(f[0]) or
                            not f[0].startswith(SYSTEM_PREFIXES)), None)
            continue
        im = INSN_RE.match(line)
        if not im:
            continue
        if has_lines:
            # Code ahead of the first line entry (.init, .plt) and code whose
            # innermost frame outside the compiler's headers is not library
            # code are skipped.
            rel = library.relative(current[0]) if current else None
            if rel is None:
                continue
            loc = "%s:%d" % (rel, current[1])
        else:
            loc = "?"
        key, is_masked_mem = normalize(im.group(1))
        if key is None:
            continue
        attributed += 1
        counts[key] += 1
        where[key][loc] += 1
        if is_masked_mem:
            masked_mem[key][loc] += 1
    return counts, where, masked_mem, has_lines, attributed, relative, inside, outside


def load_allowlist(path):
    """[(path, text, reason)] from masked_memory_allowlist.txt."""
    entries = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = [p.strip() for p in line.split(" | ", 2)]
            if len(parts) != 3:
                raise SystemExit("bad allowlist line: " + line)
            entries.append(tuple(parts))
    return entries


def allowlisted(loc, entries, repo, cache={}):
    """Whether the source line at `loc` (repository-relative path:line)
    carries the text of an entry for that file.  Only that line counts: a
    statement split across lines whose line table names another of its lines
    needs an entry for that line too.  A location without a line (no line
    tables) matches nothing."""
    path, _, line = loc.rpartition(":")
    if not path or not line.isdigit():
        return False
    if path not in cache:
        try:
            with open(os.path.join(repo, path)) as f:
                cache[path] = f.read().splitlines()
        except OSError:
            cache[path] = []
    n = int(line)
    text_at = cache[path][n - 1] if 0 < n <= len(cache[path]) else None
    return text_at is not None and any(
        p == path and text in text_at for p, text, _ in entries)


def covered_keys(args):
    if args.covered_file:
        with open(args.covered_file) as f:
            text = f.read()
    else:
        text = subprocess.run([args.timing_test, "--list"], check=True,
                              capture_output=True, text=True).stdout
    keys = set()
    for line in text.splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            keys.add(line.split()[0])
    return keys


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("binaries", nargs="+")
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument("--timing-test",
                       help="path to avx512_constant_time_test (runs --list)")
    group.add_argument("--covered-file",
                       help="file holding the output of --list")
    ap.add_argument("--repo", default=os.path.dirname(os.path.dirname(
        os.path.dirname(os.path.abspath(__file__)))),
                    help="the checkout the binaries were built from (default: "
                         "the one holding this script); its src/ and include/ "
                         "are library code")
    ap.add_argument("--locations", type=int, default=3,
                    help="source locations printed per key")
    ap.add_argument("--allowlist", default=os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "masked_memory_allowlist.txt"),
                    help="reviewed masked memory statements")
    args = ap.parse_args()

    library = Library(args.repo)
    total = collections.Counter()
    where = collections.defaultdict(collections.Counter)
    masked = collections.defaultdict(collections.Counter)
    unattributed, attribution, errors = [], [], []
    for b in args.binaries:
        c, w, m, has_lines, n, relative, inside, outside = census(b, library)
        note = "in library code"
        if not has_lines:
            unattributed.append(b)
            note = "(no line tables: the whole binary)"
        elif relative:
            errors.append("%s: its line tables name relative paths (e.g. %s), "
                          "which cannot be placed; rebuild without a file or "
                          "debug prefix map" % (b, sorted(relative)[0]))
        elif n == 0 and (outside or not inside):
            # Nothing attributed, and the line tables name files outside the
            # checkout (or none of it): another checkout or remapped paths.
            errors.append("%s: no instruction is attributed to library code "
                          "under the roots above; its line tables name %s. "
                          "Pass --repo with the checkout it was built from"
                          % (b, "e.g. " + outside if outside
                             else "no file of the checkout"))
        elif n == 0:
            # Every file it names is in the checkout, none in src/ or include/.
            note = "in library code (its sources include none)"
        attribution.append("# %s: %d instructions %s" % (b, n, note))
        total.update(c)
        for k, v in w.items():
            where[k].update(v)
        for k, v in m.items():
            masked[k].update(v)

    covered = covered_keys(args)
    allow = load_allowlist(args.allowlist)

    def locs(counter):
        return ", ".join("%s (%d)" % (l, n)
                         for l, n in counter.most_common(args.locations))

    uncovered, variable = [], []
    for key, n in total.most_common():
        # A masked form with a memory operand needs its register form timed;
        # gathers and scatters have none (masked-mem reviews them).
        base = key.split()[0]
        if key.endswith(" mem") and GATHER_SCATTER_RE.match(base):
            continue
        if base in covered:
            continue
        if VARIABLE_RE.match(base):
            variable.append((key, n))
        elif not EXEMPT_RE.match(base):
            uncovered.append((key, n))

    print("# library code: %s" % ", ".join(library.roots))
    for line in attribution:
        print(line)
    if unattributed:
        print("# no line tables (whole binary counted; its masked memory "
              "operations cannot match the allowlist): " + " ".join(unattributed))
    for e in errors:
        print("# ERROR " + e)
    print("# %d distinct instruction keys in library code, %d covered by the "
          "timing test" % (len(total), sum(1 for k in total if k in covered)))
    print("\n== uncovered (%d) ==" % len(uncovered))
    for key, n in uncovered:
        print("%-22s %8d  %s" % (key, n, locs(where[key])))
    print("\n== variable (%d): public operands only ==" % len(variable))
    for key, n in variable:
        print("%-22s %8d  %s" % (key, n, locs(where[key])))
    unreviewed, reviewed, full_read = [], [], []
    for key, counter in masked.items():
        for loc, n in counter.items():
            if FULL_READ_RE.match(key):
                full_read.append((key, loc, n))
            elif allowlisted(loc, allow, library.repo):
                reviewed.append((key, loc, n))
            else:
                unreviewed.append((key, loc, n))
    for title, rows in (
            ("masked-mem, UNREVIEWED: a secret mask here gates memory", unreviewed),
            ("masked-mem, allowlisted public masks", reviewed),
            ("masked-mem, whole-table permutes", full_read)):
        print("\n== %s (%d) ==" % (title, len(rows)))
        for key, loc, n in sorted(rows, key=lambda t: -t[2]):
            print("%-22s %8d  %s" % (key, n, loc))
    if errors:
        print("\nFAIL: %d binaries could not be attributed (see # ERROR above)"
              % len(errors))
    return 1 if uncovered or unreviewed or errors else 0


if __name__ == "__main__":
    sys.exit(main())
