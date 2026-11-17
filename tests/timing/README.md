# Constant-time measurement of the instructions the library uses

The ORAM's security argument ([src/core/DESIGN.md](../../src/core/DESIGN.md))
assumes that a secret permutation index, selection mask, occupancy mask or key
never changes how long an instruction takes. An attacker who can interrupt or
single-step a confidential VM can time individual instructions, so that
assumption must hold for each instruction, not just on average.
`avx512_constant_time_test` measures it on the host it runs on.

It covers every data-processing mnemonic the library emits, with and without
a write mask:
permutes and shuffles (their index vectors), compress, expand, masked moves
and masked compares (their masks), variable shifts (their counts), compares,
conflict detection and VP2INTERSECT (their data), AES (state and key),
mask-register instructions, and the BMI scalars applied to occupancy masks
(`pdep`, `bzhi`, `popcnt`, `tzcnt`, ...). Each entry measures one operand
form of its mnemonic, mostly zmm registers (see
[Operand forms](#operand-forms)). Each secret operand is tested with
hardcoded special cases and with random values:

- permutation indices: identity, zero, reverse, rotate, one table only, bits
  the instruction ignores, `vpshufb` clear-all
- masks: clear-all (zero), all ones, lowest bit, highest bit, even, odd, low
  half, high half, sparse, dense
- shift counts: 0, 1, width - 1, width, 255, huge
- conflict and intersect inputs: all distinct, all equal, pairs, disjoint,
  identical

The file header of
[avx512_constant_time_test.cpp](avx512_constant_time_test.cpp) describes the
method. In short:

1. A hand-written asm block runs the instruction 128 times (latency form, one
   dependency chain through the operand under test) or 192 times (throughput
   form, independent copies) between fenced TSC reads, with every operand held
   at the class's value.
2. Each round times every operand class once, in random order. The
   harness's memory accesses don't depend on the class: operands are placed at
   random slots, and samples are stored in execution order.
3. For each class, the test compares its mean paired difference from a random
   operand (the reference) and its outlier rate. The threshold keeps the whole
   run's family-wise false-alarm rate at 1e-3.

Alongside the timing test, [instruction_census.py](instruction_census.py)
checks the compiled binaries statically: every data-processing mnemonic in
library code must be one the timing test measures, and every masked memory
operation must have a public mask (see [On each target](#on-each-target)).
The census needs a build with line tables, so the default CTest run does not
include it.

## Where it must run

The evidence is per host. Run both checks on the CPU model, microcode and
platform (bare metal, TDX guest, SEV-SNP guest) that the paper's claims cover,
with the library built there with `-march=native`:

- The CPU must have the AVX-512 subsets the library is built for (see the
  top-level [README](../../README.md)). Entries whose instruction the host
  lacks, such as VP2INTERSECT on Intel servers, are listed as `skipped`; the
  library does not emit them on that host either, which the census confirms.
- The test reads the TSC directly and runs unchanged inside a TDX or SEV-SNP
  guest. The banner records CPU, microcode, kernel, hypervisor and the
  `tdx`/`sev` guest flags, so each JSON file names the platform it measured.
- Use an idle machine and pin with `--cpu` to a core whose SMT sibling is
  idle (see [Running it](#running-it)).

## Pass and fail

The last line is `VERDICT: PASS` or `VERDICT: FAIL`, and the exit status is 0
or 1 to match.

- **Smoke mode** (default; what CTest runs) passes unless some entry is `LEAK`
  or `INVALID` or the one-cycle control's status is anything but `detected`.
  `inconclusive` entries are allowed: a few seconds of data are not enough for
  a bound.
- **Certify mode** (`--certify`) also requires every entry to be `certified`:
  for every operand class, the upper bound on its difference from the random
  reference (`bound` below) is under the tolerance. A full certify run (no
  `--only`) must also have run the one-cycle control. This is the run whose
  JSON supports the side-channel claim.
- A run that measured nothing fails in both modes: every variant `--only`
  selected was skipped (the host lacks the instruction), or, in certify mode,
  only controls were selected. An `--only` pattern that names no variant is a
  usage error (exit status 2).
- **Null test** (`--certify --null-test`) must pass with nothing flagged, and
  the summary's t-statistic standard deviation should be near 1. It shows
  that the instrument's false-alarm rate and standard errors are honest on
  this host.

How to act on a failure:

- `LEAK` on a library instruction: the operand's value changes its timing on
  this host. Repeat pinned on an idle core. If it persists, the library must
  not apply that instruction to secret data on this target.
- `INVALID`: the entry's null class, a second random draw, was flagged, so
  the measurement of that entry is not trustworthy (for example, noise from
  other load). Re-run on a quieter machine.
- `inconclusive` in certify mode: the budget ran out before the bound fell
  below the tolerance. Raise `--max-rounds` or `--max-seconds`, or reduce
  noise.
- `control.one-cycle` not `detected`: the instrument failed its calibration
  on this run, and no result of the run counts. The line under it gives the
  measured difference, its expected value and `z * SE`.
  - `NOT-DETECTED`: a known difference of several cycles per sample was not
    flagged, or came out negative. The clock does not resolve the samples
    (too coarse, or its steps are not dithered by the sample's start time).
  - `MISCALIBRATED`: it was flagged, but measured outside half to one and a
    half times its expected value. The cycle conversion is off: the core
    clock changed between the ADD ruler and the control (see `clock drift`
    in the summary), or the TSC does not count steadily. Repeat pinned, with
    the frequency fixed if possible.
  - `UNRESOLVED`: measured correctly, but `z * SE` is above 0.5 cycles, so a
    difference of one cycle per sample would not be flagged reliably. The
    clock is too coarse or the core too noisy for the rounds run. Repeat on
    a quieter core.
  When the control's `t` is large and `z * SE` small, the clock does resolve
  one cycle per sample; the fault is elsewhere (frequency changes, load).
- `control.div64` reported as constant time is a note, not a failure: some
  cores have a constant-latency divider.

## Running it

```sh
cmake --build build --target avx512_constant_time_test

# Smoke mode, a few seconds. This is what CTest runs (serially, label
# `timing`). It fails only on a leak or a broken instrument.
build/tests/avx512_constant_time_test

# Certification: at least 100k rounds per variant (12.8M timed executions
# per class in the latency form), extended until every class is certified.
# A few minutes.
build/tests/avx512_constant_time_test --certify --cpu 4 --json certify.json

# Instrument validation: every class is drawn like the reference. Nothing may
# be flagged, and the t statistics must have a spread close to 1.
build/tests/avx512_constant_time_test --certify --null-test --cpu 4

# One instruction, every class printed.
build/tests/avx512_constant_time_test --only vpcompressb --verbose
```

Use an idle machine. Pin with `--cpu` to a core whose SMT sibling is idle.
Load from other programs costs precision, and the certify mode then needs
more rounds. It doesn't cause false leaks, because noise falls on every class
alike.

## Reading the report

One line per instruction, operand role and form:

| column | meaning |
| --- | --- |
| `cyc/op` | cost of one instruction in the chain, in core cycles. The latency form includes the two-XOR restore, so compare it only across classes, not with published latencies. |
| `worst class` | a flagged class if any, else the class with the largest bound |
| `t` | that class's paired t statistic against the random reference |
| `bound` | the largest difference, in core cycles per instruction, that the data still allows for that class (`|mean| + z * SE`) |
| `tail-p` | exact binomial p-value for its outlier count against the reference |
| `status` | `certified`, `inconclusive` (the bound is not yet below the tolerance), `LEAK`, or `INVALID` (the null class, a second random draw, was flagged, so the instrument failed on this entry) |

The default tolerance is 0.05 core cycles per instruction (`--tolerance`). An
operand-dependent latency would show up as at least one whole cycle per
instruction in the latency form, 20 times the tolerance.

The summary also reports:

- the family-wide spread of t statistics (mean about 0, sd about 1, when
  nothing leaks; an sd well above 1 means this host's noise defeats the
  standard errors);
- the largest bound;
- the two instrument controls:
  - `control.one-cycle`: two kernels whose ADD chains differ by one ADD per
    loop iteration, a known difference of `--iters` cycles per sample (8 by
    default). It must be detected, measured within half to one and a half
    times that value, and with `z * SE` (the paired difference's standard
    error times the leak threshold) at most 0.5 cycles. Then a difference of
    a single cycle per sample, one cycle per 128 instructions, would be
    flagged with `|t|` at least twice the threshold, even when the TSC
    advances in steps of tens of ticks, as it does under some hypervisors.
    The known difference lies inside the steady-state chain: one extra ADD
    next to the clock reads is partly absorbed by the fences and does not
    cost one cycle on every core. The two kernels have the same bytes and
    placement, except that the base's extra ADD is off the dependency chain.
  - `control.div64`: 64-bit DIV, whose latency depends on the dividend on
    current x86 cores, is expected to be flagged. That shows the harness sees
    real operand-dependent timing.

`--json` writes every per-class statistic for comparison across hosts.

## On each target

The library is compiled with `-march=native`, so the instructions it contains
differ by host. Intel servers have no VP2INTERSECT, for example, and select
the xor + unsigned-min fallback. On the target:

1. Build natively and take the census of what the library actually emits.
   Line tables let it separate library code from tests:
   ```sh
   cmake -S . -B build-g1 -DCMAKE_CXX_FLAGS=-g1 -DCPU_BYTESLICE_ORAM_BUILD=all
   cmake --build build-g1 -j
   python3 tests/timing/instruction_census.py build-g1/tests/cpu_* \
       build-g1/benchmarks/cpu_* --timing-test build-g1/tests/avx512_constant_time_test
   ```
   Or let CTest run it over the test binaries (not the benchmarks): configure
   with `-DCPU_BYTESLICE_ORAM_INSTRUCTION_CENSUS=ON` (off by default). This
   compiles the test binaries with `-g1`, which adds line tables and does not
   change the generated code, and registers the test `instruction_census`
   (`ctest -L census`).

   The census exits non-zero unless two lists are empty:
   - `uncovered`: add an entry to `BuildEntries()`. A masked form with a
     memory operand needs its register form measured (`vpermd{k}{z} mem`
     needs `vpermd{k}{z}`), whole-table permutes included; gathers and
     scatters have no register form.
   - `masked-mem, UNREVIEWED`: memory operations under a mask that
     [masked_memory_allowlist.txt](masked_memory_allowlist.txt) does not
     record as public.

   Under a secret mask such an operation reads memory chosen by the secret.
   GCC creates them from `secret & compare(x, load)` and from masked moves or
   expands of spilled values. Fix the site with the register-only forms in
   `src/core/mov_intrinsics.hpp`, or add an allowlist entry that explains why
   the mask is public. An entry matches only the source line that carries
   its text; a statement split across lines whose line table names another
   of its lines needs an entry for that line as well.

   Library code is any file whose real path lies under the real path of the
   checkout's `src/` or `include/`; the census prints these roots and how
   many instructions of each binary it attributed to them. It also fails
   when a binary with line tables has none attributed and its line tables
   name files outside the checkout (built from another checkout, or paths
   rewritten by `-ffile-prefix-map`; pass `--repo` with the checkout the
   binary was built from), and when line tables name relative paths. A
   benchmark of the host alone (`cpu_cache_latency_benchmark`, ...), whose
   files all lie in the checkout outside `src/` and `include/`, is noted
   with no library code. A binary without line tables is listed whole, test
   code included, as a preview: its masked memory operations have no source
   line to match the allowlist, so they are all `UNREVIEWED` and the census
   fails.
2. Run `--certify --json` and `--certify --null-test`, pinned, on an idle
   machine. Keep the JSON with the other results for that target.

A target's code generation can be previewed from another machine with
[march_launcher.sh](march_launcher.sh), which replaces `-march=native` at
compile time; the census only disassembles. This matters because code
generation differs between targets: for Intel targets such as Granite Rapids,
GCC vectorizes some loops into gathers and scatters, whose index vectors must
be public, and it can spill a vector that a secret mask then reads back from
memory. Both show up only in that target's build.

The census also lists instructions whose latency depends on operand values
(`variable`: integer divide and floating-point arithmetic, including compares
and conversions). These must see only public operands. On current x86 cores
that includes the numerator of a `div`: the test's DIV control divides by a
public 3 and still sees the latency vary with the dividend.
Division by a compile-time constant compiles to a multiply and is not listed.
The census lists each with its source lines for review; it does not check
that the operands are public, and this list does not change its exit status.
FP-domain shuffles, blends and bitwise operations (`vshufps`, `vinsertps`,
`vblendvpd`, `vxorpd`, ...) are not in this list: they have no
operand-dependent latency, GCC uses some of them on secret integer data, and
the timing test measures those the library emits.

### Operand forms

The census matches by mnemonic and mask decoration (`{k}`, `{k}{z}`), not by
operand form, and each timing entry measures one form: register operands,
mostly zmm (the `VEX` entries use xmm or ymm), an immediate shift count, a
general-purpose source for broadcasts, predicate 1 for `vpcmp*`. `vpsrlw`,
`vpsrlq` and `vpsllq` are also measured with the count in an xmm register
(role `data-xcount`), the form the library applies to secret radix digits and
tags. The library also emits other forms of measured mnemonics: xmm and ymm
widths of EVEX instructions, memory source operands, broadcasts from xmm or
memory, other compare predicates and immediates, and `kmov` to or from
memory. Those forms are assumed to time like the measured one; that is an
extrapolation, not a measurement. Memory source operands add a load at a
public address.

## Summaries and identity checks

[analysis/timing_summary.py](../../analysis/timing_summary.py) turns
certify/null-test JSON (and census output) into a per-form CSV, a
Markdown/LaTeX table and an identity check that the files of one target agree
on CPU, microcode, kernel and test configuration (unsupported forms are rows,
missing fields are "unavailable"). The statistical method is censored paired
differences against a random reference with a normal threshold (see
[constant_time_stats.hpp](constant_time_stats.hpp)); it is neither Welch's
t-test nor dudect.

## What this does not show

- **Other hosts.** Results hold for this CPU model, microcode and platform.
  Intel documents operand-independent timing (DOIT) for a listed set of
  instructions only while the DOITM mode bit is set on Ice Lake and later
  cores. A guest usually can neither read nor set that bit, so the
  measurement on the specific host is the evidence.
- **Memory operands.** Their addresses are public by construction. Masked
  memory operands are the census's `masked-mem` check.
- **Other operand forms** of a measured mnemonic (widths, memory sources,
  register shift counts; see [Operand forms](#operand-forms)).
- **Public operands of `variable` instructions.** The census lists these
  sites; a reviewer checks them.
- **Power and frequency effects over milliseconds** (Hertzbleed-style). Each
  sample is well under a microsecond and classes interleave, so a slow drift
  falls on every class alike. `--iters` lengthens the blocks if that regime
  matters.
- **Speculative and physical channels** beyond timing.
