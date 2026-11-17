# Core primitives

See [DESIGN.md](DESIGN.md) for the selection and waiting contracts.

- `mov_intrinsics.hpp`: `CMOV8`, `obliSelectU64`, `obliPin512`,
  `obliLoad512`, `obliAssignBytes`, and the register-only secret-masked
  forms `obliCmpEqMask8/32/64`, `obliCmpGtU8Mask`, `obliCmpGeU8Mask`,
  `obliTestMask8/32/64`, `obliTestNMask8/32/64`, `obliMaskMov8/32/64` and
  `obliMaskExpand8`.
- `monitor_wait.hpp`: optional CPU feature detection, monitor arming, and
  bounded waiting. Callers provide the predicate loop and fallback.
- `release_guard.hpp`: refuses the test/benchmark instrumentation macros
  when `CPU_BYTESLICE_ORAM_RELEASE` is defined. Included by every header
  that reads one; deliberately has no include guard.

Keep this folder a dependency leaf; do not include table, rebuild, or engine
policy. Use public lengths for masked memory tails, pass a 0/1 selection bit to
`obliAssignBytes`, and satisfy the alignment contract of `obliLoad512`.
When modifying secret selection, inspect optimized assembly for each supported
compiler: correctness tests alone cannot detect a secret-masked memory access.
`tests/timing/instruction_census.py` fails on any masked memory operation in the
compiled library that `tests/timing/masked_memory_allowlist.txt` does not record
as a public mask, and on any instruction (mnemonic and masking) that
`avx512_constant_time_test` does not time
([tests/timing](../../tests/timing/README.md)).

The operations rely on the x86-64 feature contract documented in the repository
[README](../../README.md#requirements).
