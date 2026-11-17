# Selection without secret-dependent memory access

An oblivious scan must read the same memory even when only one record matches.
The core primitives make the distinction between reading data and selecting data
explicit: memory is loaded according to public addresses and extents, then a
secret condition chooses among values already in registers. This is the
instruction-level foundation for the
[table probes](../oram/table/DESIGN.md) and rebuild kernels.

## Preserve the selection boundary through compilation

A source-level conditional expression does not guarantee a conditional-move
instruction. Likewise, an unconditional vector load followed by a masked blend
may be compiled into a masked memory load. In the latter case, the secret mask
would determine which bytes are accessed. Avoiding an explicit C++ branch is
therefore insufficient for the intended address-trace contract.

[`mov_intrinsics.hpp`](mov_intrinsics.hpp) provides scalar selection with
`CMOV8` and `obliSelectU64`, which explicitly emit a register conditional move.
Neither primitive hides a secret-dependent address computed by its caller.
The library builds only with GCC: these primitives rely on GNU inline-asm
register constraints, and the census and timing test check only the code GCC
emits.

`obliPin512` presents a vector to the compiler as a register input and output of
an opaque assembly boundary. `obliLoad512` uses that boundary after an unmasked
load, forcing the entire line to be read before later selection. The boundary
adds no machine instruction. Secret-masked consumers still need register-only
operands, including when the compiler spills this value.

A pin guarantees that a value was once whole in a register, not that a later
consumer reads it from one. The compiler may spill the pinned value and fold
the reload into the consumer's memory operand. It also folds a caller's
`secret & compare(x, y)` into one compare with the secret as its write mask,
taking whichever operand it holds in memory: a bucket line, a broadcast
constant, or a spill slot.
Whether it happens depends on the caller a function is inlined into, the
optimization level and the target, so a clean build says nothing about the
next one. The register-only forms (`obliCmpEqMask8/32/64`, `obliCmpGtU8Mask`,
`obliCmpGeU8Mask`, `obliTestMask8/32/64`, `obliTestNMask8/32/64`,
`obliMaskMov8/32/64`, `obliMaskExpand8`) write the instruction itself as an
assembly statement whose vector operands are constrained to registers. A
spilled value is then reloaded whole by an unmasked load, and the compare is
opaque, so the caller's AND stays an AND. Library code writes every compare
and test through them, and uses the masked moves and expand wherever a secret
mask selects. The census in [tests/timing](../../tests/timing/README.md)
lists every masked memory operation in the compiled library and fails on one
that is not a reviewed public mask. It is the check for the masked moves that
still rely on pins.

`obliAssignBytes` applies the same rule to an arbitrary public length. It loads
both the old and candidate values, selects in registers, and writes the result.
For `n` bytes it performs `ceil(n/64)` vector iterations and logically reads
`2n` bytes and writes `n` bytes, regardless of the secret selection bit. Tail
masks depend only on `n` and may control memory operations. The selection mask
depends on the secret and may control only register operations. These byte
counts describe the algorithm, not cache-line transfers or instruction timing.

The security argument assumes the supported instructions do not expose the
selection through the observer model in the
[system design](../../DESIGN.md#security-boundary-and-limitations). Compiler
barriers preserve an address pattern; they do not establish protection against
every physical or speculative side channel. Whether a secret index, mask, count
or data operand changes an instruction's timing is a property of the host, and
[the timing test](../../tests/timing/README.md) measures it there for every
data-processing instruction the library emits, in one operand form of each.

## Waiting on public progress

[`monitor_wait.hpp`](monitor_wait.hpp) is a separate core service for workers
waiting on sequence words. A worker arms a monitored cache line, rechecks the
sequence, then waits and retries. Rechecking after arming closes the race in
which a publisher stores between the worker's first observation and its sleep.
Spurious returns and bounded waits require a loop around the predicate.

The optional monitor instructions let a publisher's ordinary store wake a
waiting core without an explicit system-call wake on that path. Unsupported
machines use the caller's fallback. This changes how a worker waits, not how
much ORAM routing work it performs. Acquire/release synchronization and the
predicate remain the caller's responsibility; the monitor instruction is not
a substitute for either.

For implementation entry points and checks, see [README.md](README.md).
Revise this explanation directly under the
[maintenance rule](../../DESIGN.md#documentation-maintenance).
