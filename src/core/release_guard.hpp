// RELEASE-BUILD GUARD.  Deliberately no #pragma once: every header that reads
// one of the instrumentation macros below includes this, and it has to be
// re-evaluated at each of those includes -- a translation unit that defines
// an instrumentation macro AFTER its first library include still reaches the
// header that acts on it, so a check run once at the top would miss it.
//
// CPU_BYTESLICE_ORAM_RELEASE is the consumer's declaration that this build is
// a production one.  The macros refused here exist for tests and benchmarks
// only: each compiles in a probe-address log, a thread pause hook, an
// occupancy observer, comparison counters, per-access phase clocks or a
// diagnostic constructor that a production access path must not carry.
// Defining one of them together with the release macro is a build error
// rather than a silent downgrade.
//
// The macros change class layouts and inline function bodies, so every
// translation unit of one program must agree on them: defining one in some
// translation units and not in others breaks the one-definition rule, and
// nothing detects that at link time.

#if defined(CPU_BYTESLICE_ORAM_RELEASE)
#if defined(MICRORAM_BYTESLICE_PROBE_AUDIT)
#error "CPU_BYTESLICE_ORAM_RELEASE: MICRORAM_BYTESLICE_PROBE_AUDIT is a test instrumentation macro (probe-address log) and may not be defined in a release build"
#endif
#if defined(MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE)
#error "CPU_BYTESLICE_ORAM_RELEASE: MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE is a test instrumentation macro (thread pause hooks) and may not be defined in a release build"
#endif
#if defined(MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER)
#error "CPU_BYTESLICE_ORAM_RELEASE: MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER is a diagnostic macro whose hook receives secret-dependent stash, range and tier occupancies; it may not be defined in a release build"
#endif
#if defined(MICRORAM_BYTESLICE_COMPARE_COUNT)
#error "CPU_BYTESLICE_ORAM_RELEASE: MICRORAM_BYTESLICE_COMPARE_COUNT is a benchmark instrumentation macro (merge comparison counters) and may not be defined in a release build"
#endif
#if defined(MICRORAM_TREE_PHASE_TIMER)
#error "CPU_BYTESLICE_ORAM_RELEASE: MICRORAM_TREE_PHASE_TIMER is a benchmark instrumentation macro (per-access phase clocks) and may not be defined in a release build"
#endif
#if defined(MICRORAM_BYTESLICE_BATCH_PROFILE)
#error "CPU_BYTESLICE_ORAM_RELEASE: MICRORAM_BYTESLICE_BATCH_PROFILE is a benchmark instrumentation macro (diagnostic ByteMap constructor) and may not be defined in a release build"
#endif
#endif
