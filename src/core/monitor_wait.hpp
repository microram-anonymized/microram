#pragma once

// User-mode monitor-and-wait: a thread arms one cache line and sleeps until a
// store lands on it or a timeout expires, in a light C-state, with no syscall
// and no IPI.
//
//   AMD    MONITORX / MWAITX   (Excavator, every Zen; CPUID 8000_0001h ECX[29])
//   Intel  UMONITOR / UMWAIT   (WAITPKG: Tremont, Alder Lake, Sapphire Rapids
//                               and later; CPUID 7.0 ECX[5])
//
// WHY.  Every worker pool in this project waits for a sequence word the way
// this file's callers do: spin for a window, then park on a futex.  The park
// is what makes the wake dear -- a syscall and an inter-processor interrupt
// on every wake, which a request pays whenever requests arrive more slowly
// than the spin window and the workers have gone to sleep -- and the spin is
// what makes idling dear.  A monitored wait is the third option: the waiting
// core halts, and the publisher's ordinary store to the word is the wake, so
// nothing is paid on the publishing side and the wake latency is the core's
// shallow-sleep exit.
//
// AVAILABILITY.  Many hypervisors hide both CPUID bits and fault the
// instructions (#UD), so the detection below is the whole gate, and the
// fallback (spin, then park) is the path most virtualized hosts take.  The
// instructions' wake latency, power, and interaction with SMT are properties
// of the host.  Everything that consumes this header therefore treats it as
// an opt-in whose absence changes only how a worker waits, never what it
// computes or which memory the ORAM touches.
//
// Semantics the callers rely on.  MONITORX arms the line containing the
// address in RAX (RCX, RDX are extension and hint words, zero).  MWAITX waits
// for a store to the armed line, an interrupt, or -- with ECX[1] set -- EBX
// TSC ticks, whichever is first; EAX[7:4] is the C-state hint (0 is C1, 0xF is
// C0).  UMONITOR takes the address in a register; UMWAIT takes the deadline as
// an ABSOLUTE TSC value in EDX:EAX and the state in the register's bit 0 (0 is
// C0.2, the deeper), and the OS may cap the wait (IA32_UMWAIT_CONTROL), which
// is why every wait here is a loop that re-checks its word.  Both families
// wake spuriously; both must be re-armed before every sleep.

#include <cpuid.h>
#include <x86intrin.h>

#include <cassert>
#include <cstdint>

namespace microram {
namespace core {

// The same definition as in mov_intrinsics.hpp (see there).
#undef INLINE
#define INLINE inline __attribute__((always_inline))

enum class MonitorWaitKind : unsigned {
  kNone = 0,    // neither family, or not asked for: the caller parks
  kMwaitx = 1,  // AMD MONITORX / MWAITX
  kUmwait = 2,  // Intel UMONITOR / UMWAIT
};

inline const char* MonitorWaitKindName(MonitorWaitKind k) {
  switch (k) {
    case MonitorWaitKind::kMwaitx: return "mwaitx";
    case MonitorWaitKind::kUmwait: return "umwait";
    default: return "none";
  }
}

// What this CPU offers.  A hypervisor that hides the bit also faults the
// instruction, so the bit is the whole of the contract.
inline MonitorWaitKind DetectMonitorWait() {
  unsigned a = 0, b = 0, c = 0, d = 0;
  if (__get_cpuid(0x80000001u, &a, &b, &c, &d) && ((c >> 29) & 1u)) {
    return MonitorWaitKind::kMwaitx;
  }
  if (__get_cpuid_count(7u, 0u, &a, &b, &c, &d) && ((c >> 5) & 1u)) {
    return MonitorWaitKind::kUmwait;
  }
  return MonitorWaitKind::kNone;
}

// TSC ticks per microsecond, as an UPPER bound used to turn a microsecond
// timeout into ticks without calibrating: no shipping x86 TSC runs above
// 6 GHz, so a timeout expressed through this is never shorter than asked
// for.  The timeout only bounds how late a sleeper notices something that is
// not a store to its line (a stop request), so an over-estimate costs nothing
// on the path that matters.
inline constexpr uint64_t kTscTicksPerMicroBound = 6000;

// Arm the line holding `p`.  Must precede every MonitorWaitSleep.
INLINE void MonitorWaitArm(MonitorWaitKind kind, const void* p) {
  if (kind == MonitorWaitKind::kMwaitx) {
    asm volatile("monitorx" : : "a"(p), "c"(0u), "d"(0u) : "memory");
  } else if (kind == MonitorWaitKind::kUmwait) {
    asm volatile("umonitor %0" : : "r"(p) : "memory");
  }
}

// Sleep until a store hits the armed line or `timeout_ticks` TSC ticks pass.
// Returns on spurious wakes too; the caller re-checks and re-arms.
// PRECONDITION: timeout_ticks > 0.  MWAITX takes a zero timer value as no
// timer at all, so a zero would wait for a store or an interrupt only, and
// the callers rely on the timeout to notice a stop request on another line.
INLINE void MonitorWaitSleep(MonitorWaitKind kind, uint64_t timeout_ticks) {
  assert(timeout_ticks > 0);
  if (kind == MonitorWaitKind::kMwaitx) {
    const unsigned ticks =
        timeout_ticks > 0xFFFFFFFFull ? 0xFFFFFFFFu
                                      : static_cast<unsigned>(timeout_ticks);
    // EAX: C1 hint.  ECX bit 1: the timer in EBX is armed.
    asm volatile("mwaitx" : : "a"(0u), "c"(2u), "b"(ticks) : "memory");
  } else if (kind == MonitorWaitKind::kUmwait) {
    const uint64_t deadline = __rdtsc() + timeout_ticks;
    const unsigned state = 0u;  // C0.2
    asm volatile("umwait %0"
                 :
                 : "r"(state), "a"(static_cast<unsigned>(deadline)),
                   "d"(static_cast<unsigned>(deadline >> 32))
                 : "cc", "memory");
  }
}

}  // namespace core
}  // namespace microram
