// Check the compiled matchers' memory-access contract, independently of their
// returned masks. A required key line must be read even on empty occupancy or
// an early mismatch; the first line past the key must not be read.  Reading
// every key line whatever the secret occupancy and comparison outcome is what
// makes a probe's memory trace independent of the data; not reading past the
// key keeps the trace exactly the public layout's.  Checked with guard pages
// in a child process, so an optimized build cannot hide a skipped load.
#include "src/oram/table/cpu_byteslice_probe.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

#if defined(__unix__)
#include <cerrno>
#include <csignal>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>
#endif

namespace bs = microram::byteslice;
using bs::test_support::Expect;

#if defined(__unix__)
// Keep the optimized matcher callable with runtime arguments. GCC's noipa
// also prevents caller-specific clones that could omit an unused result.
#define PROBE_TEST_NOINLINE __attribute__((noipa))

extern "C" PROBE_TEST_NOINLINE uint64_t ProbeMemoryGeneric(
    const uint8_t* bucket, uint64_t live, const bs::Layout& layout,
    bs::KeyWords key) {
  return bs::MatchMaskByteSliced(bucket, live, layout, key);
}

extern "C" PROBE_TEST_NOINLINE uint64_t ProbeMemoryCascade(
    const uint8_t* bucket, uint64_t live, const bs::Layout& layout,
    bs::KeyWords key) {
  return bs::MatchMaskByteSlicedTree(bucket, live, layout, key);
}
#undef PROBE_TEST_NOINLINE

using Matcher = uint64_t (*)(const uint8_t*, uint64_t, const bs::Layout&,
                            bs::KeyWords);

void CheckAccess(Matcher matcher, const uint8_t* bucket, size_t width,
                 uint64_t live, bool mismatch, bool must_read_guard) {
  const pid_t child = fork();
  Expect(child >= 0, "could not fork the probe memory test");
  if (child == 0) {
    // A limit of one byte, not zero: the kernel skips a piped core_pattern
    // (apport) only at 1, and a crash handler per expected fault makes the
    // test take minutes.  One byte is below any ELF core, so no file either.
    const rlimit no_core{1, 1};
    if (setrlimit(RLIMIT_CORE, &no_core) != 0) _exit(2);
    // The expected fault must reach waitpid as SIGSEGV, also when a sanitizer
    // runtime has installed its own handler.
    std::signal(SIGSEGV, SIG_DFL);
    alarm(5);
    bs::KeyWords key{0x2A2A2A2A2A2A2A2Aull, 0x2A2A2A2A2A2A2A2Aull};
    if (mismatch) key.w0 ^= 1;
    const uint64_t result = matcher(bucket, live, bs::Layout{width, 1, 1}, key);
    _exit(result == (mismatch ? 0 : live) ? 0 : 1);
  }
  int status = 0;
  pid_t waited;
  do {
    waited = waitpid(child, &status, 0);
  } while (waited < 0 && errno == EINTR);
  Expect(waited == child, "could not wait for the probe memory test");
  const bool passed = must_read_guard
      ? WIFSIGNALED(status) && WTERMSIG(status) == SIGSEGV
      : WIFEXITED(status) && WEXITSTATUS(status) == 0;
  if (!passed) {
    std::fprintf(stderr, "probe memory: width=%zu live=%llu mismatch=%d "
                         "guard_required=%d status=%d\n",
                 width, static_cast<unsigned long long>(live), mismatch,
                 must_read_guard, status);
  }
  Expect(passed, "matcher did not read exactly the required key lines");
}
#endif

int main() {
#if defined(__unix__)
  const long page_size = sysconf(_SC_PAGESIZE);
  Expect(page_size >= 16 * 64 && page_size % 64 == 0,
         "probe memory test needs aligned pages covering all key lines");
  const size_t page = static_cast<size_t>(page_size);
  void* allocation = mmap(nullptr, 2 * page, PROT_READ | PROT_WRITE,
                          MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  Expect(allocation != MAP_FAILED, "could not map probe memory test pages");
  auto* data = static_cast<uint8_t*>(allocation);
  std::memset(data, 0x2A, page);
  Expect(mprotect(data + page, page, PROT_NONE) == 0,
         "could not protect probe memory test page");
  for (Matcher matcher : {ProbeMemoryGeneric, ProbeMemoryCascade}) {
    for (size_t width = 1; width <= 16; ++width) {
      // Place each required line, then the first non-key line, at the guard.
      // All preceding lines are readable and contain matching bytes.
      for (size_t guard_line = 0; guard_line <= width; ++guard_line) {
        const uint8_t* bucket = data + page - guard_line * 64;
        const bool required = guard_line < width;
        CheckAccess(matcher, bucket, width, 0, false, required);
        CheckAccess(matcher, bucket, width, 1, false, required);
        CheckAccess(matcher, bucket, width, 1, true, required);
      }
    }
  }
  Expect(munmap(data, 2 * page) == 0, "could not unmap probe test pages");
  std::puts("probe memory: all key lines read independently of occupancy and match");
#else
  std::puts("probe memory: skipped (requires POSIX protected pages and fork)");
#endif
}
