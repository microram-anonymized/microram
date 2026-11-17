#pragma once

// A counting replacement for the global allocator, for the allocation audit
// (benchmarks/oram/cpu_oram_allocation_audit.cpp) and the allocation test
// (tests/oram/cpu_oram_allocation_test.cpp).  Include it from exactly ONE
// translation unit of a binary: it defines operator new and delete.
//
// Every library buffer -- the huge-page arenas included -- comes from
// operator new, so this sees every heap byte an engine takes, both as
// REQUESTED and as GRANTED by glibc (malloc_usable_size, which adds the
// allocator's own rounding and, for a 2 MiB-aligned block, alignment slack
// that is address space rather than resident memory).

#include <execinfo.h>
#include <malloc.h>

#include <atomic>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <new>

// ---------------------------------------------------------------------------
// The counting allocator
// ---------------------------------------------------------------------------
//
// A side table maps each live pointer to its requested size, so a free knows
// what it gives back without a header (a header would move every aligned
// block and change what the allocator grants).  It is a fixed open-addressing
// table with backward-shift deletion, guarded by a spin lock, and it never
// allocates -- the allocator cannot call itself.

namespace audit {

constexpr size_t kSlots = size_t{1} << 20;  // live allocations, at most 3/4
struct Slot {
  uintptr_t ptr;
  size_t bytes;
  uint64_t row;    // the row that allocated it, for the leak report
  uint32_t site;   // into g_sites, or kSites when not captured
  uint32_t harness;  // allocated inside a HarnessScope
};
uint64_t g_row = 0;
Slot g_table[kSlots];
size_t g_used = 0;
std::atomic_flag g_lock = ATOMIC_FLAG_INIT;

struct Counters {
  size_t live_requested = 0;
  size_t live_granted = 0;
  size_t live_blocks = 0;
  size_t peak_requested = 0;
  size_t peak_granted = 0;
  uint64_t allocations = 0;  // since the last Mark
};
Counters g;   // every allocation in the process
Counters gl;  // the library's: g less what a HarnessScope allocated

// HARNESS SCOPE: allocations a thread makes while one is alive are the
// harness's (workload generator, the dataset handed to a constructor), not
// the library's.  Pool and runtime threads allocate outside any scope, so
// their allocations count as library; take the baseline after they start.
thread_local bool t_harness = false;
struct HarnessScope {
  bool previous;
  HarnessScope() : previous(t_harness) { t_harness = true; }
  ~HarnessScope() { t_harness = previous; }
};

struct Guard {
  Guard() {
    while (g_lock.test_and_set(std::memory_order_acquire)) {
    }
  }
  ~Guard() { g_lock.clear(std::memory_order_release); }
};

inline size_t Hash(uintptr_t p) {
  return static_cast<size_t>((p >> 4) * 0x9E3779B97F4A7C15ull) >> (64 - 20);
}

// ALLOCATION SITES (--sites): every allocation's call stack, hashed, with
// the bytes and blocks still live from it.  Captured outside the lock, since
// backtrace() is only safe to call once it has been warmed up (its first call
// loads the unwinder, which allocates).
constexpr int kFrames = 14;
constexpr size_t kSites = 8192;
struct Site {
  uint64_t hash;
  void* frames[kFrames];
  int depth;
  size_t live_bytes, live_blocks, live_granted;
  size_t total_bytes, total_blocks;  // every allocation, freed or not
};
Site g_sites[kSites];
bool g_capture = false;
thread_local bool t_inside = false;

size_t SiteOf(void* const* frames, int depth) {
  uint64_t h = 1469598103934665603ull;
  for (int i = 0; i < depth; ++i) {
    h = (h ^ reinterpret_cast<uintptr_t>(frames[i])) * 1099511628211ull;
  }
  size_t i = static_cast<size_t>(h) & (kSites - 1);
  for (size_t probe = 0; probe < kSites; ++probe, i = (i + 1) & (kSites - 1)) {
    if (g_sites[i].hash == h) return i;
    if (g_sites[i].hash == 0) {
      g_sites[i].hash = h;
      g_sites[i].depth = depth;
      for (int f = 0; f < depth; ++f) g_sites[i].frames[f] = frames[f];
      return i;
    }
  }
  return kSites;  // full: unattributed
}

void Record(void* p, size_t bytes) {
  const size_t granted = malloc_usable_size(p);
  void* frames[kFrames];
  int depth = 0;
  if (g_capture && !t_inside) {
    t_inside = true;
    depth = backtrace(frames, kFrames);
    t_inside = false;
  }
  Guard guard;
  if (++g_used > kSlots / 4 * 3) {
    std::fprintf(stderr, "allocation audit: side table full\n");
    std::abort();
  }
  size_t i = Hash(reinterpret_cast<uintptr_t>(p));
  while (g_table[i].ptr != 0) i = (i + 1) & (kSlots - 1);
  size_t site = kSites;
  if (depth > 0) {
    site = SiteOf(frames, depth);
    if (site < kSites) {
      g_sites[site].live_bytes += bytes;
      g_sites[site].live_granted += granted;
      ++g_sites[site].live_blocks;
      g_sites[site].total_bytes += bytes;
      ++g_sites[site].total_blocks;
    }
  }
  const bool harness = t_harness;
  g_table[i] = Slot{reinterpret_cast<uintptr_t>(p), bytes, g_row,
                    static_cast<uint32_t>(site), harness ? 1u : 0u};
  if (!harness) {
    gl.live_requested += bytes;
    gl.live_granted += granted;
    ++gl.live_blocks;
    ++gl.allocations;
    if (gl.live_requested > gl.peak_requested) gl.peak_requested = gl.live_requested;
    if (gl.live_granted > gl.peak_granted) gl.peak_granted = gl.live_granted;
  }
  g.live_requested += bytes;
  g.live_granted += granted;
  ++g.live_blocks;
  ++g.allocations;
  if (g.live_requested > g.peak_requested) g.peak_requested = g.live_requested;
  if (g.live_granted > g.peak_granted) g.peak_granted = g.live_granted;
}

void Forget(void* p) {
  if (p == nullptr) return;
  const size_t granted = malloc_usable_size(p);
  Guard guard;
  const uintptr_t key = reinterpret_cast<uintptr_t>(p);
  size_t i = Hash(key);
  while (g_table[i].ptr != key) {
    if (g_table[i].ptr == 0) {
      std::fprintf(stderr, "allocation audit: free of an unrecorded block\n");
      std::abort();
    }
    i = (i + 1) & (kSlots - 1);
  }
  if (!g_table[i].harness) {
    gl.live_requested -= g_table[i].bytes;
    gl.live_granted -= granted;
    --gl.live_blocks;
  }
  g.live_requested -= g_table[i].bytes;
  if (g_table[i].site < kSites) {
    g_sites[g_table[i].site].live_bytes -= g_table[i].bytes;
    g_sites[g_table[i].site].live_granted -= granted;
    --g_sites[g_table[i].site].live_blocks;
  }
  g.live_granted -= granted;
  --g.live_blocks;
  --g_used;
  // Backward-shift deletion: pull later members of the probe run into the
  // hole wherever their home slot does not lie strictly after it.
  size_t hole = i;
  for (size_t j = (i + 1) & (kSlots - 1); g_table[j].ptr != 0;
       j = (j + 1) & (kSlots - 1)) {
    const size_t home = Hash(g_table[j].ptr);
    const bool home_after_hole = hole <= j ? (home > hole && home <= j)
                                           : (home > hole || home <= j);
    if (!home_after_hole) {
      g_table[hole] = g_table[j];
      hole = j;
    }
  }
  g_table[hole] = Slot{0, 0, 0, 0, 0};
}

void* Allocate(size_t bytes, size_t align) {
  void* p = nullptr;
  if (align <= alignof(std::max_align_t)) {
    p = std::malloc(bytes == 0 ? 1 : bytes);
  } else if (posix_memalign(&p, align, bytes == 0 ? align : bytes) != 0) {
    p = nullptr;
  }
  if (p == nullptr) throw std::bad_alloc();
  Record(p, bytes);
  return p;
}

void Release(void* p) {
  Forget(p);
  std::free(p);
}

// A checkpoint: what is live now, and the peak since the last Mark.
struct Snapshot {
  size_t live_requested, live_granted, live_blocks;
  size_t peak_requested, peak_granted;
  uint64_t allocations;
};

Snapshot Take() {
  Guard guard;
  return Snapshot{g.live_requested, g.live_granted, g.live_blocks,
                  g.peak_requested, g.peak_granted, g.allocations};
}

// The same, for the library's allocations only (outside every HarnessScope).
Snapshot TakeLibrary() {
  Guard guard;
  return Snapshot{gl.live_requested, gl.live_granted, gl.live_blocks,
                  gl.peak_requested, gl.peak_granted, gl.allocations};
}

// What the row left live, by size: a map that leaked, or a one-time static
// its first use created.  Fixed storage: the allocator lock is held.
struct LiveSize {
  size_t bytes, count;
};
size_t LiveFromRow(uint64_t row, LiveSize* out, size_t max) {
  size_t n = 0;
  Guard guard;
  for (size_t i = 0; i < kSlots; ++i) {
    if (g_table[i].ptr == 0 || g_table[i].row != row) continue;
    size_t k = 0;
    while (k < n && out[k].bytes != g_table[i].bytes) ++k;
    if (k < n) {
      ++out[k].count;
    } else if (n < max) {
      out[n++] = LiveSize{g_table[i].bytes, 1};
    }
  }
  return n;
}

// The live sites, largest first, copied out under the lock.
struct SiteLive {
  size_t bytes, blocks, granted;
  size_t index;  // into g_sites, which CopyLiveBlocks's `site` also names
  int depth;
  void* frames[kFrames];
};
SiteLive g_site_copy[kSites];
// `total`: every allocation the capture saw, freed or not (the access
// phase's transients); otherwise what is still live.
size_t CopyLiveSites(bool total = false) {
  size_t n = 0;
  Guard guard;
  for (size_t i = 0; i < kSites; ++i) {
    const size_t bytes = total ? g_sites[i].total_bytes : g_sites[i].live_bytes;
    if (g_sites[i].hash == 0 || bytes == 0) continue;
    SiteLive& out = g_site_copy[n++];
    out.bytes = bytes;
    out.blocks = total ? g_sites[i].total_blocks : g_sites[i].live_blocks;
    out.granted = g_sites[i].live_granted;
    out.index = i;
    out.depth = g_sites[i].depth;
    for (int f = 0; f < out.depth; ++f) out.frames[f] = g_sites[i].frames[f];
  }
  return n;
}
// Live blocks grouped by (site, requested size): the block-size view that
// lets a caller tell a site's several allocations apart (for example one
// arena per level).  Fixed storage; the allocator lock is held.
struct LiveBlock {
  size_t site, bytes, count, granted;
};
LiveBlock g_block_copy[4096];
size_t CopyLiveBlocks() {
  size_t n = 0;
  Guard guard;
  for (size_t i = 0; i < kSlots; ++i) {
    if (g_table[i].ptr == 0 || g_table[i].site >= kSites) continue;
    size_t k = 0;
    while (k < n && !(g_block_copy[k].site == g_table[i].site &&
                      g_block_copy[k].bytes == g_table[i].bytes)) {
      ++k;
    }
    if (k == n) {
      if (n == sizeof(g_block_copy) / sizeof(g_block_copy[0])) continue;
      g_block_copy[n++] = LiveBlock{g_table[i].site, g_table[i].bytes, 0, 0};
    }
    ++g_block_copy[k].count;
    g_block_copy[k].granted +=
        malloc_usable_size(reinterpret_cast<void*>(g_table[i].ptr));
  }
  return n;
}
void ResetSites() {
  Guard guard;
  std::memset(g_sites, 0, sizeof(g_sites));
  for (size_t i = 0; i < kSlots; ++i) g_table[i].site = static_cast<uint32_t>(kSites);
}

// Starts a phase: the peak restarts from what is live, the count from zero.
void Mark() {
  Guard guard;
  g.peak_requested = g.live_requested;
  g.peak_granted = g.live_granted;
  g.allocations = 0;
  gl.peak_requested = gl.live_requested;
  gl.peak_granted = gl.live_granted;
  gl.allocations = 0;
}

}  // namespace audit

void* operator new(size_t n) { return audit::Allocate(n, 0); }
void* operator new[](size_t n) { return audit::Allocate(n, 0); }
void* operator new(size_t n, std::align_val_t a) {
  return audit::Allocate(n, static_cast<size_t>(a));
}
void* operator new[](size_t n, std::align_val_t a) {
  return audit::Allocate(n, static_cast<size_t>(a));
}
void* operator new(size_t n, const std::nothrow_t&) noexcept {
  try { return audit::Allocate(n, 0); } catch (...) { return nullptr; }
}
void* operator new[](size_t n, const std::nothrow_t&) noexcept {
  try { return audit::Allocate(n, 0); } catch (...) { return nullptr; }
}
void operator delete(void* p) noexcept { audit::Release(p); }
void operator delete[](void* p) noexcept { audit::Release(p); }
void operator delete(void* p, size_t) noexcept { audit::Release(p); }
void operator delete[](void* p, size_t) noexcept { audit::Release(p); }
void operator delete(void* p, std::align_val_t) noexcept { audit::Release(p); }
void operator delete[](void* p, std::align_val_t) noexcept { audit::Release(p); }
void operator delete(void* p, size_t, std::align_val_t) noexcept {
  audit::Release(p);
}
void operator delete[](void* p, size_t, std::align_val_t) noexcept {
  audit::Release(p);
}
