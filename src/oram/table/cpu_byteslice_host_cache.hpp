#pragma once

// WHAT "THIS HOST'S LAST-LEVEL CACHE" MEANS, in one place (and its L2, below).
//
// One decision reads the L3 figure, and it is a placement decision rather than
// a correctness one: the level-arena engine's automatic near/far worker
// boundary (`AutoNearMaxLevel` for `kNearMaxLevelAuto`; see levelarena
// DESIGN.md, "Batches and near/far placement").  Levels small enough to stay
// cache-resident are rebuilt near the requester, which shares that cache;
// larger levels stream through DRAM anyway and can be rebuilt on a far cache
// domain.  "The largest level whose full table is under half the L3" is a
// rule about a machine, so it is spelled here once.
//
// glibc exposes the cache sizes through sysconf.  Where the L3 reads zero the
// L2 is returned instead, and where both do (some containers, and possibly a
// confidential guest that hides its topology) the fallback is 32 MiB, the L3
// of one AMD Zen core complex (CCD).  Only the automatic boundary reads this, so a wrong answer moves a
// knob's default and nothing else; resolved benchmark configurations pin the
// boundary and never take the automatic one.

#include <cstddef>

#if defined(__unix__) || defined(__APPLE__)
#include <unistd.h>
#endif

namespace microram {
namespace byteslice {

inline size_t HostLastLevelCacheBytes() {
#if defined(_SC_LEVEL3_CACHE_SIZE)
  const long l3 = ::sysconf(_SC_LEVEL3_CACHE_SIZE);
  if (l3 > 0) return static_cast<size_t>(l3);
#endif
#if defined(_SC_LEVEL2_CACHE_SIZE)
  const long l2 = ::sysconf(_SC_LEVEL2_CACHE_SIZE);
  if (l2 > 0) return static_cast<size_t>(l2);
#endif
  return size_t{32} << 20;
}

// ONE CORE'S L2, for the streaming-store threshold (StreamStoreMinBytes in
// cpu_byteslice_routing_map.hpp): 1 MiB on Zen 5, 2 MiB on Granite Rapids.
// Performance only, like the L3 above; 1 MiB, the size the threshold was
// calibrated for, when the host cannot say.
inline size_t HostLevel2CacheBytes() {
#if defined(_SC_LEVEL2_CACHE_SIZE)
  const long l2 = ::sysconf(_SC_LEVEL2_CACHE_SIZE);
  if (l2 > 0) return static_cast<size_t>(l2);
#endif
  return size_t{1} << 20;
}

}  // namespace byteslice
}  // namespace microram
