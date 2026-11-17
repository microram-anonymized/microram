#pragma once

// Test-only variable-work oracle for the DFS residual distributor
// (src/oram/rebuild/cpu_byteslice_dfs_residual.hpp), which builds a residual
// pass's range table by obliviously compacting the gathered residual pool
// down a tree of public, nested capacities until each coarse destination
// range (a LEAF) holds its candidates in `pages` 64-slot pages.  This oracle
// computes the same leaves directly: it filters the pool record by record into
// each leaf's pages, in pool order, with scalar code independent of the
// compaction network, the unit list and the buffer reuse.  Its control flow
// and memory addresses depend on the records' tags, so it is NOT oblivious:
// never run it on private data.
#include <algorithm>
#include <cstring>
#include <vector>

#include "src/oram/rebuild/cpu_byteslice_dfs_residual.hpp"

namespace microram {
namespace byteslice {
namespace test_support {

// Fills `leaves` (pages << coarse_bits buckets, stacked) from `pool`.  Returns
// whether every leaf fits min(P, 64 * pages), which by containment is exactly
// when the DFS distributor succeeds.  Leaves at or past `main_buckets` stay
// empty, as they must: no record can target them.
inline bool ExpandedDfsLeaves(TableView pool,
                              const DfsResidualWorkspace::Shape& shape,
                              size_t pages, TableView leaves) {
  const Layout& layout = pool.layout;
  const size_t q = size_t{1} << shape.coarse_bits;
  const size_t cap = std::min(pool.num_buckets * 64, pages * 64);
  std::vector<size_t> count(q, 0);
  std::fill_n(leaves.masks, leaves.num_buckets, 0);
  std::vector<uint8_t> record(layout.EntryBytes());
  bool fits = true;
  for (size_t b = 0; b < pool.num_buckets; ++b) {
    for (size_t lane = 0; lane < 64; ++lane) {
      if (((pool.masks[b] >> lane) & 1) == 0) continue;
      uint64_t leaf = 0;
      for (unsigned i = 0; i < shape.coarse_bits; ++i) {
        const unsigned bit = shape.index_bits + i;
        const uint8_t byte = pool.Bucket(b)[layout.TagLine(bit) * 64 + lane];
        leaf |= uint64_t((byte >> (bit & 7)) & 1) << i;
      }
      const size_t slot = count[leaf]++;
      if (slot >= cap) {
        fits = false;
        continue;
      }
      ReadEntry(pool.Bucket(b), lane, record.data(), record.size());
      const size_t r = (slot / 64) * q + leaf;
      WriteEntry(leaves.Bucket(r), slot % 64, record.data(), record.size());
      leaves.masks[r] |= uint64_t{1} << (slot % 64);
    }
  }
  return fits;
}

}  // namespace test_support
}  // namespace byteslice
}  // namespace microram
