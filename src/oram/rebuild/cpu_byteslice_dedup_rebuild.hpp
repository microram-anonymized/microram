#pragma once

// The concurrent rebuild's kernels: cross-source deduplication, the
// incremental chain, and the load-0.5 residual second chance.  The level-arena
// engine reaches them through the phase planners (src/oram/scheduler/).
//
// An engine that removed an entry when an access found it would hold one copy
// of each key, and its rebuilds would never see two.  Probing never writes a
// published table here, and running the rebuild concurrently with probing
// rules out removal anyway; everything in these files follows from that: a rebuild's sources stay probeable for its whole
// duration, so accesses keep inserting fresher copies of keys the rebuild is
// still routing.  Duplicates become real objects, and a kernel has to resolve
// them -- fresher source wins.
//
// The parts, in dependency order:
//
//   cpu_byteslice_dedup_masks.hpp     all-pairs key equality between two
//                                     buckets (VP2INTERSECT and its fallback)
//   cpu_byteslice_dedup_network.hpp   the cross-source MergeSplit, the
//                                     incremental chain, mixed-radix joins
//   cpu_byteslice_residual_range.hpp  pooling load-0.5 residuals into a table
//                                     that can be swept
//   cpu_byteslice_second_chance.hpp   returning a shed entry to its intended
//                                     bucket without revealing which one

#include "src/oram/rebuild/cpu_byteslice_dedup_masks.hpp"
#include "src/oram/rebuild/cpu_byteslice_dedup_network.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_range.hpp"
#include "src/oram/rebuild/cpu_byteslice_second_chance.hpp"
#include "src/oram/rebuild/cpu_byteslice_stash_rebuild.hpp"
