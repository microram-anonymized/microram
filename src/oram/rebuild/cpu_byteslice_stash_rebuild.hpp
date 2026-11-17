#pragma once

// Load-factor-0.5 byte-sliced rebuild, with per-butterfly-level residual
// stashes.
//
// The routing layer on top of cpu_byteslice_rebuild.hpp's primitives.  At
// load 0.25 a butterfly output bucket overflowing 64 entries is a ~2^-65 event
// and is treated as a rebuild failure.  At load 0.5 buckets
// carry 32 real entries on average, the same tail is ~2^-21 per bucket, and
// overflow has to be a supported outcome: every MergeSplit sheds its surplus
// into a residual stash instead of failing, and the hierarchy gives the shed
// entries a second chance later.  Half the arena, in exchange for a cascade
// twice as long and everything below.
//
// The parts, in dependency order:
//
//   cpu_byteslice_residual_stash.hpp    StashLayout, ResidualStash, and why
//                                       the stashes are per butterfly level
//   cpu_byteslice_mergesplit_stash.hpp  the shedding MergeSplit and the fused
//                                       two-level quad
//   cpu_byteslice_butterfly_stash.hpp   grouped and cache-oblivious butterflies
//   cpu_byteslice_radix_stash.hpp       mixed-radix routing, for a table whose
//                                       bucket count is not a power of two
//   cpu_byteslice_meta.hpp              the meta byte line (tombstone,
//                                       residual source) and the dense scatter
//
// CheckOverflow, on the routing entry points, controls the stash-capacity and
// radix-staging checks.  It defaults to off: the capacity table is sized so
// exhausting a stash has probability below 2^-64 per rebuild, and callers that
// want the loss reported rather than assumed instantiate with true.

#include "src/oram/rebuild/cpu_byteslice_butterfly_stash.hpp"
#include "src/oram/rebuild/cpu_byteslice_mergesplit_stash.hpp"
#include "src/oram/table/cpu_byteslice_meta.hpp"
#include "src/oram/rebuild/cpu_byteslice_radix_stash.hpp"
#include "src/oram/rebuild/cpu_byteslice_rebuild.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_stash.hpp"
#include "src/oram/rebuild/cpu_byteslice_stash_capacity_table.hpp"
