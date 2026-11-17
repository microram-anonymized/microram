#pragma once

// CPU-only byte-sliced bucket-hash rebuild (AVX-512 VBMI2 + AES-NI/VAES): the
// umbrella that pulls in the layout and the two phases a rebuild is made of.
//
// A hierarchical-ORAM level is a bucket hash table of 64-entry buckets run at a
// target load of 0.5, rebuilt on one core (or a thread pool).  Rebuilding it is
// two phases:
//
//   1. TAG.  Give every entry tag = AES-128(secret key, key || nonce), written
//      into the entry's own tag byte lines so the tag travels with the entry.
//      A fresh nonce per rebuild is what stops a bucket index from carrying
//      information across rebuilds.  (cpu_byteslice_tags.hpp; the base-B index
//      map that turns a tag into a bucket of a non-power-of-two table is in
//      cpu_byteslice_routing_map.hpp.)
//
//   2. ROUTE.  log2(num_buckets) butterfly levels of MergeSplits, level l
//      pairing buckets (i, i + 2^l) on tag bit l.  LSB-first routing leaves
//      every entry in bucket (tag mod num_buckets), so the routed array IS the
//      hash table -- there is no separate placement pass.
//      (cpu_byteslice_mergesplit.hpp for the pair primitive;
//      cpu_byteslice_stash_rebuild.hpp for the butterflies that compose it,
//      which are the only ones the library has -- at load 0.5 every level
//      needs a residual stash to shed into.)
//
// Everything rests on the byte-sliced layout: a bucket stores byte b of all 64
// entries as one 64-byte line, so one AVX-512 register holds one byte of a
// whole bucket and any permutation of the 64 entries costs one instruction per
// line.  cpu_byteslice_layout.hpp has the layout and the types; it is worth
// reading first.
//
// The parts live in:
//
//   cpu_byteslice_layout.hpp       layout, KeyWords, Table/TableView, accessors
//   cpu_byteslice_mergesplit.hpp   MergeSplitPair, BuildMergeIndex, plans
//   cpu_byteslice_tags.hpp         key gather transpose, AES-128 tag batches
//   cpu_byteslice_routing_map.hpp  base-B index maps, re-tag, nonce allocation
//   cpu_byteslice_probe.hpp        oblivious lookup, single and batched
//
// The routing itself -- the shedding MergeSplit, the butterflies, the
// mixed-radix pass and the residual stashes -- is in
// cpu_byteslice_stash_rebuild.hpp, which includes this header.
//
// Requires x86-64 with AVX-512 F/BW/VBMI2 + BMI2 + AES-NI; VAES with 512-bit
// vectors is used when present (Ice Lake+ / Zen 4+).  GCC gets everything from
// -march=native (see CMakeLists.txt).

#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/rebuild/cpu_byteslice_mergesplit.hpp"
#include "src/oram/table/cpu_byteslice_probe.hpp"
#include "src/oram/table/cpu_byteslice_routing_map.hpp"
#include "src/oram/table/cpu_byteslice_tags.hpp"
