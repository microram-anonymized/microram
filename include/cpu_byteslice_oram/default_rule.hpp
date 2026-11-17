#pragma once

// THE LIBRARY'S DEFAULT RULE.  Default `Map<>` (`HybridByteMap` with no
// `tree_value_threshold`) and `resolve_options` with `Scheme::kAuto` both call
// `DefaultRule`, so the two cannot drift; tuned constants change here as an
// ordinary code change.  What differs between the two callers is the core
// budget behind the engine they then build: `Map<>` uses its fixed policy
// (`kHybridTreePayloadWorkers`, one worker per started 32 value bytes), the
// resolver the budget it was given.  The rule's inputs are all public (the
// value width and the configured options), so the choice reveals nothing
// about the keys or the access sequence.
//
// The rule (the policy `ResolvedPlan::policy_id()` names):
//   * scheme: the tree when the value is at least `kHybridTreeValueThreshold`
//     (96) bytes, else the incremental hierarchy.  The API mode (scalar or
//     batch) and the payload-worker count are not inputs.  Rationale: the
//     hierarchy rebuilds every value through each of its levels, so its cost
//     grows with the value width; the tree moves a value only along one
//     root-to-leaf path, splits the payload across byte-column workers, and
//     rebuilds only its small position records hierarchically.  The tree's
//     fixed per-access cost (a position-map access plus a whole path) is
//     larger, so the hierarchy wins at small widths.  96 bytes is the
//     crossover chosen from value-width sweeps on the evaluation platforms,
//     scalar and batched, with the payload workers above; it depends on the
//     host and on `tree.payload_max_threads`, so measure it for a deployment
//     and override `HybridOptions::tree_value_threshold` if it differs.
//   * geometry: branching factor 8, two dense prefixes, a 64-entry online
//     stash and the half-fanout prefix, for every capacity and width.  The
//     hierarchy's `Options` fields default to it, and so does the tree's
//     position map.  (Terms: the branching factor B is a non-top level's
//     fanout, how many carries from the level below it absorbs before it
//     carries its merged contents up; the online stash holds the records the
//     most recent accesses wrote; a dense prefix is a group of flushed stash
//     units, scanned in full, that becomes level 1's input, and two may be
//     outstanding; the half-fanout prefix gives the lowest levels fanout B/2.
//     See the vocabulary in byte_map.hpp, src/oram/levelarena/DESIGN.md and
//     include/cpu_byteslice_oram/CONFIGURATION.md.)

#include <cstddef>

namespace cpu_byteslice_oram {

// The value width, in bytes, from which the default rule picks the tree. A
// deployment default chosen by measurement, not a guarantee for every host or
// workload.
inline constexpr size_t kHybridTreeValueThreshold = 96;

// The hierarchy geometry every default-built map uses (fields as above).
struct DefaultGeometry {
  unsigned branching_factor = 8;
  unsigned dense_prefixes = 2;
  size_t online_stash_entries = 64;
  bool half_fanout_prefix = true;
};
inline constexpr DefaultGeometry kDefaultGeometry{};

// What `DefaultRule` returns: the engine and the hierarchy geometry.
struct DefaultChoice {
  bool tree;  // else the incremental hierarchy
  DefaultGeometry geometry;
};

// The cores a default `Map<>` may use, its caller included.  `Map<K, T> map(capacity, CoreBudget{8})` configures the map
// exactly as `resolve_options` with `Scheme::kAuto` at that budget does;
// without it `Map<>` keeps its fixed policy (a two-owner rebuild pool, one
// payload worker per started 32 value bytes, no fixed cap).  The engines
// still never start more threads than the host has physical cores.
struct CoreBudget {
  unsigned cores = 1;
};

// The default engine and geometry for a public value width.
inline constexpr DefaultChoice DefaultRule(size_t value_bytes) {
  return {value_bytes >= kHybridTreeValueThreshold, kDefaultGeometry};
}

}  // namespace cpu_byteslice_oram
