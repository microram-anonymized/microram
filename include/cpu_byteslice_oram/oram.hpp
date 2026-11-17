#pragma once

// The library's public surface.
//
// Two ORAM engines live behind it and they cross over with the value width:
//
//   ByteMap / HierarchicalMap  the hierarchical engine (DESIGN.md), tuned for
//                              small entries -- 8-byte keys, 16-byte values.
//   TreeByteMap / TreeMap      a Path ORAM over a hierarchical position map
//                              (src/oram/tree/DESIGN.md), built for large
//                              entries: about 2 slots per entry against the
//                              hierarchy's 5.5, and no rebuild of the values.
//   HybridByteMap / Map        picks between them from the value width.
//
// `Map` is the one to reach for: at a value of at least
// `kHybridTreeValueThreshold` bytes (96, default_rule.hpp) it is the tree,
// which is smaller there and, with its payload workers, faster; below that
// it is the hierarchy.  Pin the engine with `HierarchicalMap` or `TreeMap`,
// or move the boundary with `HybridOptions::tree_value_threshold`.
//
// THE THRESHOLD ASSUMES A WORKER POLICY.  The hybrid gives its tree one
// byte-column payload worker per started 32 value bytes, uncapped, and 96 is
// the crossover chosen for that policy (default_rule.hpp gives the
// rationale).  Change `tree.payload_max_threads` and the crossover moves.
//
// A CORE BUDGET instead: `Map<K, T> map(capacity, CoreBudget{n})` gives the map
// n cores, its caller included, and configures it exactly as
// `resolve_options` with `Scheme::kAuto` does at that budget -- engine,
// rebuild division and payload workers (default_rule.hpp, configuration.hpp).

#include <cpu_byteslice_oram/byte_map.hpp>
#include <cpu_byteslice_oram/configuration.hpp>  // Map<>'s CoreBudget constructor
#include <cpu_byteslice_oram/tree_oram.hpp>

namespace cpu_byteslice_oram {

// Key and T are stored by object representation. They must be trivially
// copyable, and Key must have unique object representations (no padding
// bytes, no floating-point members: two equal keys with different bytes
// would be different keys); both are checked at compile time.
// Deamortization (background rebuilding) is enabled by default.
// Operations: find / contains / insert_or_assign / write / exchange / erase /
// access (callback update) and their batch forms; see detail::BasicMap in
// byte_map.hpp and the repository README's "Library API".
//
// The engine is chosen from `sizeof(T)` at construction, which is public, so
// the choice leaks nothing.  A plain `Options` still configures it.
template <typename Key, typename T, bool Deamortize = true>
using Map = detail::BasicMap<HybridByteMap<Deamortize>, Key, T>;

// The hierarchical engine, pinned.  This is what `Map` resolves to for every
// value below the threshold.
template <typename Key, typename T, bool Deamortize = true>
using HierarchicalMap = detail::BasicMap<ByteMap<Deamortize>, Key, T>;

}  // namespace cpu_byteslice_oram
