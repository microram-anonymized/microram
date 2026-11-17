# Working on byte-sliced tables

This directory owns shared layouts and online primitives. Read
[DESIGN.md](DESIGN.md) for representation, probing invariants, and analytical
costs. Most callers should include an engine or rebuild umbrella; include a
header here directly when the primitive itself is the intended dependency.

| Headers | Engineering responsibility |
|---|---|
| `cpu_byteslice_layout.hpp`, `cpu_byteslice_stored_key.hpp` | Table/view storage, field offsets, key widths, and shared encoding |
| `cpu_byteslice_tags.hpp`, `cpu_byteslice_routing_map.hpp` | Tag generation, nonce allocation, routing maps, and tag-width planning |
| `cpu_byteslice_probe.hpp`, `cpu_byteslice_probe_addresses.hpp`, `cpu_byteslice_probe_plan.hpp` | Bucket kernels, address resolution, and probe plans |
| `cpu_byteslice_meta.hpp` | Metadata bits, dense scatter, and stash insertion |
| `cpu_byteslice_key_intersect.hpp`, `cpu_byteslice_dense_match.hpp` | Intersection primitives and direct-slot matching |
| `cpu_byteslice_batch_config.hpp`, `cpu_byteslice_batch_probe.hpp` | Batch configuration, deduplication, selection, and forwarding |
| `cpu_byteslice_batch_layout.hpp`, `cpu_byteslice_parallel_batch.hpp` | Result layouts and whole-job tile metadata |
| `cpu_byteslice_host_cache.hpp`, `cpu_byteslice_host_cores.hpp` | Shared host-cache and physical-core discovery |

Keep geometry and lifetime policy in the engines. When changing a layout,
check all four `Layout` fields, tag offsets, metadata placement, and any views
that share the allocation. Exercise actual key widths 1–8 and 16. Preserve the
exact duplicate-preserving fallback when modifying direct-slot matching.

Relevant tests are
[batch matching](../../../tests/oram/cpu_byteslice_batch_match_test.cpp),
[batch probing](../../../tests/oram/cpu_byteslice_batch_probe_test.cpp), and
[batch layouts](../../../tests/oram/cpu_byteslice_batch_layout_test.cpp).
The [probe memory test](../../../tests/oram/cpu_byteslice_probe_memory_test.cpp)
uses protected pages on POSIX hosts to check compiled key-line accesses;
run its optimized variant as well as the checked one. The
[probe plan test](../../../tests/oram/cpu_byteslice_probe_plan_test.cpp)
checks window validation against exhaustive interval geometry.
Run both engine suites for shared probe or metadata changes. Include repeated
keys across tile boundaries, inactive slots with stale bytes, narrow keys,
wide stored hashes, and both result layouts. Probe-audit builds check engine
uniqueness invariants but are not production oblivious execution.

Use the [repository build instructions](../../../README.md) for configuration
and test execution.
Edit design explanations in place under the
[documentation maintenance rule](../../../DESIGN.md#documentation-maintenance).
