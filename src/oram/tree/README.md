# Tree ORAM engineering guide

Read [DESIGN.md](DESIGN.md) for the construction, the default rule, layouts,
costs, and security boundary. Public users include
[`<cpu_byteslice_oram/tree_oram.hpp>`](../../../include/cpu_byteslice_oram/tree_oram.hpp),
which exposes `TreeByteMap` and `TreeMap`. Internal code lives in
`microram::tree`.

## Where to make a change

| File | Responsibility |
|---|---|
| [cpu_tree_layout.hpp](cpu_tree_layout.hpp) | Bucket and path bounds, the default rule (`DefaultFold`, `DefaultStashRegisters`), `TreeShape` and `TreeGeometry::ForCapacity`, checked sizes and geometry validation, storage allocation, path addressing, the plane split (`SliceLayout`) and the plane reassembly oracle |
| [cpu_tree_transpose.hpp](cpu_tree_transpose.hpp) | The four-slot transposition network pruned to the path length, path chunk loads and stores, the path-length dispatch, and the scalar reference transform |
| [cpu_tree_read_path_eviction.hpp](cpu_tree_read_path_eviction.hpp) | The planner `PlanReadPath<A, B>`, its byte-sliced field helpers, and the scalar reference `ReferenceReadPathEvict` |
| [cpu_tree_read_path_oram.hpp](cpu_tree_read_path_oram.hpp) | The engine: `TreeKnobs`, the payload worker count, the configuration boundary, the per-line routing kernel, `ReadPathPlane` and `CpuReadPathOram` |
| [cpu_tree_payload_workers.hpp](cpu_tree_payload_workers.hpp) | Worker ownership, two-step job publication, value readiness and completion, failure retirement |
| [cpu_tree_position_map.hpp](cpu_tree_position_map.hpp) | Position encoding, hierarchical backend, non-oblivious test backend |
| [cpu_tree_map.hpp](cpu_tree_map.hpp) | Map composition, remapping, alias handling, batches, failed-instance latch |

The stash simulator that the stash measurement runs,
[cpu_tree_stash_sim.hpp](../../../benchmarks/oram/cpu_tree_stash_sim.hpp), is
a second implementation of the planner's rule over metadata. It lives with the
benchmarks but changes with the planner.

## Change checklist

- Geometry changes go through `ForCapacity`, `ValidateGeometry` and
  `ValidateReadPathConfiguration`. Keep the stash lanes in the load, the
  rule's fold and stash width chosen per candidate depth, the write-back of
  both into the knobs in `TreeByteMap`, and the resolver's plan in agreement
  with the constructed map. Check the default-rule table in the transpose
  test, folded-slot accounting, size overflow, and the position map's
  encoded width. Use `arena_bytes()` for allocation accounting rather than
  deriving bytes from `slots()`.
- A change to the default rule, the load or the stash width needs a stash
  measurement of every fold and `A` it produces (DESIGN.md, "Stash size"),
  and updates `DefaultFold` / `DefaultStashRegisters` and both DESIGN.md
  sections together.
- Planner changes must preserve the scalar reference's slot-for-slot result
  and the rule's properties: no path entry dropped, path entries only move
  toward the leaf, path register 1 takes nothing from register 0, an unplaced
  stash entry keeps its lane, the landing lane is the lowest free one, uid
  zero is an ordinary uid, and overflow (`64A - 1` kept entries) is decided
  before any store. Change the simulator's plan in the same change. Audit
  optimized disassembly for branches or memory operands influenced by secret
  masks; a C++ ternary is not sufficient evidence of constant-time selection.
- Kernel changes must cover one- and two-register paths, `A = 3` and `4`,
  exact and partial final chunks, both transposition directions, and the
  staged (gather-first) and ordinary payload passes. Plane byte-line indices
  remain global entry offsets.
- Worker changes must preserve the distinction between value readiness and
  job completion. Wait for every worker's output writes before returning or
  throwing. Publish a cancelled job when the plan fails. Call `Drain()` or
  `DrainTree()` before inspecting storage outside normal map operations.
  Copy the caller's input into the job before publication.
- Map changes must retain one position-map operation per request, random
  paths on misses, unconditional PRF draws, overlapping exchange-buffer
  support, ordered repeated-key batches, and failure latching after an access
  or background-work drain throws.

## Validation

From the repository root, configure and build the standard test targets, then
run the tree suite:

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DCPU_BYTESLICE_ORAM_BUILD=tests
cmake --build build -j
ctest --test-dir build -R cpu_tree --output-on-failure
```

| Test | What it covers |
|---|---|
| [cpu_tree_transpose_test](../../../tests/oram/cpu_tree_transpose_test.cpp) | The network against its scalar reference and its own inverse, bit-reversed addressing, checked size arithmetic, geometry, and the default rule's fold, `A` and path per capacity |
| [cpu_tree_read_path_eviction_test](../../../tests/oram/cpu_tree_read_path_eviction_test.cpp) | The planner against the scalar reference on random working sets in every built shape, the rule's properties, and the field helpers |
| [cpu_tree_read_path_oram_test](../../../tests/oram/cpu_tree_read_path_oram_test.cpp) | The engine against a model map and against the stash simulator slot for slot; threaded planes against a synchronous twin; the storage invariant; overflow writes nothing; the configuration boundary; worker lifetime and failures; misses read distinct paths; bucket offsets |
| [cpu_tree_map_test](../../../tests/oram/cpu_tree_map_test.cpp) | The public map over the real position map: uid choice, exchange aliasing, the hybrid and its 96-byte threshold, payload worker counts, argument validation |
| [cpu_tree_batch_test](../../../tests/oram/cpu_tree_batch_test.cpp), [cpu_tree_position_batch_test](../../../tests/oram/cpu_tree_position_batch_test.cpp) | Batch request order and fault injection at the composition boundary; batched position-map exchanges against scalar ones |

`cpu_byteslice_configuration_test` checks the resolver's tree plans, and the
[instruction census](../../../tests/timing/README.md) checks the emitted code.
Passing the simulator comparison does not establish a rare-event probability.

Changes to stash parameters or the eviction rule need both structural checks
and measurements for the exact geometry, load and stash width being proposed.
Worker changes need lifetime and ownership checks, including a failed worker
while another still holds a caller's output buffer.

Update the affected sections of [DESIGN.md](DESIGN.md) and this guide when
behavior changes. Follow the [documentation maintenance rule](../../../DESIGN.md#documentation-maintenance)
by rewriting the affected explanation.
