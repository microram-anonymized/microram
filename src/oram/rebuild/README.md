# Working on rebuild kernels

This directory contains routing, deduplication, and residual recovery kernels.
Read [DESIGN.md](DESIGN.md) for the algorithms and their security and cost
arguments. Worker and publication policy belongs to the engines; planning and
dispatch belong to [scheduler](../scheduler/README.md).

| Umbrella | Intended use |
|---|---|
| `cpu_byteslice_rebuild.hpp` | Layout, basic MergeSplit, tags, maps, and probes |
| `cpu_byteslice_stash_rebuild.hpp` | Routing with per-level residual stashes |
| `cpu_byteslice_dedup_rebuild.hpp` | Cross-source deduplication and second chance |

The `mergesplit`, `butterfly_stash`, and `radix_stash` headers implement routing.
`residual_stash` owns storage, while `residual_range` and `second_chance` own
recovery. `dedup_masks` and `dedup_network` handle comparisons and routing
integration; `dedup_network` also defines the binary source-block
decomposition a merge's inputs follow.
`initialization` defines initial-load records, policies, and public plans that
feed the existing kernels.

`dfs_residual` is the public-capacity DFS distributor that builds every
distributing residual pass's range table (level one's completed A leaves,
higher separated sources' A leaves, and the top's preparation): stable
compaction into public padded children, retaining the gathered pool and
pending siblings. Its consumers are the existing fused page-by-page offers
and final-shed deduplication of `second_chance`. See
[the design](DESIGN.md#public-capacity-dfs-distribution),
[partitioner tests](../../../tests/oram/cpu_byteslice_dfs_residual_test.cpp) /
[consumer tests](../../../tests/oram/cpu_byteslice_dfs_second_chance_test.cpp),
and the [bound-certification report](../../../analysis/bound_certification/README.md)
for the capacity scope.

Do not hand-edit `cpu_byteslice_stash_capacity_table.hpp`: regenerate it with
[analysis/gen_stash_capacity_table.cpp](../../../analysis/gen_stash_capacity_table.cpp).
A capacity or geometry change needs corresponding overflow-bound review.
Keep checked execution available when altering stash or deduplication logic.

Compare occupied output bytes and masks against reference execution; dummy
bytes need not agree. Retain coverage for empty and dirty scratch, narrow and
wide keys, tag-pruning boundaries, all supported radix shapes, tombstones,
equal-rank sources, and direct/packed/stacked residual geometry. Relevant tests:

- [Stash routing](../../../tests/oram/cpu_byteslice_stash_rebuild_test.cpp)
  and [deduplication](../../../tests/oram/cpu_byteslice_dedup_rebuild_test.cpp).
- [Base-B absorption](../../../tests/oram/cpu_byteslice_baseb_absorb_test.cpp).
- [Residual builds](../../../tests/oram/cpu_byteslice_residual_build_test.cpp)
  and [overflow](../../../tests/oram/cpu_byteslice_residual_overflow_test.cpp).
- [Pruned fresher copies](../../../tests/oram/cpu_byteslice_fresher_copy_test.cpp).

Use the [repository build instructions](../../../README.md) for configuration
and test execution.
Edit design explanations in place under the
[documentation maintenance rule](../../../DESIGN.md#documentation-maintenance).
