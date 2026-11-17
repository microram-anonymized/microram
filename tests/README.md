# Tests

Every `tests/oram/*.cpp` file is one CTest binary, built twice: as a release
test and as an assertion-enabled `_checked` test. Each file opens with a
comment stating the property it checks. The groups below are a reading guide;
see the [root README](../README.md#build) for how to build and run them.

Correctness tests check functional behaviour and the invariants the security
argument relies on (fixed probe schedules, bounded failures that are reported,
no allocation on the access path). They do not by themselves establish
obliviousness; the [timing tests](timing/README.md) and the
[certification](../analysis/bound_certification/README.md) cover the
side-channel and capacity-failure arguments.

## tests/oram

| Area | Tests |
|---|---|
| Public maps and configuration | `cpu_byteslice_oram_map_test` (hierarchical `ByteMap`/`Map`, both storage modes, against `std::map`), `cpu_byteslice_arena_map_test`, `cpu_byteslice_access_test` (callback and mixed-batch APIs on every backend), `cpu_byteslice_configuration_test` (resolver), `cpu_byteslice_large_flush_test`, `cpu_byteslice_release_guard_test` |
| Table, matching and probes | `cpu_byteslice_batch_match_test`, `cpu_byteslice_batch_layout_test`, `cpu_byteslice_batch_probe_test`, `cpu_byteslice_parallel_batch_test`, `cpu_byteslice_probe_plan_test`, `cpu_byteslice_routing_tag_test`, `cpu_byteslice_key_derivation_test` |
| Memory-access contracts | `cpu_byteslice_probe_memory_test`, `cpu_byteslice_value_plane_memory_test` (required loads happen on hits, misses and empty buckets alike), `cpu_oram_allocation_test` |
| Rebuild kernels | `cpu_byteslice_stash_rebuild_test`, `cpu_byteslice_dedup_rebuild_test`, `cpu_byteslice_dedup_nest_equivalence_test`, `cpu_byteslice_baseb_absorb_test`, `cpu_byteslice_dense_select_test`, `cpu_byteslice_fresher_copy_test`, `cpu_byteslice_radix_capacity_test`, `cpu_byteslice_slot512_kernel_test` |
| Residual recovery | `cpu_byteslice_dfs_residual_test`, `cpu_byteslice_dfs_second_chance_test`, `cpu_byteslice_residual_build_test`, `cpu_byteslice_residual_occupancy_test`, `cpu_byteslice_residual_overflow_test`, `cpu_byteslice_top_resolution_test` |
| Level-arena engine | `cpu_byteslice_level_arena_test` (geometry, slots, families), `_merge_test`, `_job_test`, `_top_test`, `_engine_test`, `_init_test`, `_synchronous_test`, `_capacity_test`, `_certification_test`, `_batch_test`, `_batch_workers_test`, `cpu_byteslice_value_workers_test` |
| Concurrency and lifetime | `cpu_byteslice_level_arena_threads_test`, `_lifecycle_test`, `_lifetime_test`, `_placement_test`, `_rebuild_params_test`, `cpu_byteslice_multi_ccd_batch_test`, `cpu_byteslice_routing_budget_test`, `cpu_byteslice_routing_lifetime_test` |
| Tree ORAM | `cpu_tree_read_path_oram_test` (engine against a model map), `cpu_tree_read_path_eviction_test`, `cpu_tree_transpose_test`, `cpu_tree_position_batch_test`, `cpu_tree_batch_test`, `cpu_tree_map_test` |
| Benchmark harness adapters | `cpu_byteslice_trial_adapter_test`, `cpu_byteslice_open_loop_adapter_test` |

Names written `_x_test` abbreviate `cpu_byteslice_level_arena_x_test`.
Shared helpers: `cpu_byteslice_test_support.hpp`,
`cpu_byteslice_rebuild_test_support.hpp`,
`cpu_byteslice_level_arena_test_support.hpp` and
`cpu_byteslice_dfs_reference.hpp` (a scalar reference for the DFS distributor).

## Other directories

- [timing](timing/README.md): the instruction census and operand-timing
  measurements behind the constant-time claims; run on an idle host of the
  target microarchitecture.
- `release_guard`: checks that `CPU_BYTESLICE_ORAM_RELEASE` rejects every
  test-instrumentation macro.
- `analysis`: unit and command-line tests for the benchmark harness
  (`analysis/oram_bench`) and the analysis scripts, on synthetic fixtures.
  Run them with `python3 -m unittest discover -s tests/analysis -v`.
