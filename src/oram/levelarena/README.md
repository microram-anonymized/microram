# Working on the arena engine

Read [DESIGN.md](DESIGN.md) for the storage derivation, carry algorithm, publication protocol and security limits. Keep design explanations there and edit them in place when behavior changes; follow the [documentation maintenance rule](../../../DESIGN.md#documentation-maintenance).

Include `cpu_byteslice_level_arena_engine.hpp` for the engine. The public map adapters are [`byte_map.hpp`](../../../include/cpu_byteslice_oram/byte_map.hpp) and [`configuration.hpp`](../../../include/cpu_byteslice_oram/configuration.hpp). Use the following entry points when modifying the implementation:

| Task | Files |
|---|---|
| Change geometry or capacity selection | `cpu_byteslice_level_arena_geometry.hpp`, `cpu_byteslice_level_arena_capacity.hpp`, `cpu_byteslice_level_arena_bytes.hpp` |
| Change nonce coordinates or initialization counters | `cpu_byteslice_level_arena_family.hpp` |
| Change buffer ownership or reclamation | `cpu_byteslice_level_arena_slots.hpp`, `cpu_byteslice_level_arena_boundary.hpp`, `cpu_byteslice_level_arena_epoch.hpp` |
| Change rebuilding | `cpu_byteslice_level_arena_job.hpp`, `cpu_byteslice_level_arena_merge.hpp`, `cpu_byteslice_level_arena_stash.hpp` (level 1's direct build: `../rebuild/cpu_byteslice_dense_select.hpp`, tested by `cpu_byteslice_dense_select_test`) |
| Change publication or level transitions | `cpu_byteslice_level_arena_publication.hpp`, `cpu_byteslice_level_arena_level.hpp` |
| Change dense buffering or accesses | `cpu_byteslice_level_arena_dense.hpp`, `cpu_byteslice_level_arena_engine.hpp` |
| Change batch execution | `cpu_byteslice_level_arena_batch.hpp`, `cpu_byteslice_level_arena_batch_workers.hpp` |
| Change the synchronous storage mode | `cpu_byteslice_level_arena_synchronous.hpp` |
| Change owner grouping, wakeups or placement | `cpu_byteslice_level_arena_rebuild_params.hpp`, `cpu_byteslice_level_arena_owner.hpp`, `cpu_byteslice_level_arena_event.hpp`, `cpu_byteslice_level_arena_placement.hpp` |

For geometry changes, run `python3 analysis/level_arena_model.py` from the repository root and the arena geometry/capacity tests. Update the component buffer predictors and allocation census together. The model's bucket ratio is not bytes per logical entry.

For merge changes, use the [job](../../../tests/oram/cpu_byteslice_level_arena_job_test.cpp), [merge](../../../tests/oram/cpu_byteslice_level_arena_merge_test.cpp) and [top](../../../tests/oram/cpu_byteslice_level_arena_top_test.cpp) fixtures. Preserve their checks of source bytes, routing, newest-copy selection and forced residual cases. Compare every incoming `TableView` layout and tier layout with the job's layout; matching extents alone is insufficient. Tier occupancy belongs to `ResidualStash`'s inline masks, so construct published tier views from that stash. The incremental arena set owns the compact payload pool; every physical slot keeps one permanent slice. The geometry fixture checks packing and preserved main offsets, and the batch-worker fixture independently counts pool allocations.

For ownership changes, use the [lifecycle](../../../tests/oram/cpu_byteslice_level_arena_lifecycle_test.cpp) and [threaded](../../../tests/oram/cpu_byteslice_level_arena_threads_test.cpp) fixtures. Named pause points in `cpu_byteslice_level_arena_pause.hpp` expose specific protocol windows without relying on timing. Never retain a writable view beyond its lease, mutate published masks, or pass a predicted retirement threshold as observed reader progress.

For capacity diagnostics, [the occupancy observer](cpu_byteslice_level_arena_occupancy.hpp) reports, through a global function-pointer hook like the pause hook's, the occupancy of every residual structure of a rebuild job where it is at its maximum: stage, radix, merge, retained-carry and dense-builder stashes at the start of the residual pass that consumes them (a drain-only slot at its epilogue), DFS range-table leaves right after the build, and the published tier when the job's last phase ends. It exists only under `MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER`: without it the counting, the hook load, the job's members and the planners' stage marks are compiled out, and `CPU_BYTESLICE_ORAM_RELEASE` refuses the macro because the occupancies are secret. Only `cpu_byteslice_occupancy_observer` ([driver](../../../benchmarks/oram/cpu_byteslice_occupancy_observer.cpp), [reducer](../../../analysis/occupancy_tail.py)) defines it, and nothing it prints is a performance row. Capacities are the engine's own, an overflow is a thrown failure rather than an observation, and zero overflows in a run do not establish `2^-64`.

For online changes, run the [engine](../../../tests/oram/cpu_byteslice_level_arena_engine_test.cpp), [batch](../../../tests/oram/cpu_byteslice_level_arena_batch_test.cpp) and [batch-worker](../../../tests/oram/cpu_byteslice_level_arena_batch_workers_test.cpp) fixtures. Batch participants must join even on failure before the requester releases its snapshot. Bucket-owned dense scanning is configured through `deamortized_batch_bucket_scan`; `deamortized_batch_profile` enables per-participant phase timings.

For access-budget and counter changes, also run the
[lifetime fixture](../../../tests/oram/cpu_byteslice_level_arena_lifetime_test.cpp)
and [callback fixture](../../../tests/oram/cpu_byteslice_access_test.cpp), both
optimized and checked. They cover exhaustion without record or reply mutation,
whole-chunk refusal, smaller retries, initialization offsets and composed
hierarchy/tree operations. The lifetime fixture also checks construction-time
family/window limits and dense ID encodings at the largest accepted counters.
Run the geometry and capacity fixtures when changing these limits; capacity
pricing must use an executable horizon when it constructs an engine.

For the synchronous storage mode, run the [synchronous tests](../../../tests/oram/cpu_byteslice_level_arena_synchronous_test.cpp): they run it in lockstep with the inline executor and compare tables. A merge job that reads its older operand anywhere but through the copy breaks the in-place binding.

Use [initialization tests](../../../tests/oram/cpu_byteslice_level_arena_init_test.cpp) for one-shot construction and [placement tests](../../../tests/oram/cpu_byteslice_level_arena_placement_test.cpp) for pure placement arithmetic. CPU pinning belongs in the caller's thread-init hooks. Do not treat benchmark results on one placement as a portable default.

Scalar online value workers are opt-in. `LevelArenaEngine::Options` exposes
`value_workers` (default 0), `value_tail` (default 2, clamped to retain the
current unit in the prefix), `value_kernel` (`ValueKernel::kAuto`,
`kAccumulate`, `kPermute`), `value_spin_nanos`, `value_pause`,
`value_monitor_wait`, `value_demote`, and `value_thread_init(unsigned)`.
The hook runs once on each value thread; failure fails construction. Value
workers need a dense prefix of at most 4096 buckets (`prefix_flushes *
stash_buckets`); the constructor refuses a longer one. Values
up to 24 columns per worker use accumulation; wider ranges use the permute
fallback. Empty ranges still participate in the public job/completion schedule.
`value_serial` runs the identical split protocol on the requester for fixtures.
Audit builds run value workers too (the requester's audit sees every real
probe; the workers' choices follow the progress it publishes).
`ValueWorkers()` reports the executor actually enabled. The synchronous storage
mode can also use value workers.

The scalar cascade probes each hashed main and the dense tier published right
after it as one step: the tier's match and extract run while the main bucket is
in flight, and the main's extract after the next bucket's prefetches.  Lines
read and real/dummy choices are a function of the plan alone; a value-worker
boundary that falls between a main and its tier is supported, not realigned
(see the joint-group comment above `Cascade` in
[the engine header](cpu_byteslice_level_arena_engine.hpp)).

`Drain()` commits pending scalar insertion bytes before draining rebuilds.
Batch calls, unprobed writes, executor steps, full-unit freezes and destruction
also commit pending bytes before another actor can read or reuse them. Scalar
calls remain synchronous: all probe reads complete before returning, even
though the insertion is forwarded to the next job. Caller buffers are never
retained. Public path transitions may pay an insertion-only round trip.

The level-arena benchmark accepts `--value-workers`, `--value-tail`,
`--value-kernel`, `--value-cpus`, `--value-spin-ns`, `--value-no-pause`, and
`--value-demote`. `--rebuild-cpus` places resolved owners followed by their
helpers even with a heuristic rebuild budget. `--value-profile` adds hashed
sampling and per-thread TSC sums; throughput comparisons should leave it off
and use separate diagnostic runs. TSC rate is measured against wall time;
reported TSC ticks are not measured core cycles. Start/reply demotion remains
off by default, and progress is never demoted. The default worker count is
zero: whether value workers pay off depends on the host, the value width and
the placement, so measure them for the target workload before enabling them.
Such measurements must include complete operation semantics and insertion
drains.

Run both normal and checked [value-worker model tests](../../../tests/oram/cpu_byteslice_value_workers_test.cpp)
and [protected-page tests](../../../tests/oram/cpu_byteslice_value_plane_memory_test.cpp)
when changing this path. The model covers operation semantics, forwarding,
empty ranges, parking, progress-tag reuse, failures and aligned-buffer accounting.
Also run the online, synchronous, configuration and ownership fixtures listed
above. For sanitizer checks, build the checked value-worker model test with
`-fsanitize=thread` (run with `TSAN_OPTIONS=halt_on_error=1`) or
`-fsanitize=address,undefined`. For the instruction census, run
[`tests/timing/instruction_census.py`](../../../tests/timing/instruction_census.py)
over the value-worker, protected-page and level-arena benchmark binaries, as
described in the [timing README](../../../tests/timing/README.md).
