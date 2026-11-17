# Public headers

Applications include `<cpu_byteslice_oram/oram.hpp>` and link
`cpu_byteslice_oram::cpu_byteslice_oram`. The [root README](../../README.md#library-api)
contains examples and the API contracts.

| Header | Responsibility |
|---|---|
| `oram.hpp` | Unified entry point and typed aliases |
| `access.hpp` | Shared callback signature dispatch (implementation detail) |
| `byte_map.hpp` | `Options`, hierarchical `ByteMap`, and the common typed adapter |
| `tree_oram.hpp` | `TreeOptions`, `TreeByteMap`, `HybridOptions`, and `HybridByteMap` |
| `configuration.hpp` | Opt-in public-input resolution, thread/memory plans, and `ConfiguredByteMap` ([guide](CONFIGURATION.md)) |
| `default_rule.hpp` | The default engine choice by value width, the default hierarchy geometry, and `CoreBudget` |

`Map<Key, T>` and `HybridByteMap` choose a backend from the public value width.
The default tree threshold is 96 bytes (`kHybridTreeValueThreshold`;
`default_rule.hpp` gives the rationale). `HierarchicalMap` /
`ByteMap` and `TreeMap` / `TreeByteMap` pin the backend. `Deamortize = false`
selects the hierarchy's synchronous storage mode, including when it is a
tree's position map. Payload workers and online batch participants have
separate options.

`TreeOptions` holds the tree's geometry (`fold`, `stash_registers`,
`max_folded_slots`, `leaf_scale`, `max_load`), `prefetch_ahead`,
`uid_from_key`, the payload worker options (`payload_max_threads`,
`payload_threshold`, `payload_spin_micros`, `payload_monitor_wait`,
`payload_worker_init`) and the position map's `Options`. Zero `fold` and
`stash_registers` select the default rule of the
[tree design](../../src/oram/tree/DESIGN.md#geometry-and-the-default-rule);
explicit values are validated as the [configuration guide](CONFIGURATION.md#selection-and-overrides)
lists. The tree runs one payload worker per started `payload_threshold` (32)
value bytes, with no fixed cap by default.

Hierarchical maps support one-shot initialization from distinct records on an
untouched map. Hybrid and tree adapters have `supports_initialize = false`.
Typed values need only be trivially copyable for pointer-output operations and
bulk initialization; optional-returning `find` and `at` also need default
construction and expose presence through their control flow.

`write` and `insert_or_assign` are blind upserts on the hierarchy; `exchange`
returns the previous value while replacing it. Callback `access` / `Access`
supports value-only and key/value mutators, optionally with a presence flag.
See the [callback contract](../../README.md#callback-access), including operation
counts, exceptions, and the default-construction requirement for typed values.

The hierarchy batches probes in chunks, default 16 lanes. Parallel tiles use
`deamortized_batch_participants` including the caller. Tree batching combines
position-map operations before ordered path accesses. Every map still requires
serialized calls. See the [batch contract](../../README.md#batched-access).

The [configuration guide](CONFIGURATION.md) describes `resolve_options`,
explicit resource budgets, construction hooks, buffer-accounting coverage and
conditional capacity reports. Resolution does not create maps or workers.
The ordinary constructors use their supplied options and defaults directly.

Changes to these headers should preserve public argument validation, buffer
lifetime and aliasing contracts, ordered batch effects, and deferred owner
startup for initialization. Validate with `cpu_byteslice_oram_map_test`,
`cpu_byteslice_configuration_test`, `cpu_byteslice_arena_map_test`, and the
tree map/batch tests, including their `_checked` variants. Implementation and
security arguments live in the [source designs](../../src/DESIGN.md).
`cpu_byteslice_access_test` covers blind writes, callback updates, key moves,
exceptions, and worker-backed operations across the public adapters.

Hierarchical scalar value workers are opt-in through the
[configuration controls](CONFIGURATION.md). All operations, including aliased
Exchange, use the same semantics as the inline cascade. Workers retain no
caller pointers. A scalar insertion may remain in owned pending storage;
`drain_rebuilds()`/complete pending-work APIs commit it before returning, and
batch calls and freezes drain it automatically. The default worker count is 0.
