# Source design

The implementation separates the representation of an oblivious operation from
the policy that schedules it. This lets the hierarchical engines share routing
and probing kernels while choosing different rebuild lifetimes. The tree engine
uses the hierarchy for its small position records and keeps large values in a
separate structure, so moving a value does not require rebuilding it through
every hierarchical level.

The [system design](../DESIGN.md) explains the construction and its security
boundary. The component documents explain the mechanisms:

| Component | Design responsibility |
|---|---|
| [Core](core/DESIGN.md) | Keep secret selection in registers and preserve full memory accesses through compilation. |
| [Cryptography](crypto/DESIGN.md) | Derive unpredictable routing tags and fixed-width stored keys. |
| [ORAM](oram/DESIGN.md) | Compose probes, rebuilds, and publication into map operations. |
| [ORAM / table](oram/table/DESIGN.md) | Byte-sliced bucket layout, metadata, routing tags, and oblivious probes and batch matching. |
| [ORAM / rebuild](oram/rebuild/DESIGN.md) | Oblivious routing networks, deduplication and residual recovery that build a table from its inputs. |
| [ORAM / scheduler](oram/scheduler/DESIGN.md) | Rebuild task plans that run a rebuild in resumable, lane-divided pieces. |
| [ORAM / levelarena](oram/levelarena/DESIGN.md) | The hierarchical engine behind `ByteMap`: geometry, carries, publication, readers, worker threads, and capacity certification. |
| [ORAM / tree](oram/tree/DESIGN.md) | The tree ORAM for large values: read-path eviction, stash, payload workers, and its hierarchical position map. |
| [ORAM / support](oram/support/DESIGN.md) | Benchmark-only measurement of arrivals, queueing and batching; not part of any access protocol. |

The public API that wraps these components is in
[`include/cpu_byteslice_oram`](../include/cpu_byteslice_oram/README.md).

## Suggested reading order

1. The [system design](../DESIGN.md), for the construction, the observer model
   and the security boundary.
2. [Core](core/DESIGN.md) and [cryptography](crypto/DESIGN.md): the
   instruction-level and cryptographic primitives every engine relies on.
3. The [ORAM composition](oram/DESIGN.md), then the
   [table layer](oram/table/DESIGN.md): what one access does.
4. The [rebuild kernels](oram/rebuild/DESIGN.md) and the
   [scheduler](oram/scheduler/DESIGN.md): how tables are rebuilt obliviously.
5. The [level arena](oram/levelarena/DESIGN.md): how accesses and rebuilds
   overlap safely, and how the capacity bound is certified.
6. The [tree engine](oram/tree/DESIGN.md), for values too wide to rebuild
   cheaply.
7. [Measurement support](oram/support/DESIGN.md), only when reading the
   benchmarks.

The dependency direction follows these responsibilities. Core primitives do not
know which table is being probed. Cryptographic primitives do not allocate
rebuild epochs or choose buckets. ORAM components supply those policies and own
the state that makes their use correct. Measurement utilities observe operations
through callbacks rather than becoming part of an engine's access protocol.

Update these documents in place under the
[documentation maintenance rule](../DESIGN.md#documentation-maintenance).
README files carry include paths, configuration, file ownership, and validation
commands.
