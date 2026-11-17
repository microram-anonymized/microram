# ORAM implementation guide

Read [DESIGN.md](DESIGN.md) for component composition and follow each folder's
design document for algorithms and invariants. This directory is internal,
header-only implementation code. Applications include
`<cpu_byteslice_oram/oram.hpp>`; internal includes use repository-root paths such
as `src/oram/rebuild/cpu_byteslice_rebuild.hpp`.

| Folder | Engineering entry point |
|---|---|
| [table](table/README.md) | Layout, metadata, routing tags, probe plans, and batch primitives. |
| [rebuild](rebuild/README.md) | Routing and deduplication umbrella headers. |
| [scheduler](scheduler/README.md) | Rebuild task planners, execution contexts, and residual-pass validation. |
| [levelarena](levelarena/README.md) | Implementation behind `ByteMap<true>` and, in its synchronous storage mode, `ByteMap<false>`. |
| [tree](tree/README.md) | Tree storage, eviction, workers, and position maps. |
| [support](support/README.md) | Benchmark and calibration utilities. |

The hierarchical code uses namespace `microram::byteslice`. Arena code adds `microram::byteslice::levelarena`; tree code uses
`microram::tree`. Keep tree-to-hierarchy integration through the public
`ByteMap` interface and keep measurement helpers out of production include
paths where they are unnecessary.

Build and test commands are in the repository [README](../../README.md#build).
Tests live in `tests/oram/`; each component README identifies relevant targets.
