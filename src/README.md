# Source tree

Read [DESIGN.md](DESIGN.md) for how the components divide the work. Everything
here is internal, header-only implementation code: applications include
`<cpu_byteslice_oram/oram.hpp>`, and internal headers include each other by
repository-root paths such as `src/core/mov_intrinsics.hpp`.

| Folder | Engineering entry point |
|---|---|
| [core](core/README.md) | Constant-control-flow selection, monitor-wait, and the release-build guard. |
| [crypto](crypto/README.md) | AES key schedules, secret seeds, routing tags, and wide-key hashing. |
| [oram](oram/README.md) | Tables, rebuilds, schedulers, and the arena and tree engines. |

Keep the dependency direction of [DESIGN.md](DESIGN.md): `core` and `crypto`
include nothing from `oram`. Build and test commands are in the repository
[README](../README.md#build).
