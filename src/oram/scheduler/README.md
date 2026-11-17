# Working on rebuild planning

Read [DESIGN.md](DESIGN.md) for ordering, work units, and ownership contracts.
This directory translates public phase descriptions into kernel calls. Engine
scheduling policy remains in [levelarena](../levelarena/README.md).

| Header | Engineering responsibility |
|---|---|
| `cpu_byteslice_subtask.hpp` | Subtask kinds and fields |
| `cpu_byteslice_subtask_cost.hpp` | Per-phase widths and unit conversions |
| `cpu_byteslice_subtask_plan.hpp` | Phase planners and kernel issue order |
| `cpu_byteslice_subtask_run.hpp` | Context views and dispatcher |
| `cpu_byteslice_subtask_cursor.hpp` | Resumable execution of a planned phase: piece widths, the butterfly walk, the cursor |
| `cpu_byteslice_residual_pass.hpp` | Declarative pass validation and scratch attachment |

When adding a subtask, update its kind, planner, dispatcher, width units and
`PieceUnits` together. A planner that emits a new stage marks it
(`MarkStage`): a divisible stage names its shed stashes and every offer pass
whose masks each lane must copy privately; anything else is ordered. Check public ranges with nonzero starts and minimal widths, even
though live arena callers saturate widths. Preserve the shared butterfly leaf
rule and emitted order. A phase name does not establish that its sources are
private: pass published-mask information to the residual builder and validate
borrowed views before execution.

For residual planning changes, run the
[residual-build tests](../../../tests/oram/cpu_byteslice_residual_build_test.cpp)
and [fresher-copy tests](../../../tests/oram/cpu_byteslice_fresher_copy_test.cpp),
then the affected engine suite. Cover fused and standalone offers, direct and
DFS range plans, scratch overlap, empty public source lists, and private
masks over pinned payload. Follow the
[repository build instructions](../../../README.md) for configuration and
execution.

Edit design explanations in place under the
[documentation maintenance rule](../../../DESIGN.md#documentation-maintenance).
