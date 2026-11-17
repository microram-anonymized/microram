import RebuildBound.Proofs.NativeRoutingLocalDiagnostics

/-! Diagnostic recursion follows only requested dependencies and adds no
routing reads; eager native startup remains a distinct pending interface. -/
namespace RebuildBound.NativeRoutingLocalDiagnosticsTests
open Model Model.Hierarchy Spec NativeRoutingActual NativeRoutingLocalDiagnostics

private def cfg : Config := ⟨[4], 2, 8, 32, 128, false⟩

example : invokedJobs cfg 1 0 = [] ∧ invokedJobs cfg 2 0 = [] := by
  norm_num [invokedJobs, cfg, Config.levels, Config.seed, Config.fanout]

/-- One top completion includes its dependency jobs and both top diagnostics;
it does not read the next speculative preparation. -/
example : invokedJobs cfg 2 1 =
    [.ordinary 1 1, .ordinary 1 2, .ordinary 1 3, .ordinary 1 4,
      .topPrepare 1, .topFinish 1] := by
  norm_num [invokedJobs, cfg, Config.levels, Config.seed, Config.fanout]

/-- A seeded top exposes initialization even with no issued accesses. -/
example : invokedJobs { cfg with initialized := true } 2 8 = [.initialization] ∧
    invokedJobs { cfg with initialized := true } 1 32 = [] := by
  norm_num [invokedJobs, cfg, Config.levels, Config.seed, Config.fanout]

/-- Every reply branch retains the original sparse table program. -/
example (sh : Shapes) (tr : Trace) (level ordinal : Nat) :
    NativeRoutingLocalTable.bind (tableProgram cfg sh tr level ordinal)
        (fun result => .done result.output) =
      NativeRoutingLocalTable.tableProgram cfg sh tr level ordinal :=
  NativeRoutingLocalDiagnosticsProjection cfg sh tr level ordinal

/-- Diagnostic failures and VP2 events do not force extra reads. -/
example (sh : Shapes) (tr : Trace) (tape : IdealKey.Tape) :
    ReadTree.reads tape (tableProgram { cfg with initialized := true } sh tr 2 8) =
      ReadTree.reads tape
        (NativeRoutingLocalTable.tableProgram { cfg with initialized := true } sh tr 2 8) :=
  NativeRoutingLocalDiagnosticsReads _ sh tr tape 2 8

end RebuildBound.NativeRoutingLocalDiagnosticsTests
