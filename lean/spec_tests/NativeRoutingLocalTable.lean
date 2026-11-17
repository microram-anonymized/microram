import RebuildBound.Proofs.NativeRoutingLocalTable

/-! Sparse table readers choose records from completed dependency outputs.
These tests distinguish holes, tombstones, duplicate keys, old-family reads,
seeded initialization and unavailable future units. -/
namespace RebuildBound.NativeRoutingLocalTableTests
open Model Model.Hierarchy Model.DirectJob Spec NativeRoutingActual NativeRoutingLocalTable

private def keyA : LogicalKey := [0]
private def keyB : LogicalKey := [1]
private def keyC : LogicalKey := [2]
private def recordA : Rec := ⟨keyA, 7, false⟩
private def recordB : Rec := ⟨keyB, 11, false⟩
private def recordC : Rec := ⟨keyC, 13, false⟩
private def tombB : Rec := ⟨keyB, 0, true⟩
private def cfg : Config := ⟨[4], 2, 8, 32, 128, false⟩
private def previous : Output := ⟨[[some recordA, none]], [some tombB, none]⟩
private def carry : Output := ⟨[], [some recordC]⟩
private def tr : Trace := ⟨fun i => if i = 1 then [[some recordB, none, some recordA]] else [],
  [recordC], fun _ => false⟩

/-- Current support retains the tombstone and repeated fresh keys, skips holes,
and reads only previous main records under the prior family. -/
example : stepQueries cfg tr 1 2 previous emptyOutput =
    [.inl ((1, 2), keyA), .inl ((1, 2), keyB), .inl ((1, 2), keyB),
      .inl ((1, 2), keyA), .inl ((1, 1), keyA)] := by
  decide +kernel

/-- Top preparation/finish needs current-family input records only; the
unrelated fresh-unit key list is not read. -/
example : stepQueries cfg tr 2 1 previous carry =
    [.inl ((2, 1), keyA), .inl ((2, 1), keyB), .inl ((2, 1), keyC)] := by
  decide +kernel

/-- The registered read-support identity checks the actual program trace. -/
example (sh : Shapes) (tape : IdealKey.Tape) :
    (ReadTree.reads tape (stepProgram cfg sh tr 1 2 previous emptyOutput)).map Prod.fst =
      [.inl ((1, 2), keyA), .inl ((1, 2), keyB), .inl ((1, 2), keyB),
        .inl ((1, 2), keyA), .inl ((1, 1), keyA)] := by
  rw [NativeRoutingLocalTableStepReads]
  decide +kernel

/-- An empty-start base has no routing reads, even with arbitrary future units. -/
example (sh : Shapes) (tape : IdealKey.Tape) (trace : Trace) :
    ReadTree.reads tape (baseProgram cfg sh trace 2) = [] := by
  simp [baseProgram, cfg, Config.levels, ReadTree.gather, ReadTree.reads]

/-- The initialized base ignores every unit; only the initialization input
can choose its routing queries. This excludes seeded-unit overreads. -/
example (sh : Shapes) (trace : Trace) (units : Nat → List Bucket) :
    baseProgram { cfg with initialized := true } sh trace 2 =
      baseProgram { cfg with initialized := true } sh { trace with units := units } 2 := rfl

/-- A completed level-one prefix remains exactly the same read tree after
arbitrary changes to all later input units. -/
example (sh : Shapes) (trace : Trace) (future : Nat → List Bucket) :
    tableProgram cfg sh trace 1 2 =
      tableProgram cfg sh { trace with units := fun i => if i < 2 then trace.units i else future i } 1 2 := by
  apply NativeRoutingLocalTablePrefix cfg sh trace
    { trace with units := fun i => if i < 2 then trace.units i else future i } 2 rfl rfl
  · intro i hi
    have hi' : i < 2 := by simp [cfg, Config.seed] at hi; omega
    simp only [ite_eq_left hi']
  · decide +kernel

/-- Raising H changes no query or continuation, not merely the final output. -/
example (sh : Shapes) (trace : Trace) (level ordinal : Nat) :
    tableProgram { cfg with horizon := 2^32 } sh trace level ordinal =
      tableProgram cfg sh trace level ordinal :=
  NativeRoutingLocalTableHorizon cfg (2^32) sh trace level ordinal

/-- The sparse reader preserves the unconditional reference continuation,
including outcomes where physical capacity checks fail. -/
example (config : Config) (sh : Shapes) (trace : Trace) (tape : IdealKey.Tape)
    (level ordinal : Nat) :
    ReadTree.evaluate tape (tableProgram config sh trace level ordinal) =
      table config sh trace (IdealHierarchy.words tape) level ordinal :=
  NativeRoutingLocalTableEvaluate config sh trace tape level ordinal

end RebuildBound.NativeRoutingLocalTableTests
