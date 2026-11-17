import RebuildBound.Spec.NativeRouting.Actual

/-! A causal reader for one requested reference table. Dependency tables are
constructed before their input-record keys are read. The reader has no access
to normalization values, the capacity inventory, or future diagnostic jobs.
Repeated reconstruction is permitted: the prefix and horizon statements below
make its entire read tree stable once the table's inputs are complete. They do
not supply API replay, the unconditional marginal laws, or a family count. -/
namespace RebuildBound.Spec.NativeRoutingLocalTable
open Model Model.Hierarchy Model.DirectJob NativeRoutingActual

/-- Sequence a finite routing reader using only its returned value. -/
def bind {Q α β : Type} : ReadTree Q α → (α → ReadTree Q β) → ReadTree Q β
  | .done result, next => next result
  | .read query resume, next => .read query (fun word => bind (resume word) next)

/-- Real coordinates for the records of one already constructed input. -/
def recordQueries (family : IdealKey.Family) (records : List Rec) : List IdealKey.Coord :=
  records.map fun record => .inl (family, record.key)

/-- A step reads its current family's input records. Level one's old-home
reads use only the previous main records, under the previous family. The top
preparation's output records come from its input, so no extra reads are needed.
Physical holes contribute no record; retained records and tombstones do. -/
def stepQueries (cfg : Config) (tr : Trace) (level ordinal : Nat)
    (previous carry : Output) : List IdealKey.Coord :=
  recordQueries (familyOf cfg level ordinal)
    (previous.records ++ carry.records ++
      if level = 1 then DirectMasks.records (tr.units (ordinal - cfg.seed 1 - 1)) else []) ++
    if level = 1 ∧ level ≠ cfg.levels then
      recordQueries (familyOf cfg 1 (ordinal - 1)) (previous.main.flatMap Bucket.recs)
    else []

/-- The initialization is the sole source of reads for a base table. -/
def baseProgram (cfg : Config) (sh : Shapes) (tr : Trace) (level : Nat) :
    ReadTree IdealKey.Coord Output :=
  ReadTree.gather
    (if level = cfg.levels ∧ cfg.initialized = true then
      recordQueries (familyOf cfg cfg.levels (cfg.seed cfg.levels)) tr.init else []) []
    (fun memo => .done (base cfg sh tr (IdealHierarchy.words (memoTape memo)) level))

/-- Inputs are fixed before the step chooses any routing coordinate. -/
def stepProgram (cfg : Config) (sh : Shapes) (tr : Trace) (level ordinal : Nat)
    (previous carry : Output) : ReadTree IdealKey.Coord Output :=
  ReadTree.gather (stepQueries cfg tr level ordinal previous carry) []
    (fun memo => .done (step cfg sh tr (IdealHierarchy.words (memoTape memo))
      level ordinal previous carry))

/-- Construct exactly the dependency cone of a requested table, with job-local
reads. No configured horizon or potential-job inventory is enumerated. -/
def tableProgram (cfg : Config) (sh : Shapes) (tr : Trace) :
    Nat → Nat → ReadTree IdealKey.Coord Output
  | level, ordinal =>
    if level = 0 ∨ cfg.levels < level ∨ ordinal ≤ cfg.seed level then
      baseProgram cfg sh tr level
    else
      bind (tableProgram cfg sh tr level (ordinal - 1)) fun previous =>
        bind (if level = 1 then .done emptyOutput else
          tableProgram cfg sh tr (level - 1) (ordinal * cfg.fanout (level - 1))) fun carry =>
          stepProgram cfg sh tr level ordinal previous carry
termination_by level ordinal => (level, ordinal)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

end RebuildBound.Spec.NativeRoutingLocalTable

namespace RebuildBound.Spec
open Model Model.Hierarchy NativeRoutingActual NativeRoutingLocalTable

/-- Sparse table reconstruction has exactly the existing reference semantics,
including initialized/empty bases and reference overflow continuations. -/
def NativeRoutingLocalTableEvaluate_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (tr : Trace) (tape : IdealKey.Tape) (level ordinal : Nat),
    ReadTree.evaluate tape (tableProgram cfg sh tr level ordinal) =
      table cfg sh tr (IdealHierarchy.words tape) level ordinal

/-- A step reads precisely its explicit input support, including repeated keys
and old-family reads. There are no hidden diagnostic or dummy coordinates. -/
def NativeRoutingLocalTableStepReads_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (tr : Trace) (tape : IdealKey.Tape)
    (level ordinal : Nat) (previous carry : Output),
    (ReadTree.reads tape (stepProgram cfg sh tr level ordinal previous carry)).map Prod.fst =
      stepQueries cfg tr level ordinal previous carry

/-- Once the consumed input prefix is fixed, the entire sparse read program is
fixed under later trace extensions. No tape or schedule monotonicity is assumed. -/
def NativeRoutingLocalTablePrefix_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (tr tr' : Trace) (cut : Nat),
    tr.init = tr'.init → tr.unsh = tr'.unsh →
    (∀ i, cfg.seed 1 + i + 1 ≤ cut → tr.units i = tr'.units i) →
  ∀ level ordinal, time cfg level ordinal ≤ cut →
    tableProgram cfg sh tr level ordinal = tableProgram cfg sh tr' level ordinal

/-- Raising the certificate horizon without issuing more accesses changes no
part of a requested table's sparse program, including its adaptive reads. -/
def NativeRoutingLocalTableHorizon_statement : Prop :=
  ∀ (cfg : Config) (horizon : Nat) (sh : Shapes) (tr : Trace) (level ordinal : Nat),
    tableProgram { cfg with horizon := horizon } sh tr level ordinal =
      tableProgram cfg sh tr level ordinal

end RebuildBound.Spec
