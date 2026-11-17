import RebuildBound.Spec.NativeRouting.LocalReference

/-! A generic query logger preserves the sparse reader's entire query tree.
Logs retain original logical coordinates and chronological reply order. The
logger adds no reads; its finite marginal laws remain unconditional. -/
namespace RebuildBound.Spec.NativeRoutingLocalLog
open Model NativeRoutingActual

/-- Accumulate replies in reverse, then return their chronological order. -/
def recordAux {Q α : Type} : ReadTree Q α → List (Q × Word64) →
    ReadTree Q (α × List (Q × Word64))
  | .done result, past => .done (result, past.reverse)
  | .read query next, past => .read query fun word => recordAux (next word) ((query, word) :: past)

/-- Keep the returned result and every logical query/reply, in read order. -/
def record {Q α : Type} (tree : ReadTree Q α) : ReadTree Q (α × List (Q × Word64)) :=
  recordAux tree []
end RebuildBound.Spec.NativeRoutingLocalLog

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive MeasureTheory
open NativeRoutingActual NativeRoutingCoupling NativeNormalize NativeRoutingLocalBudget NativeRoutingLocalLog
open NativeMatchProduction NativeMatchRoutingBudget

def NativeRoutingLocalLogEvaluate_statement : Prop :=
  ∀ {Q α : Type} (tree : ReadTree Q α) (tape : Q → Word64),
    ReadTree.evaluate tape (record tree) = (ReadTree.evaluate tape tree, ReadTree.reads tape tree)

def NativeRoutingLocalLogReads_statement : Prop :=
  ∀ {Q α : Type} (tree : ReadTree Q α) (tape : Q → Word64),
    ReadTree.reads tape (record tree) = ReadTree.reads tape tree

/-- Every reply branch has precisely the original public-domain obligations,
including inconsistent repeated-coordinate branches. -/
def NativeRoutingLocalLogQueries_statement : Prop :=
  ∀ {Q α : Type} (tree : ReadTree Q α) (P : Q → Prop),
    ReadTree.allQueries P (record tree) ↔ ReadTree.allQueries P tree

def NativeRoutingLocalLogDepth_statement : Prop :=
  ∀ {Q α : Type} (tree : ReadTree Q α), depth (record tree) = depth tree

/-- Erasing the log recovers the original whole reader, not just its value on
coherent tapes. -/
def NativeRoutingLocalLogProjection_statement : Prop :=
  ∀ {Q α : Type} (tree : ReadTree Q α),
    NativeRoutingLocalTable.bind (record tree) (fun result => .done result.1) = tree

/-- Agreement on the reads selected by one coherent execution preserves both
its result and its entire read list. No all-branch tape agreement is required. -/
def NativeRoutingLocalLogCongruence_statement : Prop :=
  ∀ {Q α : Type} (tree : ReadTree Q α) (tape other : Q → Word64),
    (∀ entry ∈ ReadTree.reads tape tree, other entry.1 = entry.2) →
    ReadTree.evaluate other tree = ReadTree.evaluate tape tree ∧
      ReadTree.reads other tree = ReadTree.reads tape tree

/-- A coherent execution's own log suffices to rerun it. This does not assert
that arbitrary inconsistent reply branches have a coherent memo. -/
def NativeRoutingLocalLogMemo_statement : Prop :=
  ∀ {α : Type} (tree : ReadTree IdealKey.Coord α) (tape : IdealKey.Tape),
    let result := ReadTree.evaluate tape (record tree)
    ReadTree.evaluate (memoTape result.2) tree = result.1 ∧
      ReadTree.reads (memoTape result.2) tree = result.2 ∧
      ∀ entry ∈ result.2, memoTape result.2 entry.1 = entry.2

/-- Generic native joint marginal for a logged reader. Original logical query
names stay in the log, including distinct names with aliased native messages. -/
def NativeRoutingLocalLogNative_statement : Prop :=
  ∀ {Q α Value : Type} [MeasurableSpace (Option Value)]
    (tree : ReadTree Q α) (wire : Q → Coordinates.Query)
    (observe : α × List (Q × Word64) → Value),
    (((Measure.dirac ()).prod (answerLaw 64 (depth (record tree)))).prod (tapeLaw 128)).map
      (fun p => (p.2, (NativeRoutingLocalBudget.replayResult
        (Coordinates.nativeCode p.2 ∘ wire) (record tree) p.1.2).map observe)) =
    (((Measure.dirac ()).prod (tapeLaw 128)).prod (tapeLaw 64)).map
      (fun p => (p.1.2, some (observe
        (ReadTree.evaluate (p.2 ∘ Coordinates.nativeCode p.1.2 ∘ wire) (record tree)))))

/-- Logged production reference replay has its canonical joint law. Structural
logging preserves the proved domain and adds no fixed-width premise. -/
def NativeRoutingLocalLogReference_statement : Prop :=
  ∀ {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h), FieldsFit ctx → CounterFit ctx →
  ∀ {Value : Type} [MeasurableSpace (Option Value)]
    (observe : Acc ctx.transcriptWidth × Memo → Value),
    let tree := NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
    ((answerLaw 64 (depth (record tree))).prod (tapeLaw 128)).map
      (fun p => ((NativeRoutingLocalBudget.replayResult
        (Coordinates.referenceCode ∘ wire ctx) (record tree) p.1).map observe, p.2)) =
    (IdealKey.tapeLaw.map (fun tape => some (observe
      (interact ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape), ReadTree.reads tape tree)))).prod (tapeLaw 128)
end RebuildBound.Spec
