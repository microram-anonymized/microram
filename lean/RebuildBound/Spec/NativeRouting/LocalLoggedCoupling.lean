import RebuildBound.Spec.NativeRouting.LocalLog
import RebuildBound.Spec.NativeRouting.LocalCoverage

/-! Logged sparse replay couples complete native messages using only the
reference result's finite query log. Canonical pair inventories enter through
event containment, not through reconstruction of unread canonical jobs. -/
namespace RebuildBound.Spec.NativeRoutingLocalLoggedCoupling
open Model NativeRoutingActual

def memoAlias {Stored : Type} (stored : LogicalKey → Stored) (memo : Memo) : Prop :=
  ∃ family x y, Sum.inl (family, x) ∈ memo.map Prod.fst ∧
    Sum.inl (family, y) ∈ memo.map Prod.fst ∧ x ≠ y ∧ stored x = stored y
end RebuildBound.Spec.NativeRoutingLocalLoggedCoupling

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive
open NativeRoutingActual NativeRoutingCoupling NativeNormalize NativeRoutingLocalBudget NativeRoutingLocalLog
open NativeMatchProduction NativeMatchRoutingBudget NativeRoutingLocalLoggedCoupling

/-- Every scheduled table reconstructed by a probing lane occurs in the
complete adaptive read log. No capacity or ring-success guard is needed. -/
def NativeRoutingLocalLoggedTableReads_statement : Prop :=
  ∀ member initialized h (ctx : Context member initialized h),
    member ∈ ConfigurationFamily.members → ctx.Valid → ∀ (tape : IdealKey.Tape) t,
    t < ctx.accesses → ∀ slot, (slots (ctx.run tape))[t]? = some slot → slot.probes = true →
    ∀ c ∈ (slotSchedule (widths (ctx.run tape)) ctx.schedule t).tables,
      (ReadTree.reads tape (NativeRoutingLocalTable.tableProgram ctx.geo.cfg ctx.geo.shapes
        (traceOf ctx.unit (ctx.run tape)) c.1 c.2)).map Prod.fst ⊆
      (ReadTree.reads tape (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes
        ctx.unit ctx.schedule ctx.client)).map Prod.fst

/-- Returned logs preserve structural query-domain coverage on arbitrary
reply branches. No coherence or successful execution is assumed. -/
def NativeRoutingLocalLoggedDomain_statement : Prop :=
  ∀ {Q α : Type} (tree : ReadTree Q α) (P : Q → Prop), ReadTree.allQueries P tree →
    ∀ (encode : Q → LogicalKey) (answers : Answers 64 (depth (record tree))) result,
    NativeRoutingLocalBudget.replayResult encode (record tree) answers = some result →
    ∀ entry ∈ result.2, P entry.1

/-- The logged reference result records exactly the encoded cached conversion
history, in reverse chronological order. This is a syntactic replay identity. -/
def NativeRoutingLocalLoggedHistory_statement : Prop :=
  ∀ {Q α : Type} (tree : ReadTree Q α) (encode : Q → LogicalKey)
    (answers : Answers 64 (depth (record tree))) result,
    NativeRoutingLocalBudget.replayResult encode (record tree) answers = some result →
    conversions (chooseCoordinates (ReadTree.replyChooser encode (record tree))) answers =
      (result.2.map fun entry => (encode entry.1, entry.2)).reverse

/-- Actual-log aliases are contained in the one canonical routing pair event;
repeated reads need no additional pair count. -/
def NativeRoutingLocalLoggedAlias_statement : Prop :=
  ∀ {Stored : Type} (stored : LogicalKey → Stored) member initialized h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ tape, memoAlias stored (ReadTree.reads tape (NativeRoutingLocalReplay.readProgram
      ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)) →
      NativeNormalizePairs.PairBad stored (NativeRoutingLocalPairs.routingPairs ctx tape)

/-- The same iid-answer experiment returns the identical native logged result
when its reference log has no same-family fingerprint alias. Field/counter
premises only ensure complete-message encoding; no success conditioning occurs. -/
def NativeRoutingLocalLoggedReplay_statement : Prop :=
  ∀ {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h), FieldsFit ctx → CounterFit ctx →
    let tree := record (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes
      ctx.unit ctx.schedule ctx.client)
    ∀ (stored : Tape 128) (answers : Answers 64 (depth tree)) result,
    NativeRoutingLocalBudget.replayResult (Coordinates.referenceCode ∘ wire ctx) tree answers = some result →
    ¬memoAlias stored result.2 →
    NativeRoutingLocalBudget.replayResult (Coordinates.nativeCode stored ∘ wire ctx) tree answers = some result
end RebuildBound.Spec
