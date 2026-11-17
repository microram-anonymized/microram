import RebuildBound.Proofs.NativeMatchExactCounts
import RebuildBound.Proofs.NativeMatchLocalApi
import RebuildBound.Proofs.NativeNormalizePairs

/-! The exact comparison coefficient is about issued lanes. A ring-guarded
inventory composes with the independent pair bound without a caller-supplied
population certificate or a capacity-success premise. -/
namespace RebuildBound.NativeMatchExactCountsTests
open Model Model.Hierarchy Spec NativeMatchProduction NativeMatchPhysical
open NativeMatchLocalApi NativeMatchExactCounts NativeNormalizePairs MeasureTheory

local instance : MeasurableSpace (Pairs LogicalKey) := ⊤
local instance : DiscreteMeasurableSpace (Pairs LogicalKey) := ⟨fun _ => trivial⟩

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

private noncomputable def guarded (ctx : Context member initialized h)
    (tape : IdealKey.Tape) : Pairs LogicalKey :=
  if ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses then exactPairs ctx tape else []

private theorem guarded_read (ctx : Context member initialized h) :
    IdealKey.FiniteRead (guarded ctx) := by
  have hr := (IdealAdaptiveFiniteRead ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
    ctx.transcriptWidth ctx.client).comp
    (fun result => (⟨result.1, ctx.client.init, ctx.client.unsh⟩ : OnlineBatch.BatchRun))
  have hg := hr.comp (fun run => ready ctx.unit run ctx.snapshots ctx.accesses)
  have he := NativeMatchLocalApiFiniteRead member initialized h ctx
  exact (hg.pair he).comp (fun p => if p.1 then p.2 else [])

/-- The guard depends only on the canonical tape. Its measure stays on the
unconditional product law, and actual q supplies the normalization budget. -/
example (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) :
    (IdealKey.tapeLaw.prod (NativeNormalize.tapeLaw 128))
      {p | PairBad p.2 (guarded ctx p.1)} ≤ pairBound 128 (ctx.accesses * perAccess member) := by
  apply NativeNormalizePairsBound IdealKey.tapeLaw 128 (ctx.accesses * perAccess member) (guarded ctx)
  · intro pairs
    exact (IdealFiniteReadMeasurable _ _ (guarded_read ctx)) (measurableSet_singleton pairs)
  · intro tape
    unfold guarded
    split
    · exact NativeMatchExactPairsLinear member initialized h ctx hm hv tape ‹_›
    · simp

/-- No access produces no exact comparisons, even when initialization is nonempty. -/
example (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape)
    (hr : ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true)
    (hq : ctx.accesses = 0) : exactPairs ctx tape = [] := by
  have hb := NativeMatchExactPairsLinear member initialized h ctx hm hv tape hr
  rw [hq, Nat.zero_mul] at hb
  exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hb)

/-- The table theorem includes reference overflow continuations. There is no
capacity-success assumption hidden in this application. -/
example (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) (level ordinal : Nat)
    (hl : 1 ≤ level) (hL : level ≤ ctx.geo.cfg.levels)
    (ho : ordinal ≤ ctx.geo.cfg.seed level + ctx.geo.cfg.ordinals level) :
    (table ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape))
      (IdealHierarchy.words tape) level ordinal).records.length ≤ maxRecords member :=
  NativeMatchExactTableCount member initialized h ctx hm hv tape level ordinal hl hL ho

/-- Enlarging the permitted horizon at the same actual q keeps this budget fixed. -/
example {h' : Nat} (ctx : Context member initialized h) (ctx' : Context member initialized h')
    (hq : ctx.accesses = ctx'.accesses) :
    ctx.accesses * perAccess member = ctx'.accesses * perAccess member := by rw [hq]

/- For this certified family the top population dominates every lower-table
allowance; the generic maximum is not silently replaced in the definition. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
example : ∀ member ∈ ConfigurationFamily.members,
    maxRecords member = (member.geometry false).keyCapacity ∧
    10816 ≤ perAccess member ∧ perAccess member ≤ 66571993664 := by
  decide +kernel

end RebuildBound.NativeMatchExactCountsTests
