import RebuildBound.Spec.NativeMatch.LocalBound
import RebuildBound.Proofs.NativeNormalizePairs
import RebuildBound.Proofs.NativeMatchExactCounts
import RebuildBound.Proofs.NativeMatchLocalApi
import RebuildBound.Proofs.NativeRoutingLocalPairs

namespace RebuildBound.NativeMatchLocalBoundProof
open Model Spec NativeMatchProduction NativeMatchPhysical NativeMatchLocalApi
open NativeRoutingLocalPairs NativeNormalizePairs NativeMatchLocalBound NativeNormalize
open MeasureTheory
open scoped ENNReal

local instance : MeasurableSpace (Pairs LogicalKey) := ⊤
local instance : DiscreteMeasurableSpace (Pairs LogicalKey) := ⟨fun _ => trivial⟩

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma finiteRead (ctx : Context member initialized h) :
    IdealKey.FiniteRead (normalizationPairs ctx) := by
  have hg := (NativeRoutingLocalPairsProof.run_finiteRead ctx).comp
    (fun run => ready ctx.unit run ctx.snapshots ctx.accesses)
  have he := NativeMatchLocalApiFiniteRead member initialized h ctx
  have hp := NativeRoutingLocalPairsFiniteRead member initialized h ctx
  exact (hg.pair (he.pair hp)).comp (fun p => if p.1 then p.2.1 ++ p.2.2 else [])

lemma linear (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    (normalizationPairs ctx tape).length ≤
      coefficientA member initialized + ctx.accesses * coefficientB member initialized := by
  unfold normalizationPairs
  split
  · have he := NativeMatchExactPairsLinear member initialized h ctx hm hv tape ‹_›
    have hp := NativeRoutingLocalPairsLinear member initialized h ctx hm hv tape ‹_›
    simp only [List.length_append, coefficientA, coefficientB, Nat.mul_add]
    omega
  · simp

lemma normalize_bound (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) :
    (IdealKey.tapeLaw.prod (tapeLaw 128))
      {p | PairBad p.2 (normalizationPairs ctx p.1)} ≤ normalizeCost ctx := by
  apply NativeNormalizePairsBound IdealKey.tapeLaw 128 _ (normalizationPairs ctx)
  · intro pairs
    exact (IdealFiniteReadMeasurable _ _ (finiteRead ctx)) (measurableSet_singleton pairs)
  · exact linear ctx hm hv

lemma error_bound (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hh : 1 ≤ h) (hv : ctx.Valid) :
    (IdealKey.tapeLaw.prod (tapeLaw 128)) {p | bad ctx p} ≤ min 1 (error ctx) := by
  let μ := IdealKey.tapeLaw.prod (tapeLaw 128)
  have hc := NativeMatchProductionCombined member initialized hm h hh ctx hv
  have hn := normalize_bound ctx hm hv
  have hr : μ {p | ready ctx.unit (ctx.run p.1) ctx.snapshots ctx.accesses = false} ≤
      NativeMatchCoded.ringCost ctx := by
    have H := Measure.le_map_apply (μ := μ) measurable_fst.aemeasurable
      {tape | ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = false}
    rw [show μ.map Prod.fst = IdealKey.tapeLaw by
      dsimp [μ]
      rw [Measure.map_fst_prod, measure_univ, one_smul]] at H
    exact H
  refine le_min prob_le_one ?_
  have hu := measure_union_le (μ := μ)
    {p | ctx.capacityBad p.1 ∨ ∃ e ∈ ctx.inventory p.1, e.bad p.2}
    {p | PairBad p.2 (normalizationPairs ctx p.1) ∨
      ready ctx.unit (ctx.run p.1) ctx.snapshots ctx.accesses = false}
  have hvu := measure_union_le (μ := μ)
    {p | PairBad p.2 (normalizationPairs ctx p.1)}
    {p | ready ctx.unit (ctx.run p.1) ctx.snapshots ctx.accesses = false}
  exact hu.trans ((add_le_add hc (hvu.trans (add_le_add hn hr))).trans_eq (by
    simp only [error, add_assoc]))

lemma projection (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (policy : NativeMatchApi.Policy) (tape : IdealKey.Tape) (stored : Tape 128)
    (hoff : ¬bad ctx (tape, stored)) :
    NativeMatchApi.production ctx policy stored tape = .ok (NativeMatchApi.reference ctx tape) := by
  have hc : ¬ctx.capacityBad tape := fun hc => hoff (Or.inl (Or.inl hc))
  have he : ∀ e ∈ ctx.inventory tape, ¬e.bad stored :=
    fun e he hb => hoff (Or.inl (Or.inr ⟨e, he, hb⟩))
  have hr : ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true := by
    cases ht : ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses with
    | false => exact (hoff (Or.inr (Or.inr ht))).elim
    | true => rfl
  have hn : ¬PairBad stored (exactPairs ctx tape) := by
    intro hn
    apply hoff
    apply Or.inr ∘ Or.inl
    simp only [normalizationPairs, hr, ↓reduceIte]
    exact (NativeNormalizePairsEvent.1 stored _ _).mpr (Or.inl hn)
  exact NativeMatchLocalApiProjection NativeMatchExactPairsRun
    member initialized h ctx hm hv policy stored tape hc hr hn he

end RebuildBound.NativeMatchLocalBoundProof

namespace RebuildBound
open Spec NativeMatchLocalBoundProof

theorem NativeMatchLocalBoundFiniteRead : Spec.NativeMatchLocalBoundFiniteRead_statement := by
  intro member initialized h ctx
  exact finiteRead ctx

theorem NativeMatchLocalBoundLinear : Spec.NativeMatchLocalBoundLinear_statement := by
  intro member initialized h ctx hm hv tape
  exact linear ctx hm hv tape

theorem NativeMatchLocalBoundNormalize : Spec.NativeMatchLocalBoundNormalize_statement := by
  intro member initialized h ctx hm hv
  exact normalize_bound ctx hm hv

theorem NativeMatchLocalBoundError : Spec.NativeMatchLocalBoundError_statement := by
  intro member initialized hm h hh ctx hv
  exact error_bound ctx hm hh hv

theorem NativeMatchLocalBoundProjection : Spec.NativeMatchLocalBoundProjection_statement := by
  intro member initialized h ctx hm hv policy tape stored hoff
  exact projection ctx hm hv policy tape stored hoff

end RebuildBound
