import RebuildBound.Proofs.AdaptiveLevelOneA.GeometryLaw
import RebuildBound.Proofs.DirectJobAProbability
import RebuildBound.Proofs.DirectJobHistoryLaw
import RebuildBound.Proofs.DirectJobPopulation
import RebuildBound.Proofs.DirectJobOldWordDensity
import RebuildBound.Proofs.DirectJobUniformCycle

/-! # AdaptiveLevelOneA: the A-only history law of one cell

Within a cell, the cycle's earlier ordinals' units and word functions are
fixed: `uv j` are the units of the cycle's ordinal `j + 1` and `wv j` the word
of its ordinal `j` (`wv 0` is the previous cycle's last word). The law is
`DirectHistoryData.law d` with `KA` the keys of the first `d - 1` ordinals,
`KB = ∅` and no fresh units; its base is the two fresh blocks off `KA`
(uniform), and it draws the previous family's words on `KA` and the current
words on `KA`. The A probability is `DirectJobSelectedAProbability`. -/

open scoped ENNReal NNReal

namespace RebuildBound.AdaptiveLevelOneAProof
open Model Model.DirectJob Spec DirectJobUniformCycleProof

/-- Compatibility specialization of the shared causal history. -/
noncomputable abbrev aData (N d : Nat) (wv : Nat → LogicalKey → Nat) (uv : Nat → List Bucket) :
    DirectHistoryData := aDataFor selectedDirectGeometry N d wv uv

theorem aData_eq (N d : Nat) (wv : Nat → LogicalKey → Nat) (uv : Nat → List Bucket) :
    aData N d wv uv = aDataFor selectedDirectGeometry N d wv uv := rfl

theorem aData_valid (N d : Nat) (hd : 2 ≤ d) (wv : Nat → LogicalKey → Nat) (uv : Nat → List Bucket)
    (hcard : ∀ j, (unitKeys (uv j)).card ≤ 512) : (aData N d wv uv).Valid d := by
  have hv := aData_validFor selectedDirectGeometry (selectedDirectSep d) 32 N d hd
    (Nat.div_mul_cancel (SG1Proof.val2_dvd d)) wv uv hcard
  rw [← aData_eq] at hv
  refine ⟨hv.weight_sum, hv.before_history, hv.prior_keys, hv.fresh_keys, ?_, hv.bLoad⟩
  simpa only [show (selectedDirectSep d).d = d from
    Nat.div_mul_cancel (SG1Proof.val2_dvd d), show (selectedDirectSep d).U = 16 from rfl] using hv.aLoad

theorem aData_uniform (N d : Nat) (wv : Nat → LogicalKey → Nat) (uv : Nat → List Bucket) :
    ∀ hist, ((aData N d wv uv).law d).toFinite.weight hist =
      (Fintype.card ((aData N d wv uv).law d).toFinite.Hist : ℝ≥0∞)⁻¹ := by
  exact aData_uniformFor selectedDirectGeometry (selectedDirectSep d) N d wv uv

/-- The A event of the law. -/
def aEvent (N d : Nat) (wv : Nat → LogicalKey → Nat) (uv : Nat → List Bucket)
    (hist : (aData N d wv uv).Hist) (word : LogicalKey → Nat) : Prop :=
  ((aData N d wv uv).direct d hist word).aTier.length ≤ (selectedDirectGeometry d).aTierCapacity ∧
    (aRouteWitness (selectedDirectGeometry d) word ((aData N d wv uv).direct d hist word) ∨
      aRangeWitness (selectedDirectGeometry d) word ((aData N d wv uv).direct d hist word))

theorem aData_prob (N d : Nat) (hd : 2 ≤ d) (hd8 : d ≤ 8) (wv : Nat → LogicalKey → Nat)
    (uv : Nat → List Bucket) (hcard : ∀ j, (unitKeys (uv j)).card ≤ 512) :
    ((aData N d wv uv).law d).toFinite.prob (aEvent N d wv uv) ≤ selectedDirectABudget d := by
  have hv := aData_valid N d hd wv uv hcard
  refine DirectJobSelectedAProbability d hd hd8 ((aData N d wv uv).law d)
    ((selectedDirectSep d).oldDensity 64 (aData N d wv uv).KA.card)
    (DirectJobHistoryInputLaw d hd hd8 _ hv) rfl ?_ ((aData N d wv uv).direct d)
    (fun _ _ => ⟨rfl, rfl⟩)
  apply selected_oldDensity_mono d hd hd8
  have hdd := (DirectJobSelectedGeometry.2 d hd hd8).2.2.1
  change (aData N d wv uv).KA.card ≤ 32 * (((selectedDirectSep d).d - 1) * 16)
  rw [hdd]
  exact hv.aLoad

end RebuildBound.AdaptiveLevelOneAProof
