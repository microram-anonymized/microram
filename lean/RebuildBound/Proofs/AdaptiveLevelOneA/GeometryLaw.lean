import RebuildBound.Proofs.DirectJobHistoryGeometry
import RebuildBound.Proofs.DirectJobPopulation
import RebuildBound.Proofs.DirectJobUniformCycle.Congr

/-! The common unconditional A-only product history of a causal cell, at the
actual per-digit geometry and incoming load. -/

open scoped ENNReal NNReal
namespace RebuildBound.AdaptiveLevelOneAProof
open Model Model.DirectJob Spec DirectJobUniformCycleProof

/-- The prefix steps of the cycle: ordinals `1, …, d - 2` with their words
and units. -/
def prefixSteps (d : Nat) (wv : Nat → LogicalKey → Nat) (uv : Nat → List Bucket) :
    List ((LogicalKey → Nat) × List Bucket) :=
  List.ofFn fun p : Fin (d - 2) => (wv (p.1 + 1), uv p.1)

/-- A's keys: the keys of the cycle's first `d - 1` ordinals. -/
def aKeys (d : Nat) (uv : Nat → List Bucket) : Finset LogicalKey :=
  directPopulationUnion (List.ofFn fun p : Fin (d - 2) => unitKeys (uv p.1)) ∪ unitKeys (uv (d - 2))

/-- One fresh block off A's keys. -/
abbrev OffBlock (N : Nat) (K : Finset LogicalKey) : Type := {k : KeyIndex N // k.val ∉ K} → Fin (2 ^ 64)

/-- The cell's A-only history data. -/
noncomputable def aDataFor (geometry : Nat → Geometry) (N d : Nat) (wv : Nat → LogicalKey → Nat) (uv : Nat → List Bucket) : DirectHistoryData where
  KA := aKeys d uv
  KB := ∅
  Base := OffBlock N (aKeys d uv) × OffBlock N (aKeys d uv)
  weight _ := (Fintype.card (OffBlock N (aKeys d uv) × OffBlock N (aKeys d uv)) : ℝ≥0∞)⁻¹
  before _ := referenceChain (wv 0) (.ofOutput emptyOutput) (directChainJobs geometry 1 (prefixSteps d wv uv))
  olderWord _ := wv (d - 2)
  chronology _ := chainRecords (directChainJobs geometry 1 (prefixSteps d wv uv))
  priorUnits _ _ := uv (d - 2)
  freshUnits _ _ := []

theorem aData_validFor (geometry : Nat → Geometry) (s : SepGeom) (load N d : Nat)
    (hd : 2 ≤ d) (hsd : s.d = d) (wv : Nat → LogicalKey → Nat) (uv : Nat → List Bucket)
    (hcard : ∀ j, (unitKeys (uv j)).card ≤ load * s.U) :
    (aDataFor geometry N d wv uv).ValidFor s load := by
  have hne : (Fintype.card (OffBlock N (aKeys d uv) × OffBlock N (aKeys d uv)) : ℝ≥0∞) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  refine DirectJobHistoryPrefixValidFor (aDataFor geometry N d wv uv) s load
    (fun _ => directChainJobs geometry 1 (prefixSteps d wv uv)) (fun _ => wv 0)
    (List.ofFn fun p : Fin (d - 2) => unitKeys (uv p.1)) (unitKeys (uv (d - 2))) ?_
    (fun _ => ⟨rfl, rfl⟩) ?_ ?_ (fun _ _ => rfl) rfl (by simp; omega) ?_ (by simp [aDataFor])
  · show ∑ _ : OffBlock N (aKeys d uv) × OffBlock N (aKeys d uv),
      (Fintype.card (OffBlock N (aKeys d uv) × OffBlock N (aKeys d uv)) : ℝ≥0∞)⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel hne (ENNReal.natCast_ne_top _)
  · intro _
    apply forall₂_for
    rw [List.forall₂_iff_get]
    refine ⟨by simp [prefixSteps], fun p h1 h2 => ?_⟩
    simp [prefixSteps, unitKeys]
  · intro keys hk
    simp only [List.mem_cons, List.mem_ofFn] at hk
    rcases hk with rfl | ⟨p, rfl⟩ <;> exact hcard _
  · intro _ _
    simp [aDataFor, DirectMasks.records]

theorem aData_uniformFor (geometry : Nat → Geometry) (s : SepGeom) (N d : Nat) (wv : Nat → LogicalKey → Nat) (uv : Nat → List Bucket) :
    ∀ hist, ((aDataFor geometry N d wv uv).lawFor (geometry (d - 1)) s).toFinite.weight hist =
      (Fintype.card ((aDataFor geometry N d wv uv).lawFor (geometry (d - 1)) s).toFinite.Hist : ℝ≥0∞)⁻¹ := by
  intro hist
  change (Fintype.card (OffBlock N (aKeys d uv) × OffBlock N (aKeys d uv)) : ℝ≥0∞)⁻¹ *
    (Fintype.card (aDataFor geometry N d wv uv).Words : ℝ≥0∞)⁻¹ =
    (Fintype.card ((OffBlock N (aKeys d uv) × OffBlock N (aKeys d uv)) ×
      (aDataFor geometry N d wv uv).Words) : ℝ≥0∞)⁻¹
  rw [Fintype.card_prod (OffBlock N (aKeys d uv) × OffBlock N (aKeys d uv)), Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

/-- The A event of the law. -/
def aEventFor (geometry : Nat → Geometry) (N d : Nat) (wv : Nat → LogicalKey → Nat) (uv : Nat → List Bucket)
    (hist : (aDataFor geometry N d wv uv).Hist) (word : LogicalKey → Nat) : Prop :=
  ((aDataFor geometry N d wv uv).directFor (geometry (d - 1)) hist word).aTier.length ≤ (geometry d).aTierCapacity ∧
    (aRouteWitness (geometry d) word ((aDataFor geometry N d wv uv).directFor (geometry (d - 1)) hist word) ∨
      aRangeWitness (geometry d) word ((aDataFor geometry N d wv uv).directFor (geometry (d - 1)) hist word))

end RebuildBound.AdaptiveLevelOneAProof
