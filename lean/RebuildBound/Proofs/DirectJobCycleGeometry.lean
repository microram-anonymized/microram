import RebuildBound.Spec.DirectJobCycleGeometry
import RebuildBound.Proofs.DirectJobPopulation
import RebuildBound.Proofs.FiniteCoupling
import RebuildBound.Proofs.DirectJobUniformCycle.Keys
import RebuildBound.Proofs.DirectJobUniformCycle.Congr
import RebuildBound.Proofs.DirectJobUniformCycle.Split

/-! A uniform cycle tape supplies unconditional reference histories for the
actual per-digit geometry and source load. Coordinate splitting and reference
word congruence are shared by every member; no numerical bound is imported. -/

open MeasureTheory
open scoped ENNReal
namespace RebuildBound.DirectJobUniformCycleProof
open Model Model.DirectJob Spec

noncomputable section
variable {n : Nat} (units : Fin n → List Bucket)

abbrev Words (j : Fin n) : Type := cycleKeys units j → Fin (2 ^ 64)

/-- The blocks strictly before ordinal `i`. -/
abbrev Base (i : Nat) : Type := ∀ p : {p : Fin n // p.val < i}, Words units p.1

/-- Ordinal `p`'s zero-extended block of a base (zero for `p ≥ i`). -/
def baseWord (i : Nat) (hi : i + 1 < n) (base : Base units i) (p : Nat) (k : Model.LogicalKey) : Nat :=
  if hp : p < i then
    if hk : k ∈ cycleKeys units ⟨p, by omega⟩ then (base ⟨⟨p, by omega⟩, hp⟩ ⟨k, hk⟩ : Nat)
    else 0
  else 0

/-- The first `i` ordinals with the base's words. -/
def prefixSteps (i : Nat) (hi : i + 1 < n) (base : Base units i) :
    List ((Model.LogicalKey → Nat) × List Bucket) :=
  List.ofFn fun p : Fin i => (baseWord units i hi base p, units ⟨p.1, by have := p.2; omega⟩)

def histDataFor (geometry : Nat → Geometry) (i : Nat) (hi : i + 1 < n) : DirectHistoryData where
  KA := cycleKeys units ⟨i, by omega⟩
  KB := unitKeys (units ⟨i + 1, hi⟩)
  Base := Base units i
  weight _ := (Fintype.card (Base units i) : ℝ≥0∞)⁻¹
  before base := referenceChain (fun _ => 0) (.ofOutput emptyOutput)
    (directChainJobs geometry 1 (prefixSteps units i hi base))
  olderWord base := baseWord units i hi base (i - 1)
  chronology base := chainRecords (directChainJobs geometry 1 (prefixSteps units i hi base))
  priorUnits _ _ := units ⟨i, by omega⟩
  freshUnits _ _ := units ⟨i + 1, hi⟩

abbrev Unused (i : Nat) (hi : i + 1 < n) : Type :=
  ∀ j : {j : Fin n // ¬ j.val < i ∧ j ≠ ⟨i, by omega⟩ ∧ j ≠ ⟨i + 1, hi⟩}, Words units j.1

def splitLaterFor (geometry : Nat → Geometry) (s : SepGeom) (i : Nat) (hi : i + 1 < n) :
    CycleTape units ≃ ((histDataFor units geometry i hi).lawFor (geometry (i + 1)) s).toFinite.Outcome × Unused units i hi :=
  let e1 : (∀ j, Words units j) ≃ ((Base units i × Words units ⟨i, by omega⟩) ×
      Words units ⟨i + 1, hi⟩) × Unused units i hi :=
    split3 (Words units) (fun j : Fin n => j.val < i) ⟨i, by omega⟩ ⟨i + 1, hi⟩
      (by simp) (by simp) (by simp [Fin.ext_iff])
  let e2 : Words units ⟨i + 1, hi⟩ ≃
      ((cycleKeys units ⟨i, by omega⟩ ∪ unitKeys (units ⟨i + 1, hi⟩) : Finset Model.LogicalKey) →
        Fin (2 ^ 64)) :=
    keyCast (cycleKeys_succ units i hi) (Fin (2 ^ 64))
  e1.trans (Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) e2) (Equiv.refl _))

theorem histData_validFor (geometry : Nat → Geometry) (s : SepGeom) (load i : Nat)
    (hi : i + 1 < n) (hd : s.d = i + 2)
    (hcard : ∀ j, (unitKeys (units j)).card ≤ load * s.U) :
    (histDataFor units geometry i hi).ValidFor s load := by
  have hne : (Fintype.card (Base units i) : ℝ≥0∞) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  refine DirectJobHistoryPrefixValidFor (histDataFor units geometry i hi) s load
    (fun base => directChainJobs geometry 1 (prefixSteps units i hi base)) (fun _ _ => 0)
    (List.ofFn fun p : Fin i => unitKeys (units ⟨p.1, by have := p.2; omega⟩))
    (unitKeys (units ⟨i, by omega⟩)) ?_ (fun _ => ⟨rfl, rfl⟩) ?_ ?_ (fun _ _ => rfl)
    (cycleKeys_eq_population units i (by omega)) (by simpa using hd.symm) (fun _ _ => rfl) (hcard _)
  · show ∑ _ : Base units i, (Fintype.card (Base units i) : ℝ≥0∞)⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel hne (ENNReal.natCast_ne_top _)
  · intro base
    apply forall₂_for
    rw [List.forall₂_iff_get]
    refine ⟨by simp [prefixSteps], fun p h1 h2 => ?_⟩
    simp [prefixSteps, unitKeys]
  · intro keys hk
    simp only [List.mem_cons, List.mem_ofFn] at hk
    rcases hk with rfl | ⟨p, rfl⟩ <;> exact hcard _

theorem baseWord_tape {Ω : Type} (π : Ω → CycleTape units) (i : Nat) (hi : i + 1 < n)
    (native : Fin n → Ω → Model.LogicalKey → Nat)
    (hnative : ∀ j ω k (hk : k ∈ cycleKeys units j), native j ω k = π ω j ⟨k, hk⟩)
    (ω : Ω) (p : Nat) (hp : p < i) (k : Model.LogicalKey)
    (hk : k ∈ cycleKeys units ⟨p, by omega⟩) :
    baseWord units i hi (fun q => π ω q.1) p k = native ⟨p, by omega⟩ ω k := by
  simp only [baseWord, hp, hk, ↓reduceDIte]
  rw [hnative _ _ k hk]

theorem laterFor (geometry : Nat → Geometry) (s : SepGeom) (load : Nat) [MeasurableSpace (CycleTape units)] [MeasurableSingletonClass (CycleTape units)]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (π : Ω → CycleTape units) (hπ : Measurable π)
    (hμ : μ.map π = ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape units)))
    (hcard : ∀ j, (unitKeys (units j)).card ≤ load * s.U)
    (oldWord : Ω → Model.LogicalKey → Nat)
    (native : Fin n → Ω → Model.LogicalKey → Nat)
    (hnative : ∀ j ω k (hk : k ∈ cycleKeys units j), native j ω k = π ω j ⟨k, hk⟩)
    (i : Nat) (hi : i + 1 < n) (hd : s.d = i + 2) :
    DirectCycleLaterCoupled μ geometry s load oldWord (cycleStepsOn units native) i := by
  refine ⟨histDataFor units geometry i hi, histData_validFor units geometry s load i hi hd hcard,
    fun ω => (splitLaterFor units geometry s i hi (π ω)).1, ?_, ?_⟩
  · have hw : ∀ hist, ((histDataFor units geometry i hi).lawFor (geometry (i + 1)) s).toFinite.weight hist =
        (Fintype.card ((histDataFor units geometry i hi).lawFor (geometry (i + 1)) s).toFinite.Hist : ℝ≥0∞)⁻¹ := by
      intro hist
      change (Fintype.card (Base units i) : ℝ≥0∞)⁻¹ *
        (Fintype.card (histDataFor units geometry i hi).Words : ℝ≥0∞)⁻¹ =
        (Fintype.card (Base units i × (histDataFor units geometry i hi).Words) : ℝ≥0∞)⁻¹
      rw [Fintype.card_prod, Nat.cast_mul,
        ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
    exact FiniteCouplingProof.finite_uniform_image_coupling μ π hπ hμ _ (Unused units i hi)
      (splitLaterFor units geometry s i hi) hw
  · intro ω prev cur hp hc _
    have hi' : i < n := by omega
    simp only [cycleStepsOn, List.getElem?_ofFn, hi', hi, dite_true, Option.some.injEq] at hp hc
    subst hp hc
    refine ⟨?_, ?_, ?_, rfl, rfl, ?_⟩
    · show referenceChain (fun _ => 0) (.ofOutput emptyOutput)
          (directChainJobs geometry 1 (prefixSteps units i hi (fun q => π ω q.1))) = _
      refine chain_congr_for geometry 1 _ _ _ _ _ []
        (by simp [ReferenceTable.records, ReferenceTable.ofOutput, emptyOutput, Bucket.recs,
          DirectPrefix.winners])
        (by simp [ReferenceTable.ofOutput, emptyOutput]) (by simp [prefixSteps, cycleStepsOn]; omega)
        (fun p h h' => by simp [prefixSteps, cycleStepsOn]) ?_
      intro p h h' x hx
      have hpi : p < i := by simpa [prefixSteps] using h
      simp only [List.nil_append] at hx
      obtain ⟨q, hq, hxq⟩ := mem_steps_records hx
      have hqp : q ≤ p := by simp at hq; omega
      have hkey : x.key ∈ cycleKeys units ⟨p, by omega⟩ :=
        unitKeys_sub_cycleKeys units (Fin.le_def.2 hqp)
          (by simpa [prefixSteps] using mem_unitKeys hxq)
      simp only [prefixSteps, cycleStepsOn, List.getElem_ofFn, List.getElem_take]
      exact baseWord_tape units π i hi native hnative ω p hpi x.key hkey
    · intro x hx
      have hrec : x ∈ chainRecords (directChainJobs geometry 1 (prefixSteps units i hi (fun q => π ω q.1))) := by
        have hh := DirectJobReferenceHistory (fun _ => 0) (.ofOutput emptyOutput)
          (directChainJobs geometry 1 (prefixSteps units i hi (fun q => π ω q.1))) []
          (by simp [ReferenceTable.records, ReferenceTable.ofOutput, emptyOutput, Bucket.recs,
            DirectPrefix.winners])
        have := mem_records_of_perm hh (List.mem_append_left _ hx)
        simpa using this
      rw [chainRecords_for] at hrec
      obtain ⟨q, hq, hxq⟩ := mem_steps_records hrec
      have hqi : q < i := by simpa [prefixSteps] using hq
      have hkey : x.key ∈ cycleKeys units ⟨i - 1, by omega⟩ :=
        unitKeys_sub_cycleKeys units (Fin.le_def.2 (show q ≤ i - 1 by omega))
          (by simpa [prefixSteps] using mem_unitKeys hxq)
      have hold := DirectJobSelectedCycleProof.oldWord_succ (cycleStepsOn units native ω) (i - 1)
        (oldWord ω) (native ⟨i - 1, by omega⟩ ω, units ⟨i - 1, by omega⟩)
        (by simp [cycleStepsOn, show i - 1 < n by omega])
      rw [show i - 1 + 1 = i by omega] at hold
      rw [hold]
      exact baseWord_tape units π i hi native hnative ω (i - 1) (by omega) x.key hkey
    · intro k hk
      show (if hx : k ∈ cycleKeys units ⟨i, hi'⟩ then ((π ω ⟨i, hi'⟩ ⟨k, hx⟩ : Fin (2 ^ 64)) : Nat)
        else 0) = native ⟨i, hi'⟩ ω k
      have hk' : k ∈ cycleKeys units ⟨i, hi'⟩ := hk
      simp only [hk', ↓reduceDIte]
      rw [hnative _ _ k hk']
    · intro k hk
      have hk' : k ∈ cycleKeys units ⟨i + 1, hi⟩ := by
        rw [cycleKeys_succ]
        exact hk
      show (if hx : k ∈ cycleKeys units ⟨i, hi'⟩ ∪ unitKeys (units ⟨i + 1, hi⟩) then
        (((splitLaterFor units geometry s i hi (π ω)).1.2 ⟨k, hx⟩ : Fin (2 ^ 64)) : Nat) else 0) =
          native ⟨i + 1, hi⟩ ω k
      have hk2 : k ∈ cycleKeys units ⟨i, hi'⟩ ∪ unitKeys (units ⟨i + 1, hi⟩) := hk
      simp only [hk2, ↓reduceDIte]
      rw [hnative _ _ k hk']
      rfl

end
end RebuildBound.DirectJobUniformCycleProof

open RebuildBound.DirectJobUniformCycleProof RebuildBound.Spec in
theorem RebuildBound.DirectJobUniformCycleHistory : DirectJobUniformCycleHistory_statement := by
  intro n units geometry s load i hi hd hcard _ _ Ω _ μ π hπ hμ oldWord native hnative
  exact laterFor units geometry s load μ π hπ hμ hcard oldWord native hnative i hi hd
