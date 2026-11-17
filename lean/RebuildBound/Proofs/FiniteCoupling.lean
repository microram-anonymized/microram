import RebuildBound.Spec.FiniteTransport
import RebuildBound.Spec.Model.Law
import RebuildBound.Spec.Model.SepLaw
import RebuildBound.Spec.Model.TopLaw
import RebuildBound.Spec.Model.TopPrepLaw
import RebuildBound.Spec.G3
import RebuildBound.Proofs.FiniteLaw
import RebuildBound.Proofs.BlindBits.Words
import Mathlib.Probability.UniformOn

/-! # FiniteCoupling: transport and uniform-tape coupling for every job law.

The four job laws are their `toFinite` laws by `rfl` (probability and word
function), and the generic `prob` is the proof-side `FiniteLawProof.prob`, so
every `FiniteLawProof.prob_*` lemma applies to it directly.

Couplings pull back along measurable maps to finite spaces. A uniform image
law and an outcome split therefore supply a coupling on the ambient space
without requiring the caller to repeat the measure-map argument.

Pitfall: pass the event explicitly to `finite_transport`/`finite_transport_sub`;
leaving it as `_` makes higher-order unification against `L.prob (fun …)`
exhaust the heartbeat limit. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound
open Model Spec

/-! ## The four projections are definitional -/

theorem Model.JobLaw.prob_toFinite {g : Geom} (L : JobLaw g)
    (E : L.Hist → (Model.LogicalKey → Nat) → Prop) : L.prob E = L.toFinite.prob E := rfl
theorem Model.SJobLaw.prob_toFinite {g : SepGeom} (L : SJobLaw g)
    (E : L.Hist → (Model.LogicalKey → Nat) → Prop) : L.prob E = L.toFinite.prob E := rfl
theorem Model.TopJobLaw.prob_toFinite {g : TopGeom} (L : TopJobLaw g)
    (E : L.Hist → (Model.LogicalKey → Nat) → Prop) : L.prob E = L.toFinite.prob E := rfl
theorem Model.TPJobLaw.prob_toFinite {g : TPGeom} (L : TPJobLaw g)
    (E : L.Hist → (Model.LogicalKey → Nat) → Prop) : L.prob E = L.toFinite.prob E := rfl

theorem Model.JobLaw.wordFn_toFinite {g : Geom} (L : JobLaw g) :
    L.wordFn = L.toFinite.wordFn := rfl
theorem Model.SJobLaw.wordFn_toFinite {g : SepGeom} (L : SJobLaw g) :
    L.wordFn = L.toFinite.wordFn := rfl
theorem Model.TopJobLaw.wordFn_toFinite {g : TopGeom} (L : TopJobLaw g) :
    L.wordFn = L.toFinite.wordFn := rfl
theorem Model.TPJobLaw.wordFn_toFinite {g : TPGeom} (L : TPJobLaw g) :
    L.wordFn = L.toFinite.wordFn := rfl

/-- The generic law is the proof-side finite law. -/
theorem Model.FiniteJobLaw.prob_eq_finiteLaw (L : FiniteJobLaw)
    (E : L.Hist → (Model.LogicalKey → Nat) → Prop) :
    L.prob E = FiniteLawProof.prob L.weight L.wordFn E := rfl

/-! ## Uniform projections -/

namespace DirectJobUniformProof

/-- A finite product projection has equally sized fibers. Reuse the existing
uniform-average transport instead of proving a new independence theorem. -/
theorem uniform_projection {Ω Outcome Unused : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Outcome]
    [Fintype Unused] [Nonempty Unused] (split : Ω ≃ Outcome × Unused)
    (outcome : Outcome) :
    ProbabilityTheory.uniformOn (Set.univ : Set Ω) {ω | (split ω).1 = outcome} =
      (Fintype.card Outcome : ℝ≥0∞)⁻¹ := by
  classical
  have hfiber (x : Outcome) :
      (Finset.univ.filter fun ω => (split ω).1 = x).card = Fintype.card Unused := by
    let e : {ω // (split ω).1 = x} ≃ Unused :=
      { toFun := fun ω => (split ω.val).2
        invFun := fun u => ⟨split.symm (x, u), by simp⟩
        left_inv := by
          intro ω
          apply Subtype.ext
          apply split.injective
          change split (split.symm (x, (split ω.val).2)) = split ω.val
          rw [split.apply_symm_apply]
          exact Prod.ext ω.property.symm rfl
        right_inv := fun u => by simp }
    simpa only [Fintype.card_subtype] using Fintype.card_congr e
  have hset : {ω | (split ω).1 = outcome} =
      (↑(Finset.univ.filter fun ω => (split ω).1 = outcome) : Set Ω) := by
    ext ω
    simp
  rw [ProbabilityTheory.uniformOn_univ, hset, Measure.count_apply_finset,
    div_eq_mul_inv, mul_comm, Finset.card_filter, Nat.cast_sum]
  simpa using G2.avg_comp (fun ω => (split ω).1) (Fintype.card Unused)
    Fintype.card_pos.ne' hfiber (fun x => if x = outcome then 1 else 0)

end DirectJobUniformProof

namespace FiniteCouplingProof

/-! ## Transport -/

/-- A coupling of the image law pulls back along a measurable map to a finite
type with measurable singletons. -/
theorem coupling_map {Ω T : Type} [MeasurableSpace Ω] [MeasurableSpace T] [Finite T]
    [MeasurableSingletonClass T] (μ : Measure Ω) (π : Ω → T) (hπ : Measurable π)
    (L : FiniteJobLaw) (sample : T → L.Outcome)
    (hc : FiniteCoupling (μ.map π) L sample) : FiniteCoupling μ L (sample ∘ π) := by
  intro outcome
  have h := hc outcome
  rw [Measure.map_apply hπ (Set.toFinite _).measurableSet] at h
  exact h

/-- The event at a coupled sample has probability at most the law's. -/
theorem finite_transport {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (L : FiniteJobLaw) (sample : Ω → L.Outcome)
    (hc : FiniteCoupling μ L sample) (E : L.Hist → (Model.LogicalKey → Nat) → Prop) :
    μ {ω | E (sample ω).1 (L.wordFn (sample ω).2)} ≤ L.prob E := by
  classical
  let outcomes := Finset.univ.filter fun x : L.Outcome => E x.1 (L.wordFn x.2)
  have hcover : {ω | E (sample ω).1 (L.wordFn (sample ω).2)} ⊆
      ⋃ x ∈ outcomes, {ω | sample ω = x} := by
    intro ω hω
    exact Set.mem_iUnion.mpr ⟨sample ω, Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω⟩, rfl⟩⟩
  calc
    μ {ω | E (sample ω).1 (L.wordFn (sample ω).2)} ≤
        μ (⋃ x ∈ outcomes, {ω | sample ω = x}) := measure_mono hcover
    _ ≤ ∑ x ∈ outcomes, μ {ω | sample ω = x} := measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ outcomes, L.weight x.1 * (Fintype.card L.Words : ℝ≥0∞)⁻¹ :=
      Finset.sum_le_sum fun x _ => hc x
    _ = L.prob E := by
      simp only [outcomes, Finset.sum_filter, Fintype.sum_prod_type, FiniteJobLaw.prob,
        Finset.mul_sum, mul_ite, mul_one, mul_zero]

/-- Containment form: what a premise supplied by the hierarchy model
feeds in. -/
theorem finite_transport_sub {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (L : FiniteJobLaw) (sample : Ω → L.Outcome)
    (hc : FiniteCoupling μ L sample) (E : L.Hist → (Model.LogicalKey → Nat) → Prop) (A : Set Ω)
    (hA : A ⊆ {ω | E (sample ω).1 (L.wordFn (sample ω).2)}) : μ A ≤ L.prob E :=
  (measure_mono hA).trans (finite_transport μ L sample hc E)

/-- A uniform finite tape that splits into the law's outcomes and unused
coordinates is coupled to the law when the history weights are uniform. -/
theorem finite_uniform_coupling {Ω : Type} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (L : FiniteJobLaw)
    (Unused : Type) [Fintype Unused] [Nonempty Unused] (split : Ω ≃ L.Outcome × Unused)
    (hw : ∀ hist, L.weight hist = (Fintype.card L.Hist : ℝ≥0∞)⁻¹) :
    FiniteCoupling (ProbabilityTheory.uniformOn (Set.univ : Set Ω)) L
      (fun ω => (split ω).1) := by
  intro outcome
  rw [DirectJobUniformProof.uniform_projection split outcome, hw,
    Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

/-- A measurable projection with a uniform finite image couples the ambient
space to a law whose split outcomes have uniform history weights. -/
theorem finite_uniform_image_coupling {Ω T : Type} [MeasurableSpace Ω]
    [MeasurableSpace T] [Fintype T] [MeasurableSingletonClass T]
    (μ : Measure Ω) (π : Ω → T) (hπ : Measurable π)
    (hμ : μ.map π = ProbabilityTheory.uniformOn (Set.univ : Set T))
    (L : FiniteJobLaw) (Unused : Type) [Fintype Unused] [Nonempty Unused]
    (split : T ≃ L.Outcome × Unused)
    (hw : ∀ hist, L.weight hist = (Fintype.card L.Hist : ℝ≥0∞)⁻¹) :
    FiniteCoupling μ L (fun ω => (split (π ω)).1) := by
  have hc := finite_uniform_coupling L Unused split hw
  rw [← hμ] at hc
  exact coupling_map μ π hπ L _ hc

/-- The top finish and the top preparation use the same transport. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {g : TopGeom} (L : TopJobLaw g)
    (unsh : Rec → Bool) (sample : Ω → L.toFinite.Outcome)
    (hc : FiniteCoupling μ L.toFinite sample) :
    μ {ω | topFailEvent L unsh (sample ω).1 (L.wordFn (sample ω).2)} ≤
      L.prob (topFailEvent L unsh) :=
  finite_transport μ L.toFinite sample hc (topFailEvent L unsh)

end FiniteCouplingProof

theorem FiniteTransport : FiniteTransport_statement := by
  intro Ω _ μ L sample hc E A hA
  exact FiniteCouplingProof.finite_transport_sub μ L sample hc E A hA

end RebuildBound
