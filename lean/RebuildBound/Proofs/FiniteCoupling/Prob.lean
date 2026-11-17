import RebuildBound.Spec.Model.Law
import RebuildBound.Spec.Model.SepLaw
import RebuildBound.Spec.Model.TopLaw
import RebuildBound.Spec.Model.TopPrepLaw
import RebuildBound.Proofs.FiniteLaw

/-! # The union-bound lemmas for every job law

Each job law's `prob` is `FiniteLawProof.prob L.weight L.wordFn` by `rfl`
(`JobLaw.prob_eq` and its three siblings). The lemmas below take that equation
as their first argument, `prob_mono_of L.prob_eq h`: the job law's `prob` then
stays the head of every goal, so the events unify first-order. (Stating them
for `FiniteJobLaw.prob` instead makes Lean unify `L.toFinite.prob ?E` with
`L.prob E` up to unfolding, which exhausts the heartbeat limit.) -/

open scoped ENNReal NNReal

namespace RebuildBound

theorem Model.JobLaw.prob_eq {g : Model.Geom} (L : Model.JobLaw g) :
    L.prob = FiniteLawProof.prob L.weight L.wordFn := rfl
theorem Model.SJobLaw.prob_eq {g : Model.SepGeom} (L : Model.SJobLaw g) :
    L.prob = FiniteLawProof.prob L.weight L.wordFn := rfl
theorem Model.TopJobLaw.prob_eq {g : Model.TopGeom} (L : Model.TopJobLaw g) :
    L.prob = FiniteLawProof.prob L.weight L.wordFn := rfl
theorem Model.TPJobLaw.prob_eq {g : Model.TPGeom} (L : Model.TPJobLaw g) :
    L.prob = FiniteLawProof.prob L.weight L.wordFn := rfl

namespace FiniteLawProof

open Spec

variable {Hist Word : Type} [Fintype Hist] [Fintype Word] {weight : Hist → ℝ≥0∞}
  {wordFn : Word → Model.LogicalKey → ℕ} {P : (Hist → (Model.LogicalKey → ℕ) → Prop) → ℝ≥0∞}

theorem prob_mono_of (hP : P = prob weight wordFn) {E F : Hist → (Model.LogicalKey → ℕ) → Prop}
    (h : ∀ hist hw, E hist (wordFn hw) → F hist (wordFn hw)) : P E ≤ P F :=
  hP ▸ prob_mono weight wordFn h

theorem prob_or_of (hP : P = prob weight wordFn) (E F : Hist → (Model.LogicalKey → ℕ) → Prop) :
    P (fun hist w => E hist w ∨ F hist w) ≤ P E + P F :=
  hP ▸ prob_or weight wordFn E F

theorem prob_exists_lt_of (hP : P = prob weight wordFn) (n : ℕ)
    (E : ℕ → Hist → (Model.LogicalKey → ℕ) → Prop) :
    P (fun hist w => ∃ j < n, E j hist w) ≤ ∑ j ∈ Finset.range n, P (E j) :=
  hP ▸ prob_exists_lt weight wordFn n E

/-- The union bound over a cover. -/
theorem prob_le_cover_of (hP : P = prob weight wordFn) (E : Hist → (Model.LogicalKey → ℕ) → Prop)
    (F : ℕ → Hist → (Model.LogicalKey → ℕ) → Prop) (n : ℕ) (h : ∀ hist w, E hist w → ∃ R < n, F R hist w) :
    P E ≤ ∑ R ∈ Finset.range n, P (F R) :=
  hP ▸ prob_le_cover weight wordFn E F n (fun hist w => h hist (wordFn w))

theorem prob_false_of (hP : P = prob weight wordFn) : P (fun _ _ => False) = 0 := by
  subst hP; simp [prob]

/-- An event contained in `{1 ≤ f hist}`, `f` a function of the history and the words. -/
theorem prob_le_sum_of (hP : P = prob weight wordFn) (E : Hist → (Model.LogicalKey → ℕ) → Prop)
    (f : Hist → Word → ℝ≥0∞) (hE : ∀ hist h, E hist (wordFn h) → 1 ≤ f hist h) :
    P E ≤ ∑ hist, weight hist * ((Fintype.card Word : ℝ≥0∞)⁻¹ * ∑ h, f hist h) :=
  hP ▸ prob_le_sum weight wordFn E f hE

/-- An event contained in `{1 ≤ f}` for a function `f` of the words alone. -/
theorem prob_le_avg_of (hP : P = prob weight wordFn) (hw : ∑ hist, weight hist = 1)
    (E : Hist → (Model.LogicalKey → ℕ) → Prop) (f : Word → ℝ≥0∞)
    (hE : ∀ hist h, E hist (wordFn h) → 1 ≤ f h) :
    P E ≤ (Fintype.card Word : ℝ≥0∞)⁻¹ * ∑ h, f h :=
  hP ▸ prob_le_avg weight wordFn hw E f hE

/-- **P3 applied to a job law.** A demand event whose excess is at most
`Σ_v (X_v - C)` of a count vector with the subset MGF envelope has probability
at most `Bsub`. -/
theorem prob_le_Bsub_of [Nonempty Word] (hP : P = prob weight wordFn) (h3 : P3_statement)
    (hw : ∑ hist, weight hist = 1) {n : ℕ} (C S : ℕ) (lam D : ℝ) (hlam : 0 < lam)
    (hC : lam ≤ C) (hD : 0 ≤ D) (X : Hist → Word → Fin n → ℕ)
    (hmgf : ∀ (J : Finset (Fin n)) (z : ℝ), 1 ≤ z →
      ∑ hist, weight hist * ((Fintype.card Word : ℝ≥0∞)⁻¹ *
        ∑ h, ENNReal.ofReal (z ^ ∑ v ∈ J, X hist h v)) ≤
        ENNReal.ofReal (D * Real.exp (lam * J.card * (z - 1))))
    (E : Hist → (Model.LogicalKey → ℕ) → Prop) (hE : ∀ hist h, E hist (wordFn h) → S < ∑ v, (X hist h v - C)) :
    P E ≤ ENNReal.ofReal (Bsub n C lam S D) :=
  hP ▸ prob_le_Bsub weight wordFn h3 hw C S lam D hlam hC hD X hmgf E hE

end FiniteLawProof

end RebuildBound
