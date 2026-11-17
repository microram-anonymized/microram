import RebuildBound.Spec.AdaptiveStepsJobs

/-!
# AdaptiveCell: the conditioning lemma `CausalCell`

Under the joint tape
premises the pushforward of `μ` to `FamilyTape cfg N × DummyTape n m` is
uniform. Split that space as cells `Y` (the tape off the fresh coordinates and
the dummy tape) times fresh blocks `Z`. On every cell the fresh-block count of
the event is at most `|Z| · b`, by the cell's uniform finite law; summing over
cells gives the count bound `|X| · b`, hence probability at most `b`.

Probability: the uniform measure `ProbabilityTheory.uniformOn` on the finite
tape space is reduced to counting (`Measure.count_apply_finset`); no obstacle.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.AdaptiveCellProof
open RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy

open Classical in
/-- Uniform weights: the event count is the law's mass times the outcome count. -/
theorem count_eq (L : FiniteJobLaw) (E : L.Hist → (LogicalKey → Nat) → Prop)
    (hw : ∀ hist, L.weight hist = (Fintype.card L.Hist : ℝ≥0∞)⁻¹) :
    (((Finset.univ.filter fun o : L.Outcome => E o.1 (L.wordFn o.2)).card : ℕ) : ℝ≥0∞) =
      (Fintype.card L.Hist : ℝ≥0∞) * (Fintype.card L.Words : ℝ≥0∞) * L.prob E := by
  have hH : (Fintype.card L.Hist : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hW : (Fintype.card L.Words : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hW0 : (Fintype.card L.Words : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card L.Words := Fintype.card_pos
    exact_mod_cast this.ne'
  by_cases hH0 : (Fintype.card L.Hist : ℝ≥0∞) = 0
  · have : Fintype.card L.Hist = 0 := by exact_mod_cast hH0
    have hemp : IsEmpty L.Hist := Fintype.card_eq_zero_iff.1 this
    simp
  unfold FiniteJobLaw.prob
  simp_rw [hw]
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.card_filter, Nat.cast_sum,
    Fintype.sum_prod_type]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  generalize (∑ x : L.Hist, ∑ x_1 : L.Words, if E x (L.wordFn x_1) then (1 : ℝ≥0∞) else 0) = S
  rw [show (Fintype.card L.Hist : ℝ≥0∞) * (Fintype.card L.Words : ℝ≥0∞) *
      ((Fintype.card L.Hist : ℝ≥0∞)⁻¹ * ((Fintype.card L.Words : ℝ≥0∞)⁻¹ * S)) =
      ((Fintype.card L.Hist : ℝ≥0∞) * (Fintype.card L.Hist : ℝ≥0∞)⁻¹) *
      ((Fintype.card L.Words : ℝ≥0∞) * (Fintype.card L.Words : ℝ≥0∞)⁻¹) * S by ring,
    ENNReal.mul_inv_cancel hW0 hW, ENNReal.mul_inv_cancel hH0 hH, one_mul, one_mul]

theorem causalCell : CausalCell_statement := by
  classical
  intro cfg N n m Ω _ μ _ tape dtape words hprem fresh _ A b hcell
  -- the cells and the fresh blocks
  let Y := ({c : Coord cfg // ¬ fresh c} → KeyIndex N → Fin (2 ^ 64)) × DummyTape n m
  let Z := {c : Coord cfg // fresh c} → KeyIndex N → Fin (2 ^ 64)
  let X := FamilyTape cfg N × DummyTape n m
  let e : X ≃ Y × Z :=
    { toFun := fun x => ((fun c => x.1 c.1, x.2), fun c => x.1 c.1)
      invFun := fun p => (fun c => if h : fresh c then p.2 ⟨c, h⟩ else p.1.1 ⟨c, h⟩, p.1.2)
      left_inv := fun x => by
        ext c <;> simp only <;> split_ifs <;> rfl
      right_inv := fun p => by
        rcases p with ⟨⟨y, d⟩, z⟩
        refine Prod.ext (Prod.ext ?_ rfl) ?_
        · funext c; simp [c.2]
        · funext c; simp [c.2] }
  choose L split E hw hb hE using hcell
  let P : Y → Z → Prop := fun y z => E y (split y z).1 ((L y).wordFn (split y z).2)
  let B : Set X := {x | P (e x).1 (e x).2}
  let f : Ω → X := fun ω => (tape ω, dtape ω)
  have hA : A ⊆ f ⁻¹' B := by
    intro ω hω
    exact hE ((fun c => tape ω c.1), dtape ω) ω hω rfl rfl
  have hBm : MeasurableSet B := (Set.toFinite B).measurableSet
  -- per-cell count
  have hcellc : ∀ y, (((Finset.univ.filter fun z => P y z).card : ℕ) : ℝ≥0∞) ≤
      (Fintype.card Z : ℝ≥0∞) * b := by
    intro y
    have h1 : (Finset.univ.filter fun z => P y z).card =
        (Finset.univ.filter fun o : (L y).Outcome => E y o.1 ((L y).wordFn o.2)).card := by
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      exact Fintype.card_congr ((split y).subtypeEquiv fun z => Iff.rfl)
    have hZ : Fintype.card Z = Fintype.card (L y).Hist * Fintype.card (L y).Words := by
      rw [Fintype.card_congr (split y), Fintype.card_prod]
    rw [h1, count_eq (L y) (E y) (hw y), hZ, Nat.cast_mul]
    gcongr; exact hb y
  have hcount : (((Finset.univ.filter fun x : X => P (e x).1 (e x).2).card : ℕ) : ℝ≥0∞) ≤
      (Fintype.card X : ℝ≥0∞) * b := by
    have h1 : (Finset.univ.filter fun x : X => P (e x).1 (e x).2).card =
        ∑ y : Y, (Finset.univ.filter fun z => P y z).card := by
      rw [← Fintype.card_subtype]
      rw [Fintype.card_congr (e.subtypeEquiv (p := fun x => P (e x).1 (e x).2)
        (q := fun q : Y × Z => P q.1 q.2) fun x => Iff.rfl)]
      rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
      simp only [Finset.card_filter]
    rw [h1, Nat.cast_sum]
    calc ∑ y : Y, (((Finset.univ.filter fun z => P y z).card : ℕ) : ℝ≥0∞)
        ≤ ∑ _y : Y, (Fintype.card Z : ℝ≥0∞) * b := Finset.sum_le_sum fun y _ => hcellc y
      _ = (Fintype.card X : ℝ≥0∞) * b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          Fintype.card_congr e, Fintype.card_prod Y Z, Nat.cast_mul]
  calc μ A ≤ μ (f ⁻¹' B) := measure_mono hA
    _ = (μ.map f) B := (Measure.map_apply hprem.measurable hBm).symm
    _ = ProbabilityTheory.uniformOn (Set.univ : Set X) B := by rw [hprem.uniform]
    _ = (((Finset.univ.filter fun x : X => P (e x).1 (e x).2).card : ℕ) : ℝ≥0∞) /
          (Fintype.card X : ℝ≥0∞) := by
      rw [ProbabilityTheory.uniformOn_univ]
      have hset : B = ↑(Finset.univ.filter fun x : X => P (e x).1 (e x).2) := by ext; simp [B]
      rw [hset, Measure.count_apply_finset]
    _ ≤ b := ENNReal.div_le_of_le_mul (by rw [mul_comm]; exact hcount)

end RebuildBound.AdaptiveCellProof

/-- **CausalCell**: the conditioning lemma of the adaptive capacity chain. -/
theorem RebuildBound.CausalCell : RebuildBound.Spec.CausalCell_statement :=
  RebuildBound.AdaptiveCellProof.causalCell
