import RebuildBound.Spec.Prob.Subset
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

open MeasureTheory
open scoped ENNReal

namespace RebuildBound

private lemma P3_bd (n C S : ℕ) (lam D : ℝ) (ν : Measure (Fin n → ℕ))
    (_hν : IsProbabilityMeasure ν) (hl : 0 < lam) (hlC : lam ≤ C)
    (henv : ∀ (J : Finset (Fin n)) (z : ℝ), 1 ≤ z →
      ∫⁻ x, ENNReal.ofReal (z ^ (∑ v ∈ J, x v)) ∂ν ≤
        ENNReal.ofReal (D * Real.exp (lam * J.card * (z - 1))))
    (J : Finset (Fin n)) (hJ : J.Nonempty) :
    ν {x | C * J.card + S + 1 ≤ ∑ v ∈ J, x v} ≤
      ENNReal.ofReal (D * Real.exp (lam * J.card * (Spec.subsetZ C lam S J.card - 1)) /
        Spec.subsetZ C lam S J.card ^ (C * J.card + S + 1)) := by
  set j := J.card with hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Finset.card_pos.mpr hJ
  have hpos : 0 < lam * j := by positivity
  set z := Spec.subsetZ C lam S j with hz
  have hz1 : 1 ≤ z := by
    rw [hz, Spec.subsetZ, one_le_div hpos]
    push_cast
    have : lam * j ≤ C * j := by nlinarith
    linarith
  have hzpos : 0 < z ^ (C * j + S + 1) := by positivity
  set T := C * j + S + 1
  have hmeas : Measurable fun x : Fin n → ℕ => ENNReal.ofReal (z ^ (∑ v ∈ J, x v)) :=
    Measurable.of_discrete
  have hmk := mul_meas_ge_le_lintegral₀ (μ := ν) hmeas.aemeasurable (ENNReal.ofReal (z ^ T))
  have hsub : {x : Fin n → ℕ | T ≤ ∑ v ∈ J, x v} ⊆
      {x | ENNReal.ofReal (z ^ T) ≤ ENNReal.ofReal (z ^ (∑ v ∈ J, x v))} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hz1 hx)
  have h1 : ENNReal.ofReal (z ^ T) * ν {x | T ≤ ∑ v ∈ J, x v} ≤
      ENNReal.ofReal (D * Real.exp (lam * j * (z - 1))) :=
    (mul_le_mul_right (measure_mono hsub) _).trans (hmk.trans (henv J z hz1))
  rw [ENNReal.ofReal_div_of_pos hzpos, ENNReal.le_div_iff_mul_le]
  · rw [mul_comm]; exact h1
  · left; simpa using hzpos
  · left; exact ENNReal.ofReal_ne_top

theorem P3 : Spec.P3_statement := by
  intro n C S lam D ν hν hl hlC hD henv
  classical
  set E := {x : Fin n → ℕ | S < ∑ v, (x v - C)} with hE
  set Js := (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.Nonempty) with hJs
  set A : Finset (Fin n) → Set (Fin n → ℕ) :=
    fun J => {x | C * J.card + S + 1 ≤ ∑ v ∈ J, x v} with hA
  set b : ℕ → ℝ := fun j => D * Real.exp (lam * j * (Spec.subsetZ C lam S j - 1)) /
        Spec.subsetZ C lam S j ^ (C * j + S + 1) with hb
  have hsubset : E ⊆ ⋃ J ∈ Js, A J := by
    intro x hx
    have hx : S < ∑ v, (x v - C) := hx
    set J : Finset (Fin n) := Finset.univ.filter (fun v => C < x v) with hJ
    have hsum : ∑ v, (x v - C) = ∑ v ∈ J, (x v - C) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => C < x v)]
      have : ∑ v ∈ Finset.univ.filter (fun v => ¬ C < x v), (x v - C) = 0 :=
        Finset.sum_eq_zero (fun v hv => by
          simp only [Finset.mem_filter] at hv; omega)
      rw [this, add_zero]
    have hne : J.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      have h0 : ∑ v, (x v - C) = 0 := by rw [hsum, h]; rfl
      omega
    have hJx : ∑ v ∈ J, x v = ∑ v ∈ J, (x v - C) + C * J.card := by
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun v hv => ?_)
      simp only [hJ, Finset.mem_filter] at hv
      omega
    simp only [Set.mem_iUnion]
    refine ⟨J, ?_, ?_⟩
    · simp [hJs, hne]
    · simp only [hA, Set.mem_setOf_eq]
      omega
  have hb0 : ∀ j, 0 ≤ b j := by
    intro j
    simp only [hb, Spec.subsetZ]
    have : (0:ℝ) ≤ ((C * j + S + 1 : ℕ) : ℝ) / (lam * j) := by
      apply div_nonneg (by positivity)
      exact mul_nonneg hl.le (Nat.cast_nonneg _)
    positivity
  have h2 : ν E ≤ ∑ J ∈ Js, ENNReal.ofReal (b J.card) := by
    calc ν E ≤ ν (⋃ J ∈ Js, A J) := measure_mono hsubset
      _ ≤ ∑ J ∈ Js, ν (A J) := measure_biUnion_finset_le _ _
      _ ≤ _ := Finset.sum_le_sum (fun J hJ => by
          have hne : J.Nonempty := by simpa [hJs] using hJ
          exact P3_bd n C S lam D ν hν hl hlC henv J hne)
  have h3 : ∑ J ∈ Js, b J.card = ∑ j ∈ Finset.Icc 1 n, (n.choose j : ℝ) * b j := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Js) (t := Finset.Icc 1 n) (g := Finset.card)
      (fun J hJ => by
        have hne : J.Nonempty := by simpa [hJs] using hJ
        simp only [Finset.mem_Icc]
        exact ⟨Finset.card_pos.mpr hne, by simpa using Finset.card_le_univ J⟩)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have : Js.filter (fun J => J.card = j) = Finset.powersetCard j Finset.univ := by
      ext J
      simp only [hJs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Finset.card_pos.mp (by omega), h⟩
    rw [this, Finset.sum_congr rfl (g := fun _ => b j) (fun J hJ => by
      rw [(Finset.mem_powersetCard.mp hJ).2]), Finset.sum_const, Finset.card_powersetCard]
    simp
  have h4 : ν E ≤ ENNReal.ofReal (∑ j ∈ Finset.Icc 1 n, (n.choose j : ℝ) * b j) := by
    refine h2.trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun J _ => hb0 _), h3]
  have h5 : ν E ≤ 1 := prob_le_one
  unfold Spec.Bsub
  have hsum : D * ∑ j ∈ Finset.Icc 1 n,
      (n.choose j : ℝ) * Real.exp (lam * j * (Spec.subsetZ C lam S j - 1)) /
        Spec.subsetZ C lam S j ^ (C * j + S + 1) =
      ∑ j ∈ Finset.Icc 1 n, (n.choose j : ℝ) * b j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hb]; ring
  rw [hsum]
  rcases le_total 1 (∑ j ∈ Finset.Icc 1 n, (n.choose j : ℝ) * b j) with h | h
  · rw [min_eq_left h]; simpa using h5
  · rw [min_eq_right h]; exact h4

end RebuildBound
