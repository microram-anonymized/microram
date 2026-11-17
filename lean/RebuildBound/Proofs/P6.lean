import RebuildBound.Proofs.X1
import RebuildBound.Spec.P6

/-!
# P6: closure of class 𝒯, extended

Measure-based throughout (`lintegral`, `binomial`); no obstacle beyond reusing X1's
binomial lemmas (`ae_le_binomial`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P6Proof

open RebuildBound.Spec RebuildBound.X1Proof

lemma sum_slot {M : Type*} [AddCommMonoid M] (f : Slot → M) : ∑ s, f s = f .main + f .shadow := by
  show Finset.sum {Slot.main, Slot.shadow} f = _
  simp

lemma sum_states {ι : Type*} [Fintype ι] {M : Type*} [AddCommMonoid M] (f : ι × Slot → M) :
    ∑ q, f q = ∑ a, (f (a, .main) + f (a, .shadow)) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => sum_slot _

variable {ι : Type} [DecidableEq ι]

lemma setNode_self (a : ι) (x : States ι) : setNode a (x (a, .main)) (x (a, .shadow)) x = x := by
  funext ⟨b, s⟩
  by_cases hb : b = a
  · subst hb; cases s <;> simp
  · rw [setNode_of_ne _ _ _ _ hb]

lemma sum_capAt [Fintype ι] (a : ι) (C : ℕ) (x : States ι) :
    ∑ q, capAt a C x q = ∑ q, x q := by
  rw [sum_states, sum_states]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    ← Finset.add_sum_erase _ (fun a => x (a, .main) + x (a, .shadow)) (Finset.mem_univ a)]
  congr 1
  · simp only [capAt_main, capAt_shadow]; omega
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hb' : b ≠ a := Finset.ne_of_mem_erase hb
    rw [capAt_of_ne a C x (q := (b, .main)) hb', capAt_of_ne a C x (q := (b, .shadow)) hb']

lemma sum_sumAlong {κ : Type} [Fintype κ] [Fintype ι] (parent : κ → ι) (x : States κ) :
    ∑ q, sumAlong parent x q = ∑ q, x q := by
  rw [sum_states, sum_states]
  simp only [sumAlong]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_fiberwise Finset.univ parent (fun b => x (b, .main))
  · exact Finset.sum_fiberwise Finset.univ parent (fun b => x (b, .shadow))

lemma mainEmbed_add_unitVec (N : ι → ℕ) (a : ι) :
    mainEmbed (N + unitVec a) = mainEmbed N + unitVec (a, Slot.main) := by
  funext ⟨b, s⟩
  cases s
  · by_cases h : b = a
    · subst h; simp [mainEmbed, unitVec_apply]
    · simp [mainEmbed, unitVec_apply, h]
  · simp [mainEmbed, unitVec_apply]

omit [DecidableEq ι] in
lemma sum_mainEmbed [Fintype ι] (N : ι → ℕ) : ∑ q, (mainEmbed N q : ℝ≥0∞) = ∑ a, (N a : ℝ≥0∞) := by
  rw [sum_states]; simp [mainEmbed]

end RebuildBound.P6Proof

open RebuildBound.Spec RebuildBound.X1Proof RebuildBound.P6Proof

theorem RebuildBound.P6_thinAll : RebuildBound.Spec.P6_thinAll_statement := by
  intro ι _ c φ l p hφ
  induction l with
  | nil => exact hφ
  | cons b l ih => exact RebuildBound.X1_thin c _ b (p b) ih

theorem RebuildBound.P6_capAll : RebuildBound.Spec.P6_capAll_statement := by
  intro ι _ φ l C
  induction l generalizing φ with
  | nil => exact id
  | cons b l ih =>
    intro hφ
    have h := RebuildBound.X1_cap (fun _ => (⊤ : ℕ∞)) φ b C hφ le_top
    simp only [Function.update_eq_self_iff.mpr rfl] at h
    exact ih (φ ∘ capAt b C) h

theorem RebuildBound.P6_mix : RebuildBound.Spec.P6_mix_statement := by
  intro ι Z _ _ c φ ν hφ hm
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    exact lintegral_mono fun z => (hφ z).mono hxy
  · intro x k l
    simp only
    rw [← lintegral_add_left (hm _), ← lintegral_add_left (hm _)]
    exact lintegral_mono fun z => (hφ z).dirConvex x k l
  · intro x a ha
    exact lintegral_mono fun z => (hφ z).main_le_shadow x a ha

theorem RebuildBound.P6_bound : RebuildBound.Spec.P6_bound_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ι _ _ K φ a C h x
    refine (h _).trans ?_
    simp only [← Nat.cast_sum, sum_capAt, le_refl]
  · intro ι _ _ K φ a p h x
    have hx : ∀ m ≤ x (a, .main), ∀ r ≤ x (a, .shadow),
        φ (setNode a m r x) ≤ K + ∑ q, (x q : ℝ≥0∞) := by
      intro m hm r hr
      refine (h _).trans ?_
      gcongr with q
      have := setNode_mono a hm hr (le_refl x)
      rw [setNode_self] at this
      exact_mod_cast this q
    unfold thinAt
    calc _ ≤ ∫⁻ _, K + ∑ q, (x q : ℝ≥0∞) ∂(binomial (x (a, .main)) p) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_le_binomial (x (a, .main)) p] with m hm
          calc _ ≤ ∫⁻ _, K + ∑ q, (x q : ℝ≥0∞) ∂(binomial (x (a, .shadow)) p) := by
                refine lintegral_mono_ae ?_
                filter_upwards [ae_le_binomial (x (a, .shadow)) p] with r hr
                exact hx m hm r hr
            _ = _ := by simp
      _ = _ := by simp
  · intro κ ι _ _ _ _ K parent φ h x
    refine (h _).trans ?_
    simp only [← Nat.cast_sum, sum_sumAlong, le_refl]
  · intro ι Z _ _ K φ ν hν hK h hm x
    calc _ ≤ ∫⁻ z, K z + ∑ q, (x q : ℝ≥0∞) ∂ν := lintegral_mono fun z => h z x
      _ = _ := by rw [lintegral_add_right _ measurable_const]; simp

theorem RebuildBound.P6_embed : RebuildBound.Spec.P6_embed_statement := by
  intro ι _ _ φ K hφ hK
  refine ⟨?_, ?_, ?_⟩
  · intro N N' h
    refine hφ.mono fun ⟨b, s⟩ => ?_
    cases s
    · exact h b
    · exact le_rfl
  · intro N k l
    simp only [Function.comp_apply, mainEmbed_add_unitVec]
    exact hφ.dirConvex _ _ _
  · intro N
    simpa [sum_mainEmbed] using hK (mainEmbed N)

theorem RebuildBound.P6_terminal : RebuildBound.Spec.P6_terminal_statement := by
  intro ι _ _ P p L
  refine ⟨?_, ?_⟩
  · have := RebuildBound.P6_mix (ι := ι) (Z := ℕ) (fun _ => ⊤) (fun e (x : States ι) =>
      (((e + ∑ a, x (a, .shadow)) - L : ℕ) : ℝ≥0∞)) (binomial P p) ?_ (fun x => Measurable.of_discrete)
    · exact this
    · intro e
      refine RebuildBound.X1_terminal (fun n => (((e + n) - L : ℕ) : ℝ≥0∞)) ?_ ?_
      · intro m n h
        show (((e + m - L : ℕ)) : ℝ≥0∞) ≤ ((e + n - L : ℕ) : ℝ≥0∞)
        exact_mod_cast (by omega : e + m - L ≤ e + n - L)
      · intro n
        exact_mod_cast (by omega : (e + (n + 1) - L) + (e + (n + 1) - L) ≤ (e + (n + 2) - L) + (e + n - L))
  · intro x
    unfold earlyStopLoss
    calc _ ≤ ∫⁻ _, (P : ℝ≥0∞) + ∑ q, (x q : ℝ≥0∞) ∂(binomial P p) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_le_binomial P p] with e he
          have h1 : (((e + ∑ a, x (a, .shadow)) - L : ℕ) : ℝ≥0∞) ≤
              ((e + ∑ a, x (a, .shadow) : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.sub_le _ _
          refine h1.trans ?_
          have h2 : ∑ a, x (a, .shadow) ≤ ∑ q, x q := by
            rw [sum_states]
            exact Finset.sum_le_sum fun a _ => Nat.le_add_left _ _
          have h3 : e + ∑ a, x (a, .shadow) ≤ P + ∑ q, x q := Nat.add_le_add he h2
          exact_mod_cast h3
      _ = _ := by simp
