import RebuildBound.Proofs.ShadowLaw.Unit
import RebuildBound.Spec.P7
import RebuildBound.Spec.P8c

/-!
# P8c: per-home means (adaptation of P8a)

Route: the restricted stop-loss is directionally convex, monotone and finite, so P5a
replaces each key's unit law by its compound Poisson law, P5b_split makes that
`poissonVec (p i)`, P5b_conv adds the means along the list, and P5b_pad raises the
mean to `λ`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open RebuildBound.Spec

namespace RebuildBound.P8cProof

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private lemma coord_sum_le (J : Finset ι) (C : ℕ) (y y' : ι → ℕ) (h : y ≤ y') :
    ∑ v ∈ J, (y v - C) ≤ ∑ v ∈ J, (y' v - C) :=
  Finset.sum_le_sum fun v _ => by have : y v ≤ y' v := h v; omega

private lemma mono (J : Finset ι) (C S : ℕ) : Monotone (restrictedStopLoss J C S) := by
  intro y y' h
  unfold restrictedStopLoss
  have := coord_sum_le J C y y' h
  exact_mod_cast (by omega : ∑ v ∈ J, (y v - C) - S ≤ ∑ v ∈ J, (y' v - C) - S)

private lemma fin (J : Finset ι) (C S : ℕ) (y : ι → ℕ) : restrictedStopLoss J C S y ≠ ∞ :=
  ENNReal.natCast_ne_top _

private lemma dirconv (J : Finset ι) (C S : ℕ) : DirConvex (restrictedStopLoss J C S) := by
  intro x k l
  unfold restrictedStopLoss
  have hk : x ≤ x + unitVec k := fun v => by simp
  have hl : x ≤ x + unitVec l := fun v => by simp
  have hk' : x + unitVec k ≤ x + unitVec k + unitVec l := fun v => by simp
  have hl' : x + unitVec l ≤ x + unitVec k + unitVec l := by
    intro v; simp only [Pi.add_apply]; omega
  have h1 := coord_sum_le J C _ _ hk
  have h2 := coord_sum_le J C _ _ hl
  have h3 := coord_sum_le J C _ _ hk'
  have h4 := coord_sum_le J C _ _ hl'
  have h5 : ∑ v ∈ J, ((x + unitVec k) v - C) + ∑ v ∈ J, ((x + unitVec l) v - C) ≤
      ∑ v ∈ J, ((x + unitVec k + unitVec l) v - C) + ∑ v ∈ J, (x v - C) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    simp only [Pi.add_apply, unitVec]
    by_cases hkv : v = k <;> by_cases hlv : v = l <;> simp [hkv, hlv, Pi.single_apply] <;> omega
  rw [← Nat.cast_add, ← Nat.cast_add]
  exact_mod_cast (by omega : _)

private lemma poissonVec_zero : poissonVec (fun _ : ι => (0 : ℝ≥0)) = Measure.dirac 0 := by
  refine Measure.ext_of_singleton fun n => ?_
  rw [RebuildBound.P5bProof.poissonVec_apply]
  by_cases hn : n = 0
  · subst hn; simp
  · obtain ⟨k, hk⟩ : ∃ k, n k ≠ 0 := by
      by_contra hcon; push_neg at hcon; exact hn (funext hcon)
    rw [Finset.prod_eq_zero (Finset.mem_univ k)]
    · simp [Ne.symm hn]
    · simp [hk]

private lemma conv_formula (ps : List (ι → ℝ≥0)) (h : ∀ p ∈ ps, ∑ v, p v = 1) :
    convList (ps.map (compoundPoisson 1 ∘ unitLaw)) =
      poissonVec (fun v => (ps.map (fun p => p v)).sum) := by
  induction ps with
  | nil => simp [convList, poissonVec_zero]
  | cons p ps ih =>
    have hp := h p (by simp)
    rw [List.map_cons, convList, ih (fun q hq => h q (by simp [hq])), Function.comp_apply,
      RebuildBound.P5b_split 1 p hp, RebuildBound.P5b_conv]
    congr 1
    funext v
    simp

end RebuildBound.P8cProof

theorem RebuildBound.P8c : RebuildBound.Spec.P8c_statement := by
  intro ι _ _ J C S lam ps hsum hle
  open RebuildBound.P8cProof in
  have hprob : ∀ μ ∈ ps.map unitLaw, IsProbabilityMeasure μ := by
    intro μ hμ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hμ
    exact P11dProof.unitLaw_prob p (hsum p hp)
  have h1 := RebuildBound.P5a (restrictedStopLoss J C S) (RebuildBound.P8cProof.dirconv J C S)
    (RebuildBound.P8cProof.fin J C S) (ps.map unitLaw) hprob 0
  simp only [zero_add, List.map_map] at h1
  refine h1.trans ?_
  rw [RebuildBound.P8cProof.conv_formula ps hsum]
  exact RebuildBound.P5b_pad _ (RebuildBound.P8cProof.mono J C S) _ _ hle
