import RebuildBound.Proofs.X1
import RebuildBound.Proofs.P6
import RebuildBound.Spec.P11

/-!
# ShadowNet: terminal test per class (from P11c)

Moved from the d = 2 chain (`P11c`); namespace `RebuildBound.P11cProof` kept.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval
namespace RebuildBound.P11cProof
open RebuildBound.Spec RebuildBound.X1Proof RebuildBound.P6Proof
section Partial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
lemma sum_shadow_add_unitVec_sub (S : Finset ι) (x : States ι) (k : ι × Slot) :
    ∑ a ∈ S, (x + unitVec k) (a, .shadow) =
      ∑ a ∈ S, x (a, .shadow) + if (k.2 = .shadow ∧ k.1 ∈ S) then 1 else 0 := by
  obtain ⟨b, s⟩ := k
  simp only [add_unitVec_apply, Finset.sum_add_distrib]
  congr 1
  cases s
  · simp
  · simp [Finset.sum_ite_eq', eq_comm]

lemma terminal_sub (S : Finset ι) (g : ℕ → ℝ≥0∞) (hg : Monotone g)
    (hconv : ∀ n, g (n + 1) + g (n + 1) ≤ g (n + 2) + g n) :
    ClassT (fun _ : ι => (⊤ : ℕ∞)) (fun x : States ι => g (∑ a ∈ S, x (a, .shadow))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    exact hg (Finset.sum_le_sum fun a _ => hxy (a, .shadow))
  · intro x k l
    simp only [sum_shadow_add_unitVec_sub, ← add_assoc]
    generalize ∑ a ∈ S, x (a, .shadow) = n
    by_cases h1 : (k.2 = .shadow ∧ k.1 ∈ S) <;> by_cases h2 : (l.2 = .shadow ∧ l.1 ∈ S) <;>
      simp [h1, h2, add_comm]
    · rw [show 1 + (n + 1) = n + 2 by omega, add_comm (g n)]
      exact hconv n
  · intro x a _
    simp only [sum_shadow_add_unitVec_sub]
    by_cases h : a ∈ S
    · simpa [h] using hg (Nat.le_succ _)
    · simp [h]

end Partial
variable {b : ℕ}
lemma termTest_class (P : ℕ) (p : I) (L lo : ℕ) (R : Bits b) :
    ClassT (fun _ : Bits b => (⊤ : ℕ∞)) (termTest P p L lo R) ∧
      CountBounded (P : ℝ≥0∞) (termTest P p L lo R) := by
  refine ⟨?_, ?_⟩
  · refine RebuildBound.P6_mix (ι := Bits b) (Z := ℕ) (fun _ => ⊤) (fun e (x : States (Bits b)) =>
      (((e + ∑ v ∈ rangeHomes lo R, x (v, .shadow)) - L : ℕ) : ℝ≥0∞)) (binomial P p) ?_
      (fun x => Measurable.of_discrete)
    intro e
    refine terminal_sub _ (fun n => (((e + n) - L : ℕ) : ℝ≥0∞)) ?_ ?_
    · intro m n h
      show (((e + m - L : ℕ)) : ℝ≥0∞) ≤ ((e + n - L : ℕ) : ℝ≥0∞)
      exact_mod_cast (by omega : e + m - L ≤ e + n - L)
    · intro n
      exact_mod_cast (by omega : (e + (n + 1) - L) + (e + (n + 1) - L) ≤ (e + (n + 2) - L) + (e + n - L))
  · intro x
    unfold termTest
    calc _ ≤ ∫⁻ _, (P : ℝ≥0∞) + ∑ q, (x q : ℝ≥0∞) ∂(binomial P p) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_le_binomial P p] with e he
          have h1 : (((e + ∑ a ∈ rangeHomes lo R, x (a, .shadow)) - L : ℕ) : ℝ≥0∞) ≤
              ((e + ∑ a ∈ rangeHomes lo R, x (a, .shadow) : ℕ) : ℝ≥0∞) := by
            exact_mod_cast Nat.sub_le _ _
          refine h1.trans ?_
          have h2 : ∑ a ∈ rangeHomes lo R, x (a, .shadow) ≤ ∑ q, x q := by
            rw [sum_states]
            exact (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans
              (Finset.sum_le_sum fun a _ => Nat.le_add_left _ _)
          have h3 : e + ∑ a ∈ rangeHomes lo R, x (a, .shadow) ≤ P + ∑ q, x q := Nat.add_le_add he h2
          exact_mod_cast h3
      _ = _ := by simp

end RebuildBound.P11cProof
