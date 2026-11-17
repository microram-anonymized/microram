import RebuildBound.Proofs.NetworkAverage
import RebuildBound.Proofs.ShadowNet.Fiber
import RebuildBound.Proofs.ShadowNet.Swap
import RebuildBound.Proofs.ShadowNet.Class

/-!
# ShadowNet: gluing word functions (from P11ab)

Moved from the d = 2 chain (`P11ab`); namespace `RebuildBound.P11abProof` kept.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval
namespace RebuildBound.P11abProof
open RebuildBound.Spec RebuildBound.P11aProof
variable {K : Type} [Fintype K] [DecidableEq K] {b : ℕ}
omit [DecidableEq K] in
lemma agree_symm {j : ℕ} {h h' : K → Bits b} (hh : AgreeBelow j h h') : AgreeBelow j h' h :=
  fun x i hi => (hh x i hi).symm

/-- Glue `h` below `j` with `g` above. -/
def glue (j : ℕ) (h g : K → Bits b) : K → Bits b :=
  fun x i => if i.val < j then h x i else g x i

lemma card_class_eq (j : ℕ) (h h' : K → Bits b) :
    (Finset.univ.filter (AgreeBelow j h)).card = (Finset.univ.filter (AgreeBelow j h')).card := by
  apply Finset.card_bij' (fun g _ => glue j h' g) (fun g _ => glue j h g)
  · intro g _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro x i hi
    simp [glue, hi]
  · intro g _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro x i hi
    simp [glue, hi]
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    funext x i
    by_cases hi : i.val < j
    · simp [glue, hi, hg x i hi]
    · simp [glue, hi]
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    funext x i
    by_cases hi : i.val < j
    · simp [glue, hi, hg x i hi]
    · simp [glue, hi]

lemma wordAvg_condAvg (j : ℕ) (F : (K → Bits b) → ℝ≥0∞) :
    wordAvg (fun h => condAvg j h F) = wordAvg F := by
  set h0 : K → Bits b := fun _ _ => false
  set N := (Finset.univ.filter (AgreeBelow j h0)).card
  have hN : ∀ h, (Finset.univ.filter (AgreeBelow j h)).card = N := fun h => card_class_eq j h h0
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by
    have : h0 ∈ Finset.univ.filter (AgreeBelow j h0) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro x i _; rfl
    exact_mod_cast (Finset.card_pos.mpr ⟨_, this⟩).ne'
  have hNt : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  unfold wordAvg condAvg
  congr 1
  simp_rw [hN]
  rw [← Finset.mul_sum]
  have swap : ∑ h : K → Bits b, ∑ h' ∈ Finset.univ.filter (AgreeBelow j h), F h' =
      ∑ h' : K → Bits b, (N : ℝ≥0∞) * F h' := by
    have e1 : ∀ h : K → Bits b, ∑ h' ∈ Finset.univ.filter (AgreeBelow j h), F h' =
        ∑ h', if AgreeBelow j h h' then F h' else 0 := fun h => by
      rw [Finset.sum_filter]
    simp_rw [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h' _ => ?_
    have : ∀ h : K → Bits b, (if AgreeBelow j h h' then F h' else 0) =
        if AgreeBelow j h' h then F h' else 0 := fun h => by
      by_cases hh : AgreeBelow j h h'
      · simp [hh, agree_symm hh]
      · have : ¬ AgreeBelow j h' h := fun h2 => hh (agree_symm h2)
        simp [hh, this]
    rw [Finset.sum_congr rfl fun h _ => this h]
    rw [← Finset.sum_filter, Finset.sum_const, hN, nsmul_eq_mul]
  rw [swap, ← Finset.mul_sum, ← mul_assoc, ENNReal.inv_mul_cancel hN0 hNt, one_mul]

lemma termTest_reads (P : ℕ) (p : I) (L lo : ℕ) (R : Bits b) :
    ∀ x y : States (Bits b), (∀ v, InRange lo R v → ∀ s, x (v, s) = y (v, s)) →
      termTest P p L lo R x = termTest P p L lo R y := by
  intro x y hxy
  unfold termTest
  congr 1
  funext e
  have : ∑ v ∈ rangeHomes lo R, x (v, .shadow) = ∑ v ∈ rangeHomes lo R, y (v, .shadow) :=
    Finset.sum_congr rfl fun v hv => hxy v (by simpa [rangeHomes] using hv) _
  rw [this]

end RebuildBound.P11abProof
