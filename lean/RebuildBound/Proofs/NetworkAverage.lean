import RebuildBound.Spec.Prob.Network

/-! Shared averaging scaffolding; conditional laws remain in their network packages. -/
open scoped ENNReal
namespace RebuildBound.NetworkAverage
open RebuildBound.Spec

variable {K : Type} [Fintype K] [DecidableEq K] {b : ℕ}

lemma wordAvg_congr {F G : (K → Bits b) → ℝ≥0∞} (h : ∀ w, F w = G w) :
    wordAvg F = wordAvg G := by
  unfold wordAvg
  congr 1
  exact Finset.sum_congr rfl (fun w _ => h w)

lemma wordAvg_mono {F G : (K → Bits b) → ℝ≥0∞} (h : ∀ w, F w ≤ G w) :
    wordAvg F ≤ wordAvg G := by
  unfold wordAvg
  exact mul_le_mul_right (Finset.sum_le_sum fun w _ => h w) _

/-- Transport a word average along an equivalence of its finite sample space. -/
lemma wordAvg_equiv {A : Type} [Fintype A]
    (e : A ≃ (K → Bits b)) (F : (K → Bits b) → ℝ≥0∞) :
    wordAvg F = (Fintype.card A : ℝ≥0∞)⁻¹ * ∑ a, F (e a) := by
  unfold wordAvg
  rw [Fintype.card_congr e, e.sum_comp]

/-- Combine two independent uniform word averages using a joint sample space.
This is only finite-sum transport; conditional laws stay in their consumers. -/
lemma wordAvg_pair_equiv {A : Type} [Fintype A]
    (e : A ≃ (K → Bits b) × (K → Bits b))
    (F : (K → Bits b) → (K → Bits b) → ℝ≥0∞) :
    wordAvg (fun o => wordAvg (F o)) =
      (Fintype.card A : ℝ≥0∞)⁻¹ * ∑ a, F (e a).1 (e a).2 := by
  have hc : (Fintype.card A : ℝ≥0∞) =
      (Fintype.card (K → Bits b) : ℝ≥0∞) * Fintype.card (K → Bits b) := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  unfold wordAvg
  rw [Finset.mul_sum, hc]
  simp only [← mul_assoc]
  rw [← Finset.mul_sum, ENNReal.mul_inv (by simp) (by simp)]
  congr 1
  rw [← Fintype.sum_prod_type']
  exact (e.sum_comp (fun x => F x.1 x.2)).symm

/-- An involutive resampling of two word assignments transports a per-assignment
bound to their uniform averages. The caller supplies both the involution and the
conditional bound; no route validity or conditioning premise is hidden here. -/
lemma wordAvg_le_of_involution
    (swap : ((K → Bits b) × (K → Bits b)) → ((K → Bits b) × (K → Bits b)))
    (hswap : Function.Involutive swap) (F G : (K → Bits b) → ℝ≥0∞)
    (hbound : ∀ h, ∑ g, F (swap (h, g)).1 ≤ Fintype.card (K → Bits b) * G h) :
    wordAvg F ≤ wordAvg G := by
  have hN0 : (Fintype.card (K → Bits b) : ℝ≥0∞) ≠ 0 := by simp
  have hNt : (Fintype.card (K → Bits b) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have key : (Fintype.card (K → Bits b) : ℝ≥0∞) * ∑ h, F h ≤
      Fintype.card (K → Bits b) * ∑ h, G h := by
    calc (Fintype.card (K → Bits b) : ℝ≥0∞) * ∑ h, F h
        = ∑ q : (K → Bits b) × (K → Bits b), F q.1 := by
          rw [Fintype.sum_prod_type' (fun h (_ : K → Bits b) => F h), Finset.mul_sum]
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ q : (K → Bits b) × (K → Bits b), F (swap q).1 :=
          (Equiv.sum_comp (hswap.toPerm _) (fun q => F q.1)).symm
      _ = ∑ h, ∑ g, F (swap (h, g)).1 :=
          Fintype.sum_prod_type' (fun h g => F (swap (h, g)).1)
      _ ≤ ∑ h, (Fintype.card (K → Bits b) : ℝ≥0∞) * G h :=
          Finset.sum_le_sum fun h _ => hbound h
      _ = Fintype.card (K → Bits b) * ∑ h, G h := by rw [Finset.mul_sum]
  unfold wordAvg
  exact mul_le_mul_of_nonneg_left ((ENNReal.mul_le_mul_iff_right hN0 hNt).mp key) zero_le

end RebuildBound.NetworkAverage
