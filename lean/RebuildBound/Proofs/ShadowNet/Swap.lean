import RebuildBound.Spec.P11
import RebuildBound.Proofs.X1
import RebuildBound.Proofs.NetworkAverage

/-!
# ShadowNet: binomial counts and swaps (from P11b)

Moved from the d = 2 chain (`P11b`); namespace `RebuildBound.P11bProof` kept.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval
namespace RebuildBound.P11bProof
open RebuildBound.Spec RebuildBound.X1Proof
section Count
variable {K α : Type*} [Fintype K] [DecidableEq K] [Fintype α]
/-- Resampling one coordinate preserves the sum over all assignments. -/
lemma sum_sum_update (F : (K → α) → ℝ≥0∞) (a : K) :
    ∑ g : K → α, ∑ w : α, F (Function.update g a w) = Fintype.card α * ∑ g, F g := by
  have hinv : Function.Involutive
      (fun q : (K → α) × α => (Function.update q.1 a q.2, q.1 a)) := by
    rintro ⟨g, w⟩
    simp
  calc ∑ g : K → α, ∑ w : α, F (Function.update g a w)
      = ∑ q : (K → α) × α, F (Function.update q.1 a q.2) :=
        (Fintype.sum_prod_type' (fun g w => F (Function.update g a w))).symm
    _ = ∑ q : (K → α) × α, F q.1 := Equiv.sum_comp (hinv.toPerm _) (fun q => F q.1)
    _ = ∑ g : K → α, ∑ _w : α, F g := Fintype.sum_prod_type' (fun g _ => F g)
    _ = Fintype.card α * ∑ g, F g := by
        rw [Finset.mul_sum]
        simp [Finset.sum_const, nsmul_eq_mul]

lemma card_filter_not_eq (Q : α → Prop) [DecidablePred Q] (p : I)
    (hQ : ((Finset.univ.filter Q).card : ℝ≥0∞) = Fintype.card α * pe p) :
    ((Finset.univ.filter (fun w => ¬ Q w)).card : ℝ≥0∞) = Fintype.card α * qe p := by
  have h1 : ((Finset.univ.filter Q).card : ℝ≥0∞) + (Finset.univ.filter (fun w => ¬ Q w)).card
      = Fintype.card α := by
    rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have h2 : (Fintype.card α : ℝ≥0∞) * pe p + Fintype.card α * qe p = Fintype.card α := by
    rw [← mul_add, add_comm, qe_add_pe, mul_one]
  have h3 := h1.trans h2.symm
  rw [hQ] at h3
  exact (ENNReal.add_right_inj (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    ENNReal.ofReal_ne_top)).mp h3

/-- **The counting lemma.** For independent uniform words, the number of keys of
`E` whose word satisfies `Q` is `Bin(|E|, p)`, where `p` is the probability of
`Q`. -/
lemma sum_count_binomial [Nonempty α] (Q : α → Prop) [DecidablePred Q] (p : I)
    (hQ : ((Finset.univ.filter Q).card : ℝ≥0∞) = Fintype.card α * pe p)
    (E : Finset K) (f : ℕ → ℝ≥0∞) :
    ∑ g : K → α, f ((E.filter (fun x => Q (g x))).card) =
      Fintype.card (K → α) * ∫⁻ e, f e ∂(binomial E.card p) := by
  have hnQ := card_filter_not_eq Q p hQ
  induction E using Finset.induction_on generalizing f with
  | empty =>
    simp [binomial_zero, lintegral_dirac, Finset.sum_const, nsmul_eq_mul]
  | insert a E ha ih =>
    have hN0 : (Fintype.card α : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
    have hNt : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hcount : ∀ (g : K → α) (w : α),
        f ((insert a E).filter (fun x => Q (Function.update g a w x))).card =
          if Q w then f ((E.filter (fun x => Q (g x))).card + 1)
          else f (E.filter (fun x => Q (g x))).card := by
      intro g w
      have hE : E.filter (fun x => Q (Function.update g a w x)) =
          E.filter (fun x => Q (g x)) := by
        apply Finset.filter_congr
        intro x hx
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hx ha)]
      rw [Finset.filter_insert, Function.update_self, hE]
      split_ifs
      · rw [Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.mp h).1)]
      · rfl
    rw [← ENNReal.mul_right_inj hN0 hNt]
    calc (Fintype.card α : ℝ≥0∞) * ∑ g : K → α, f ((insert a E).filter (fun x => Q (g x))).card
        = ∑ g : K → α, ∑ w : α,
            f ((insert a E).filter (fun x => Q (Function.update g a w x))).card :=
          (sum_sum_update (fun g => f ((insert a E).filter (fun x => Q (g x))).card) a).symm
      _ = ∑ g : K → α, (((Finset.univ.filter Q).card : ℝ≥0∞) *
              f ((E.filter (fun x => Q (g x))).card + 1) +
            ((Finset.univ.filter (fun w => ¬ Q w)).card : ℝ≥0∞) *
              f (E.filter (fun x => Q (g x))).card) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.sum_congr rfl fun w _ => hcount g w, Finset.sum_ite, Finset.sum_const,
            Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      _ = ((Finset.univ.filter Q).card : ℝ≥0∞) *
              ∑ g : K → α, f ((E.filter (fun x => Q (g x))).card + 1) +
            ((Finset.univ.filter (fun w => ¬ Q w)).card : ℝ≥0∞) *
              ∑ g : K → α, f (E.filter (fun x => Q (g x))).card := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = (Fintype.card α : ℝ≥0∞) *
            (Fintype.card (K → α) * ∫⁻ e, f e ∂(binomial (insert a E).card p)) := by
          rw [ih (fun e => f (e + 1)), ih f, hQ, hnQ, Finset.card_insert_of_notMem ha,
            lintegral_binomial_succ]
          ring

end Count
lemma card_inRange {b : ℕ} (lo : ℕ) (hlo : lo ≤ b) (R : Bits b) :
    (Finset.univ.filter (InRange lo R)).card = 2 ^ lo := by
  have h : Finset.univ.filter (InRange lo R) =
      Fintype.piFinset (fun i : Fin b => if lo ≤ i.val then {R i} else Finset.univ) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, InRange]
    refine forall_congr' fun i => ?_
    split_ifs with hi <;> simp [hi]
  rw [h, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_singleton, Finset.card_univ, Fintype.card_bool]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  simp only [not_le]
  rw [Fin.card_filter_val_lt, min_eq_right hlo]

lemma card_inRange_eq {b : ℕ} (lo : ℕ) (hlo : lo ≤ b) (R : Bits b) :
    ((Finset.univ.filter (InRange lo R)).card : ℝ≥0∞) =
      Fintype.card (Bits b) * pe (halfPow (b - lo)) := by
  rw [card_inRange lo hlo R, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pe,
    ← ENNReal.ofReal_natCast (2 ^ lo), ← ENNReal.ofReal_natCast (2 ^ b),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  show ((2 ^ lo : ℕ) : ℝ) = ((2 ^ b : ℕ) : ℝ) * (1 / 2) ^ (b - lo)
  obtain ⟨d, rfl⟩ : ∃ d, b = lo + d := ⟨b - lo, by omega⟩
  rw [Nat.add_sub_cancel_left]
  push_cast
  rw [pow_add, mul_assoc, ← mul_pow]
  norm_num

section Route
variable {K : Type} [DecidableEq K] {b : ℕ}
/-- Bits below `lo` from `u`, the others from `w`. -/
def mix (lo : ℕ) (u w : Bits b) : Bits b := fun i => if i.val < lo then u i else w i

/-- For the keys of `E`, replace the bits `≥ lo` of `h` by those of `g`. -/
def sw (lo : ℕ) (E : Finset K) (h g : K → Bits b) : K → Bits b :=
  fun x => if x ∈ E then mix lo (h x) (g x) else h x

lemma agreeBelow_sw (lo : ℕ) (E : Finset K) (h g : K → Bits b) :
    AgreeBelow lo h (sw lo E h g) := by
  intro x i hi
  by_cases hx : x ∈ E <;> simp [sw, mix, hx, hi]

lemma inRange_mix (lo : ℕ) (R u w : Bits b) : InRange lo R (mix lo u w) ↔ InRange lo R w := by
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  simp [mix, not_lt.mpr hi]

lemma sw_sw_fst (lo : ℕ) (E : Finset K) (h g : K → Bits b) :
    sw lo E (sw lo E h g) (sw lo E g h) = h := by
  funext x i
  by_cases hx : x ∈ E <;> by_cases hi : i.val < lo <;> simp [sw, mix, hx, hi]

lemma sw_sw_snd (lo : ℕ) (E : Finset K) (h g : K → Bits b) :
    sw lo E (sw lo E g h) (sw lo E h g) = g := by
  funext x i
  by_cases hx : x ∈ E <;> by_cases hi : i.val < lo <;> simp [sw, mix, hx, hi]

/-- The swap of the bits `≥ lo` of the early keys between two assignments. -/
def swp (lo : ℕ) (early : (K → Bits b) → Finset K) (q : (K → Bits b) × (K → Bits b)) :
    (K → Bits b) × (K → Bits b) :=
  (sw lo (early q.1) q.1 q.2, sw lo (early q.1) q.2 q.1)

lemma swp_involutive (lo : ℕ) (early : (K → Bits b) → Finset K)
    (hearly : ∀ h h', AgreeBelow lo h h' → early h = early h') :
    Function.Involutive (swp lo early) := by
  rintro ⟨h, g⟩
  have hE : early (sw lo (early h) h g) = early h :=
    (hearly _ _ (agreeBelow_sw lo (early h) h g)).symm
  simp only [swp]
  rw [hE, sw_sw_fst, sw_sw_snd]

variable {C : ℕ} {pos : K → Bits b} {ρ : BlindRoute K b}
end Route
end RebuildBound.P11bProof
