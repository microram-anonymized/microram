import RebuildBound.Proofs.ShadowLaw.Unit
import RebuildBound.Spec.P8c

/-!
# ShadowLaw: heterogeneous bridge and block counts (from P11fg)

Moved from the d = 2 chain (`P11fg`); namespace `RebuildBound.P11fgProof` kept.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace RebuildBound.P11fgProof
open RebuildBound.Spec RebuildBound.P11dProof
lemma cp_law {κ : Type} [Fintype κ] [DecidableEq κ] {A : Type} [Fintype A] [Nonempty A]
    (d : A → κ) : compoundPoisson 1 (unitLaw (law d)) = poissonVec (law d) := by
  rw [RebuildBound.P5b_split 1 _ (sum_law _)]
  simp

section Hetero
variable {κ : Type} [Fintype κ] [DecidableEq κ] {A : Type} [Fintype A]
lemma prob_ofFn (n : ℕ) (d : Fin n → A → κ) [Nonempty A] :
    IsProbabilityMeasure (convList (List.ofFn fun i => unitLaw (law (d i)))) := by
  induction n with
  | zero => simp only [List.ofFn_zero, convList]; infer_instance
  | succ m ihm =>
    rw [List.ofFn_succ, convList]
    haveI := unitLaw_prob (law (d 0)) (sum_law _)
    haveI := ihm (fun i => d i.succ)
    infer_instance

lemma bridgeH [Nonempty A] (n : ℕ) (d : Fin n → A → κ) (F : (κ → ℕ) → ℝ≥0∞) :
    ∫⁻ v, F v ∂(convList (List.ofFn fun i => unitLaw (law (d i)))) =
      ((Fintype.card A : ℝ≥0∞) ^ n)⁻¹ * ∑ g : Fin n → A, F (∑ i, unitVec (d i (g i))) := by
  induction n generalizing F with
  | zero => simp [convList, lintegral_dirac]
  | succ n ih =>
    haveI := prob_ofFn n (fun i => d i.succ)
    rw [List.ofFn_succ, convList, Measure.lintegral_conv Measurable.of_discrete,
      lintegral_unitLaw_law]
    simp_rw [ih]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => A)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [pow_succ', ENNReal.mul_inv (by simp) (by simp), mul_assoc]
    simp only [Finset.mul_sum]

/-- Turn the word average of a sum of per-key unit vectors into the
heterogeneous convolution law. Per-key destination and geometry premises are
supplied by the caller. -/
lemma wordAvg_bridgeH {K : Type} [Fintype K] [DecidableEq K] {b : ℕ}
    (d : K → Bits b → κ) (F : (κ → ℕ) → ℝ≥0∞) :
    wordAvg (fun h : K → Bits b => F (∑ x, unitVec (d x (h x)))) =
      ∫⁻ v, F v ∂(convList (List.ofFn fun i =>
        unitLaw (law (d ((Fintype.equivFin K).symm i))))) := by
  rw [bridgeH]
  let e := (Fintype.equivFin K).arrowCongr (Equiv.refl (Bits b))
  rw [RebuildBound.NetworkAverage.wordAvg_equiv e.symm, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  congr 1
  simpa [e, Equiv.arrowCongr_apply] using (Equiv.sum_comp (Fintype.equivFin K).symm
    (fun x => unitVec (d x ((e.symm h) x)))).symm

end Hetero
section PoissonH
variable {κ : Type} [Fintype κ]
lemma convList_ofFn_poissonVec (n : ℕ) (ν : Fin (n + 1) → κ → ℝ≥0) :
    convList (List.ofFn fun i => poissonVec (ν i)) = poissonVec (∑ i, ν i) := by
  induction n with
  | zero =>
    simp only [List.ofFn_succ, List.ofFn_zero, convList, Fin.sum_univ_succ, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero]
    exact Measure.conv_dirac_zero _
  | succ n ih =>
    rw [List.ofFn_succ, convList, ih (fun i => ν i.succ), RebuildBound.P5b_conv,
      Fin.sum_univ_succ (f := ν)]

lemma poisson_chainH (f : (κ → ℕ) → ℝ≥0∞) (hf : Monotone f) (n : ℕ) (ν : Fin n → κ → ℝ≥0)
    (lam : ℝ≥0) (h : ∀ V, ∑ i, ν i V ≤ lam) :
    ∫⁻ v, f v ∂(convList (List.ofFn fun i => poissonVec (ν i))) ≤
      ∫⁻ v, f v ∂(poissonVec (fun _ => lam)) := by
  cases n with
  | zero =>
    simp only [List.ofFn_zero, convList]
    rw [lintegral_dirac]
    calc f 0 = ∫⁻ _, f 0 ∂(poissonVec (fun _ => lam)) := by simp
      _ ≤ ∫⁻ v, f v ∂(poissonVec (fun _ => lam)) :=
          lintegral_mono fun y => hf fun i => Nat.zero_le (y i)
  | succ n =>
    rw [convList_ofFn_poissonVec]
    exact RebuildBound.P5b_pad f hf _ _ (fun V => by simpa [Finset.sum_apply] using h V)

end PoissonH
section G
variable {K : Type} [Fintype K] {b : ℕ}
/-- A key's destination from its start `p` and word `w`. -/
def dG (lo : ℕ) (p w : Bits b) : Bits b := fun i => if i.val < lo + 1 then w i else p i

/-- The aligned block of `V`: every bucket agreeing with `V` above bit `lo + 1`. -/
def blk (lo : ℕ) (V : Bits b) : Finset (Bits b) :=
  Fintype.piFinset (fun i => if i.val < lo + 1 then Finset.univ else {V i})

lemma card_blk (lo : ℕ) (V : Bits b) : (blk lo V).card ≤ 2 ^ (lo + 1) := by
  unfold blk
  rw [Fintype.card_piFinset]
  have : ∀ i : Fin b, (if i.val < lo + 1 then Finset.univ else ({V i} : Finset Bool)).card =
      if i.val < lo + 1 then 2 else 1 := by
    intro i; split_ifs <;> simp
  simp only [this]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  have h := Fin.card_filter_val_lt (n := b) (m := lo + 1)
  rw [h]
  exact Nat.pow_le_pow_right (by norm_num : 0 < 2) (min_le_right _ _)

lemma fiber_le (lo : ℕ) (hlo : lo < b) (p V : Bits b) :
    (Finset.univ.filter (fun w => dG lo p w = V)).card ≤
      if p ∈ blk lo V then 2 ^ (b - (lo + 1)) else 0 := by
  by_cases h : p ∈ blk lo V
  · rw [if_pos h]
    have hsub : Finset.univ.filter (fun w => dG lo p w = V) ⊆
        Fintype.piFinset (fun i => if i.val < lo + 1 then ({V i} : Finset Bool) else Finset.univ) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      rw [Fintype.mem_piFinset]
      intro i
      by_cases hi : i.val < lo + 1
      · have := congrFun hw i
        simp [dG, hi] at this
        simp [hi, this]
      · simp [hi]
    refine (Finset.card_le_card hsub).trans ?_
    rw [Fintype.card_piFinset]
    have : ∀ i : Fin b, (if i.val < lo + 1 then ({V i} : Finset Bool) else Finset.univ).card =
        if i.val < lo + 1 then 1 else 2 := by
      intro i; split_ifs <;> simp
    simp only [this]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, one_mul]
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin b)))
      (fun i : Fin b => i.val < lo + 1)
    have h2 := Fin.card_filter_val_lt (n := b) (m := lo + 1)
    rw [h2, Finset.card_univ, Fintype.card_fin] at h1
    have : (Finset.univ.filter fun i : Fin b => ¬ i.val < lo + 1).card = b - (lo + 1) := by
      rw [min_eq_right (by omega)] at h1
      omega
    rw [this]
  · rw [if_neg h]
    refine le_of_eq (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun w _ hw => h ?_))
    unfold blk
    rw [Fintype.mem_piFinset]
    intro i
    by_cases hi : i.val < lo + 1
    · simp [hi]
    · have := congrFun hw i
      simp [dG, hi] at this
      simp [hi, this]

lemma sum_law_bound (lo : ℕ) (hlo : lo < b) (lam : ℝ≥0) (pos : K → Bits b)
    (hpos : ∀ v, ((Finset.univ.filter fun x => pos x = v).card : ℝ≥0) ≤ lam) (V : Bits b) :
    ∑ x, law (dG lo (pos x)) V ≤ lam := by
  classical
  unfold law
  have hA : (Fintype.card (Bits b) : ℝ≥0) = 2 ^ b := by simp [Bits]
  rw [← Finset.sum_div, hA, div_le_iff₀ (by positivity)]
  have hfib : ∀ x, ((Finset.univ.filter (fun w => dG lo (pos x) w = V)).card : ℝ≥0) ≤
      if pos x ∈ blk lo V then (2 : ℝ≥0) ^ (b - (lo + 1)) else 0 := by
    intro x
    have := fiber_le lo hlo (pos x) V
    split_ifs at this ⊢
    · exact_mod_cast this
    · simp_all
  have hcnt : ((Finset.univ.filter fun x => pos x ∈ blk lo V).card : ℝ≥0) ≤ 2 ^ (lo + 1) * lam := by
    have hU : (Finset.univ.filter fun x => pos x ∈ blk lo V) ⊆
        (blk lo V).biUnion (fun v => Finset.univ.filter fun x => pos x = v) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨pos x, hx, rfl⟩
    have h1 := (Finset.card_le_card hU).trans Finset.card_biUnion_le
    have h2 : (((Finset.univ.filter fun x => pos x ∈ blk lo V).card : ℕ) : ℝ≥0) ≤
        ∑ v ∈ blk lo V, ((Finset.univ.filter fun x => pos x = v).card : ℝ≥0) := by
      exact_mod_cast h1
    refine h2.trans ?_
    calc _ ≤ (blk lo V).card • lam := Finset.sum_le_card_nsmul _ _ _ (fun v _ => hpos v)
      _ ≤ 2 ^ (lo + 1) * lam := by
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_blk lo V) (zero_le' (α := ℝ≥0))
  calc ∑ x, ((Finset.univ.filter (fun w => dG lo (pos x) w = V)).card : ℝ≥0)
      ≤ ∑ x, (if pos x ∈ blk lo V then (2 : ℝ≥0) ^ (b - (lo + 1)) else 0) :=
        Finset.sum_le_sum fun x _ => hfib x
    _ = ((Finset.univ.filter fun x => pos x ∈ blk lo V).card : ℝ≥0) * 2 ^ (b - (lo + 1)) := by
        rw [← Finset.sum_filter]; simp
    _ ≤ (2 ^ (lo + 1) * lam) * 2 ^ (b - (lo + 1)) := mul_le_mul_of_nonneg_right hcnt (zero_le' (α := ℝ≥0))
    _ = lam * 2 ^ b := by
        rw [mul_comm (2 ^ (lo + 1) : ℝ≥0) lam, mul_assoc, ← pow_add]
        congr 2
        omega

end G
end RebuildBound.P11fgProof
