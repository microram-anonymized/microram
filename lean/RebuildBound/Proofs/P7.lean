import RebuildBound.Spec.P7
import Mathlib.MeasureTheory.Integral.Marginal

/-!
# P7 from P7alg

Law of the restricted excess via `lmarginal` induction on `J` (`P7aux.law`),
then the split at `K` and the moment generating function at 2. No Mathlib
obstacles; everything is in `ℝ≥0∞` tsums.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace RebuildBound
namespace P7aux

lemma conv_swap (a b h : ℕ → ℝ≥0∞) :
    ∑' m, a m * ∑' k, h (m + k) * b k =
      ∑' n, h n * ∑ ij ∈ antidiagonal n, b ij.1 * a ij.2 := by
  have h1 : ∑' m, a m * ∑' k, h (m + k) * b k =
      ∑' p : ℕ × ℕ, h (p.1 + p.2) * (b p.1 * a p.2) := by
    rw [ENNReal.tsum_prod (f := fun k m => h (k + m) * (b k * a m)), ENNReal.tsum_comm]
    refine tsum_congr fun k => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [Nat.add_comm k m]; ring
  rw [h1, ← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq]
  rw [ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _), ← ENNReal.tsum_mul_left]
  refine tsum_congr fun s => ?_
  have : (s.1.1 + s.1.2) = n := Finset.mem_antidiagonal.mp s.2
  change h (s.1.1 + s.1.2) * (b s.1.1 * a s.1.2) = _
  rw [this]
  

noncomputable def qE (C : ℕ) (lam : ℝ) (m : ℕ) : ℝ≥0∞ := ENNReal.ofReal (Spec.excessPmf C lam m)

lemma lint_pois (r : ℝ≥0) (h : ℕ → ℝ≥0∞) :
    ∫⁻ n, h n ∂(poissonMeasure r) =
      ∑' n, ENNReal.ofReal (Real.exp (-r) * r ^ n / (n.factorial : ℝ)) * h n := by
  rw [poissonMeasure, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

lemma regroup (C : ℕ) (r : ℝ≥0) (h : ℕ → ℝ≥0∞) :
    ∑' n, ENNReal.ofReal (Real.exp (-r) * r ^ n / (n.factorial : ℝ)) * h (n - C) =
      ∑' m, qE C r m * h m := by
  have hnn : ∀ n : ℕ, 0 ≤ Real.exp (-(r:ℝ)) * (r:ℝ) ^ n / (n.factorial : ℝ) := fun n => by positivity
  have e1 := ENNReal.summable.sum_add_tsum_nat_add' (f := fun n : ℕ =>
    ENNReal.ofReal (Real.exp (-r) * r ^ n / (n.factorial : ℝ)) * h (n - C)) (k := C + 1)
  have e2 := ENNReal.summable.sum_add_tsum_nat_add' (f := fun m : ℕ => qE C r m * h m) (k := 1)
  rw [← e1, ← e2]
  congr 1
  · have : ∀ n ∈ range (C + 1), ENNReal.ofReal (Real.exp (-(r:ℝ)) * (r:ℝ) ^ n / (n.factorial : ℝ)) *
        h (n - C) = ENNReal.ofReal (Real.exp (-(r:ℝ)) * (r:ℝ) ^ n / (n.factorial : ℝ)) * h 0 := by
      intro n hn
      have : n - C = 0 := by have := Finset.mem_range.mp hn; omega
      rw [this]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun n _ => hnn n)]
    simp [qE, Spec.excessPmf]
  · refine tsum_congr fun j => ?_
    have : j + (C + 1) - C = j + 1 := by omega
    have h2 : j + (C + 1) = C + (j + 1) := by omega
    simp only [qE, Spec.excessPmf, Spec.seriesW, h2, Nat.add_sub_cancel_left]


noncomputable def PE (C : ℕ) (lam : ℝ) (n k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Spec.cauchyPow (Spec.excessPmf C lam) n k)

lemma excessPmf_nonneg (C : ℕ) {lam : ℝ} (hl : 0 ≤ lam) (m : ℕ) : 0 ≤ Spec.excessPmf C lam m := by
  cases m with
  | zero => exact Finset.sum_nonneg fun z _ => by positivity
  | succ j => unfold Spec.excessPmf Spec.seriesW; positivity

lemma cauchyPow_nonneg (C : ℕ) {lam : ℝ} (hl : 0 ≤ lam) (n k : ℕ) :
    0 ≤ Spec.cauchyPow (Spec.excessPmf C lam) n k := by
  induction n generalizing k with
  | zero => unfold Spec.cauchyPow; split_ifs <;> norm_num
  | succ n ih =>
    unfold Spec.cauchyPow
    exact Finset.sum_nonneg fun ij _ => mul_nonneg (ih _) (excessPmf_nonneg C hl _)

lemma PE_zero (C : ℕ) (lam : ℝ) (k : ℕ) : PE C lam 0 k = if k = 0 then 1 else 0 := by
  unfold PE Spec.cauchyPow; split_ifs <;> simp

lemma PE_succ (C : ℕ) {lam : ℝ} (hl : 0 ≤ lam) (n k : ℕ) :
    PE C lam (n + 1) k = ∑ ij ∈ antidiagonal k, PE C lam n ij.1 * qE C lam ij.2 := by
  unfold PE qE
  rw [Spec.cauchyPow, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun ij _ => ?_
    rw [ENNReal.ofReal_mul (cauchyPow_nonneg C hl _ _)]
  · intro ij _; exact mul_nonneg (cauchyPow_nonneg C hl _ _) (excessPmf_nonneg C hl _)

lemma law {ι : Type} [Fintype ι] [DecidableEq ι] (C : ℕ) (r : ℝ≥0) (J : Finset ι) :
    ∀ (g : ℕ → ℝ≥0∞) (x : ι → ℕ),
      (∫⋯∫⁻_J, (fun z : ι → ℕ => g (∑ v ∈ J, (z v - C))) ∂(fun _ : ι => poissonMeasure r)) x =
        ∑' k, g k * PE C r J.card k := by
  induction J using Finset.induction_on with
  | empty =>
    intro g x
    rw [lmarginal_empty]
    simp only [Finset.sum_empty, Finset.card_empty, PE_zero]
    rw [tsum_eq_single 0 (fun k hk => by simp [hk])]
    simp
  | insert a J ha ih =>
    intro g x
    rw [lmarginal_insert _ (Measurable.of_discrete) ha]
    have hin : ∀ xa : ℕ, (∫⋯∫⁻_J, (fun z : ι → ℕ => g (∑ v ∈ insert a J, (z v - C)))
        ∂(fun _ : ι => poissonMeasure r)) (Function.update x a xa) =
        ∑' k, g ((xa - C) + k) * PE C r J.card k := by
      intro xa
      rw [lmarginal_update_of_notMem Measurable.of_discrete ha]
      rw [← ih (fun k => g ((xa - C) + k)) x]
      congr 1
      funext z
      simp only [Function.comp]
      rw [Finset.sum_insert ha]
      congr 2
      · simp
      · exact Finset.sum_congr rfl fun v hv => by
          rw [Function.update_of_ne (by rintro rfl; exact ha hv)]
    simp_rw [hin]
    rw [lint_pois, regroup C r (fun m => ∑' k, g (m + k) * PE C r J.card k),
      Finset.card_insert_of_notMem ha, conv_swap]
    refine tsum_congr fun n => ?_
    rw [PE_succ C (by positivity)]


lemma law_full {ι : Type} [Fintype ι] (C : ℕ) (r : ℝ≥0) (J : Finset ι) (g : ℕ → ℝ≥0∞) :
    ∫⁻ z, g (∑ v ∈ J, (z v - C)) ∂(Spec.poissonVec (fun _ : ι => r)) =
      ∑' k, g k * PE C r J.card k := by
  classical
  unfold Spec.poissonVec
  have := lintegral_eq_of_lmarginal_eq (μ := fun _ : ι => poissonMeasure r) J
    (f := fun z : ι → ℕ => g (∑ v ∈ J, (z v - C)))
    (g := fun _ => ∑' k, g k * PE C r J.card k)
    Measurable.of_discrete Measurable.of_discrete (by
      funext x
      rw [law]
      simp [lmarginal])
  rw [this]
  simp

lemma pois_sum (r : ℝ≥0) :
    ∑' n, ENNReal.ofReal (Real.exp (-r) * r ^ n / (n.factorial : ℝ)) = 1 := by
  have h := hasSum_one_poissonMeasure r
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) h.summable, h.tsum_eq]
  simp

lemma pois_mgf (r : ℝ≥0) (C : ℕ) :
    ∑' n, ENNReal.ofReal (Real.exp (-r) * r ^ n / (n.factorial : ℝ)) *
      ENNReal.ofReal ((2:ℝ) ^ n / 2 ^ C) = ENNReal.ofReal (Real.exp r / 2 ^ C) := by
  have h := ((NormedSpace.expSeries_div_hasSum_exp (2 * (r:ℝ))).mul_left
    (Real.exp (-r) / 2 ^ C))
  have h' : HasSum (fun n : ℕ => Real.exp (-r) * r ^ n / (n.factorial : ℝ) * ((2:ℝ) ^ n / 2 ^ C))
      (Real.exp r / 2 ^ C) := by
    convert h using 1
    · funext n; rw [mul_pow]; field_simp
    · rw [← Real.exp_eq_exp_ℝ, show (Real.exp (-r) / 2 ^ C) * Real.exp (2 * r) =
        Real.exp (-r + 2 * r) / 2 ^ C by rw [Real.exp_add]; ring]
      ring_nf
  rw [← h'.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) h'.summable]
  refine tsum_congr fun n => ?_
  rw [ENNReal.ofReal_mul (by positivity)]


lemma qE_mgf (C : ℕ) (r : ℝ≥0) :
    ∑' m, qE C r m * ENNReal.ofReal ((2:ℝ) ^ m) ≤ ENNReal.ofReal (1 + Real.exp r / 2 ^ C) := by
  rw [← regroup C r (fun m => ENNReal.ofReal ((2:ℝ) ^ m))]
  have hp : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-r) * r ^ n / (n.factorial : ℝ)) *
      ENNReal.ofReal ((2:ℝ) ^ (n - C)) ≤
      ENNReal.ofReal (Real.exp (-r) * r ^ n / (n.factorial : ℝ)) *
        (1 + ENNReal.ofReal ((2:ℝ) ^ n / 2 ^ C)) := by
    intro n
    gcongr
    rcases le_or_gt n C with hn | hn
    · rw [Nat.sub_eq_zero_of_le hn]; simp
    · have : (2:ℝ) ^ n / 2 ^ C = 2 ^ (n - C) := by
        rw [div_eq_iff (by positivity), ← pow_add, Nat.sub_add_cancel hn.le]
      rw [this]; exact le_add_self
  calc _ ≤ ∑' n, ENNReal.ofReal (Real.exp (-r) * r ^ n / (n.factorial : ℝ)) *
        (1 + ENNReal.ofReal ((2:ℝ) ^ n / 2 ^ C)) := ENNReal.tsum_le_tsum hp
    _ = 1 + ENNReal.ofReal (Real.exp r / 2 ^ C) := by
      simp_rw [mul_add, mul_one]
      rw [ENNReal.tsum_add, pois_sum, pois_mgf]
    _ = _ := by
      rw [ENNReal.ofReal_add (by norm_num) (by positivity)]; simp

lemma gf_pow (C : ℕ) {r : ℝ≥0} (n : ℕ) :
    ∑' k, ENNReal.ofReal ((2:ℝ) ^ k) * PE C r n k =
      (∑' m, qE C r m * ENNReal.ofReal ((2:ℝ) ^ m)) ^ n := by
  induction n with
  | zero =>
    simp only [PE_zero, pow_zero]
    rw [tsum_eq_single 0 (fun k hk => by simp [hk])]
    simp
  | succ n ih =>
    have hl : (0:ℝ) ≤ r := r.2
    have h1 : ∑' k, ENNReal.ofReal ((2:ℝ) ^ k) * PE C r (n + 1) k =
        ∑' m, qE C r m * ∑' k, ENNReal.ofReal ((2:ℝ) ^ (m + k)) * PE C r n k := by
      refine Eq.trans ?_ (conv_swap (qE C r) (PE C r n) (fun k => ENNReal.ofReal ((2:ℝ) ^ k))).symm
      refine tsum_congr fun k => ?_
      rw [PE_succ C hl, Finset.mul_sum]
    rw [h1, pow_succ']
    simp_rw [pow_add, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 ^ _), mul_assoc,
      ENNReal.tsum_mul_left, ih]
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr fun m => ?_
    ring


lemma tail_nat (a j : ℕ) (ha : 1 ≤ a) : a + j ≤ a * 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have : 1 ≤ a * 2 ^ j := Nat.mul_pos ha (Nat.two_pow_pos j)
    rw [pow_succ]; nlinarith

lemma tail_real (S K k : ℕ) (hS : S < K + 1) (hk : K < k) :
    (((k - S : ℕ)) : ℝ) ≤ ((K + 1 - S : ℕ) : ℝ) / 2 ^ (K + 1) * 2 ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = K + 1 + j := ⟨k - (K + 1), by omega⟩
  have h1 := tail_nat (K + 1 - S) j (by omega)
  have h2 : K + 1 + j - S = K + 1 - S + j := by omega
  have h3 : ((K + 1 - S : ℕ) : ℝ) / 2 ^ (K + 1) * 2 ^ (K + 1 + j) =
      ((K + 1 - S : ℕ) : ℝ) * 2 ^ j := by
    rw [pow_add (2:ℝ) (K + 1) j]; field_simp
  rw [h2, h3]
  exact_mod_cast h1

end P7aux

theorem P7_of (h : Spec.P7alg_statement) : Spec.P7_statement := by
  classical
  intro ι _ J C S K lam hSK
  have hl : (0:ℝ) ≤ lam := lam.2
  set n := J.card with hn
  have hc : ∀ k, 0 ≤ Spec.seriesCoeff n C lam k := fun k =>
    le_trans (P7aux.cauchyPow_nonneg C hl n k) (h n C k lam hl)
  have e : ∫⁻ z, Spec.restrictedStopLoss J C S z ∂(Spec.poissonVec (fun _ : ι => lam)) =
      ∑' k, ((k - S : ℕ) : ℝ≥0∞) * P7aux.PE C lam n k :=
    P7aux.law_full C lam J (fun k => ((k - S : ℕ) : ℝ≥0∞))
  rw [e]
  set T0 : ℝ := ((K + 1 - S : ℕ) : ℝ) / 2 ^ (K + 1) with hT0
  have hT0nn : 0 ≤ T0 := by positivity
  have hpt : ∀ k, ((k - S : ℕ) : ℝ≥0∞) * P7aux.PE C lam n k ≤
      (if k ∈ Finset.Icc (S + 1) K then
        ENNReal.ofReal (((k - S : ℕ) : ℝ) * Spec.seriesCoeff n C lam k) else 0) +
      ENNReal.ofReal T0 * (ENNReal.ofReal ((2:ℝ) ^ k) * P7aux.PE C lam n k) := by
    intro k
    by_cases hk1 : k ∈ Finset.Icc (S + 1) K
    · rw [if_pos hk1]
      refine le_trans ?_ le_self_add
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      gcongr
      exact ENNReal.ofReal_le_ofReal (h n C k lam hl)
    · rw [if_neg hk1, zero_add]
      by_cases hkS : k ≤ S
      · rw [Nat.sub_eq_zero_of_le hkS]; simp
      · have hk : K < k := by
          by_contra hh
          exact hk1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        rw [← mul_assoc, ← ENNReal.ofReal_mul hT0nn]
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (P7aux.tail_real S K k (by omega) hk)
  have hA : ∑' k, (if k ∈ Finset.Icc (S + 1) K then
        ENNReal.ofReal (((k - S : ℕ) : ℝ) * Spec.seriesCoeff n C lam k) else 0) =
      ENNReal.ofReal (∑ k ∈ Finset.Icc (S + 1) K, ((k - S : ℕ) : ℝ) * Spec.seriesCoeff n C lam k) := by
    rw [tsum_eq_sum (s := Finset.Icc (S + 1) K) (fun k hk => by simp [hk]),
      ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (by positivity) (hc k))]
    exact Finset.sum_congr rfl fun k hk => by simp [hk]
  set w : ℝ := Real.exp lam / 2 ^ C with hw
  have hM : (∑' k, ENNReal.ofReal ((2:ℝ) ^ k) * P7aux.PE C lam n k) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * w)) := by
    rw [P7aux.gf_pow]
    calc _ ≤ ENNReal.ofReal (1 + w) ^ n := by
          gcongr; exact P7aux.qE_mgf C lam
      _ = ENNReal.ofReal ((1 + w) ^ n) := by rw [ENNReal.ofReal_pow (by positivity)]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          rw [Real.exp_nat_mul]
          exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp w]) n
  calc _ ≤ ∑' k, ((if k ∈ Finset.Icc (S + 1) K then
        ENNReal.ofReal (((k - S : ℕ) : ℝ) * Spec.seriesCoeff n C lam k) else 0) +
      ENNReal.ofReal T0 * (ENNReal.ofReal ((2:ℝ) ^ k) * P7aux.PE C lam n k)) :=
        ENNReal.tsum_le_tsum hpt
    _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hA]
    _ ≤ ENNReal.ofReal (∑ k ∈ Finset.Icc (S + 1) K, ((k - S : ℕ) : ℝ) * Spec.seriesCoeff n C lam k) +
        ENNReal.ofReal T0 * ENNReal.ofReal (Real.exp ((n : ℝ) * w)) := by gcongr
    _ = ENNReal.ofReal (Spec.Phi K n C lam S) := by
      rw [← ENNReal.ofReal_mul hT0nn, ← ENNReal.ofReal_add
        (Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (hc k)) (by positivity)]
      unfold Spec.Phi
      rw [hT0, hw]
      congr 2
      ring_nf

end RebuildBound
