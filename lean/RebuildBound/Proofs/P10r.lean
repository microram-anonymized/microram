import RebuildBound.Proofs.P10r.Radix

/-!
# P10r: the truncation enclosure at a terminal radix

`REPORT.tex`, paragraph "A rigorous terminal truncation enclosure", every odd `r`; the
case `r = 1` is P10 (`Proofs/P10.lean`), whose lemmas this file reuses. Write
`F = shadowTree C λ t` thinned by `q`, `G = truncTree C λ H t` thinned by `q`,
`S = pairConvPow F r`, `U = pairConvPow G r` and `T = truncPairConvPow H G r`.

1. `T = U|_{low}` (`truncPairConvPow_eq`): partial sums are at most the final sum.
   `U ≤ S` (`pairConvPow_mono`), so `T ≤ S`; write `D = S - T`.
2. Mass: `U(ℕ²) = a^r` with `a = G(ℕ²)`, `1 ≤ a + (2^t - 1) P(Po(λ) > H)`
   (`truncTree_mass`), hence `1 ≤ a^r + r (2^t - 1) P(Po(λ) > H)` (Bernoulli). The
   restriction to `low` removes `U(high) ≤ S(high) = P(Po(r λ_t q) > H)` for `r > 1`
   (`radix_tot`), and nothing for `r ≤ 1`, since a thinned truncated tree has no mass
   above `H` (`pairConvPow_high`).
3. Cauchy–Schwarz (`lintegral_cap_le`, from `lintegral_snd_le`): the capped loss is
   at most the total, and `∫ T² dS ≤ μ + μ²`, `μ = r λ q` (`radix_moment`).
4. The radix root law is `S.map cap = T.map cap + D.map cap`, and the zero completion
   of `T.map cap` puts `D`'s mass at zero; `stopLoss_iter` over the `g` roots.

Probability API: measure-based throughout, as P10. Obstacles recorded: none beyond
P10's (Poisson thinning, binomial convolution, Poisson moments, all from P10); the
depth `t = 0` has total `Po(0)`, which Mathlib does not identify with `δ₀`
(`poissonMeasure_zero`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P10rProof

open RebuildBound.Spec RebuildBound.P10Proof RebuildBound.P11eProof

/-- The cap of the radix node: `s ↦ s.2 + (s.1 - C)`. -/
def cap (C : ℕ) (s : ℕ × ℕ) : ℕ := s.2 + (s.1 - C)

lemma cap_le_tot (C : ℕ) (s : ℕ × ℕ) : cap C s ≤ tot s := by
  simp only [cap, tot]
  omega

/-- Cauchy–Schwarz for the capped loss: `lintegral_snd_le` after the map
`s ↦ (tot s - cap s, cap s)`, which keeps the total. -/
lemma lintegral_cap_le (C : ℕ) (B : Measure (ℕ × ℕ)) :
    ∫⁻ s, (cap C s : ℝ≥0∞) ∂B ≤
      (∫⁻ s, ((tot s : ℕ) : ℝ≥0∞) ^ 2 ∂B) ^ (1 / 2 : ℝ) * (B Set.univ) ^ (1 / 2 : ℝ) := by
  set f : ℕ × ℕ → ℕ × ℕ := fun s => (tot s - cap C s, cap C s) with hf
  have h := lintegral_snd_le (B.map f)
  have htot : ∀ s, tot (f s) = tot s := fun s => by
    have := cap_le_tot C s
    simp only [hf, tot] at this ⊢
    omega
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete,
    lintegral_map Measurable.of_discrete Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ] at h
  simp only [htot] at h
  exact h

/-- At most one thinned truncated tree has no mass above `H`. -/
lemma pairConvPow_high (μ : Measure (ℕ × ℕ)) [IsFiniteMeasure μ] (H : ℕ)
    (h : μ (lowTotal H)ᶜ = 0) : ∀ r, r ≤ 1 → pairConvPow μ r (lowTotal H)ᶜ = 0
  | 0, _ => by
    rw [pairConvPow, Measure.dirac_apply' _ MeasurableSet.of_discrete]
    exact Set.indicator_of_notMem (fun h => absurd (zero_mem_lowTotal H) h) _
  | 1, _ => by
    rw [pairConvPow, pairConvPow, show ((0, 0) : ℕ × ℕ) = 0 from rfl, Measure.dirac_zero_conv]
    exact h
  | r + 2, h2 => absurd h2 (by omega)

lemma coe_rate (lam : ℝ≥0) (r : ℕ) (q : I) :
    ((r * (lam * pNN q) : ℝ≥0) : ℝ) = r * (lam : ℝ) * q := by
  rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_natCast, mul_assoc]
  rfl

/-- The radix sum is above `H` with probability at most `τ_H(r λ q)`. -/
lemma radix_high_le (C : ℕ) (lam : ℝ≥0) (t r H : ℕ) (q : I)
    (h : (r * (lam : ℝ) * q : ℝ) < H + 2) :
    pairConvPow ((shadowTree C lam t).bind (thinPair q)) r (lowTotal H)ᶜ ≤
      ENNReal.ofReal (poissonTail H (r * (lam : ℝ) * q)) := by
  rw [map_tot_high, radix_tot]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp only [lamAt, ↓reduceIte, zero_mul, mul_zero, poissonMeasure_zero]
    rw [Measure.dirac_apply' _ MeasurableSet.of_discrete, Set.indicator_of_notMem (by simp)]
    exact zero_le
  · have h0 : t ≠ 0 := by omega
    simp only [lamAt, h0, ↓reduceIte]
    rw [← coe_rate] at h ⊢
    exact poisson_tail_le _ H h

/-- The second moment of the radix sum's total is at most `μ + μ²`, `μ = r λ q`. -/
lemma radix_moment (C : ℕ) (lam : ℝ≥0) (t r : ℕ) (q : I) :
    ∫⁻ s, ((tot s : ℕ) : ℝ≥0∞) ^ 2 ∂(pairConvPow ((shadowTree C lam t).bind (thinPair q)) r) ≤
      ENNReal.ofReal (r * (lam : ℝ) * q + (r * (lam : ℝ) * q) ^ 2) := by
  rw [← lintegral_map (f := fun n : ℕ => ((n : ℕ) : ℝ≥0∞) ^ 2) Measurable.of_discrete
    Measurable.of_discrete, radix_tot, lintegral_sq_poisson, ← coe_rate,
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_coe_nnreal]
  have : r * (lamAt lam t * pNN q) ≤ r * (lam * pNN q) := by
    gcongr
    exact lamAt_le lam t
  have h' : ((r * (lamAt lam t * pNN q) : ℝ≥0) : ℝ≥0∞) ≤ ((r * (lam * pNN q) : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_le_coe.2 this
  gcongr

end RebuildBound.P10rProof

open RebuildBound.Spec RebuildBound.P10Proof RebuildBound.P11eProof RebuildBound.P10rProof in
theorem RebuildBound.P10r : RebuildBound.Spec.P10r_statement := by
  intro C lam P g t r H L q hH hμH
  have hTp := isProb_shadowTree C lam t
  set F := (shadowTree C lam t).bind (thinPair q) with hF
  set G := (truncTree C lam H t).bind (thinPair q) with hG
  have hGF : G ≤ F := bind_mono_left (truncTree_le C lam H t) _
  have : IsFiniteMeasure G := isFinite_bind_thinPair _ q
  have hSp : IsProbabilityMeasure (pairConvPow F r) := isProb_pairConvPow F r
  set S := pairConvPow F r with hS
  set U := pairConvPow G r with hU
  set T := truncPairConvPow H G r with hT
  have hTU : T = U.restrict (lowTotal H) := truncPairConvPow_eq H G r
  have hUS : U ≤ S := pairConvPow_mono hGF r
  have hTS : T ≤ S := hTU ▸ Measure.restrict_le_self.trans hUS
  have : IsFiniteMeasure T := isFiniteMeasure_of_le S hTS
  set D := S - T with hD
  have hSD : S = D + T := (Measure.sub_add_cancel_of_le hTS).symm
  have hDS : D ≤ S := by
    conv_rhs => rw [hSD]
    exact Measure.le_add_right le_rfl
  have : IsFiniteMeasure D := isFiniteMeasure_of_le S hDS
  -- the mass of `T`
  set τ := poissonMeasure lam {n | H < n} with hτ
  set b : ℝ≥0∞ := ((2 ^ t - 1 : ℕ) : ℝ≥0∞) * τ with hb
  set X : ℝ≥0∞ := if 1 < r then S (lowTotal H)ᶜ else 0 with hX
  have ha1 : G Set.univ ≤ 1 := by
    rw [hG, bind_thinPair_univ]
    exact truncTree_univ_le C lam H t
  have hab : 1 ≤ G Set.univ + b := by
    rw [hG, bind_thinPair_univ]
    exact truncTree_mass C lam H t
  have hUhigh : U (lowTotal H)ᶜ ≤ X := by
    rcases lt_or_ge 1 r with h1 | h1
    · simp only [hX, h1, ↓reduceIte]
      exact hUS _
    · have h1' : ¬ 1 < r := by omega
      simp only [hX, h1', ↓reduceIte]
      rw [hU, pairConvPow_high G H (bind_thinPair_high _ H q (truncTree_high C lam H t)) r h1]
  have hmass : 1 ≤ T Set.univ + (r * b + X) := by
    calc 1 ≤ G Set.univ ^ r + r * b := one_le_pow_add ha1 hab r
      _ = U (lowTotal H) + U (lowTotal H)ᶜ + r * b := by
          rw [measure_add_measure_compl MeasurableSet.of_discrete, hU, pairConvPow_univ]
      _ ≤ T Set.univ + X + r * b := by
          rw [hTU, Measure.restrict_apply_univ]
          gcongr
      _ = _ := by ring
  have hDT : D Set.univ + T Set.univ = 1 := by
    rw [← Measure.add_apply, ← hSD]
    exact measure_univ
  have hDu : D Set.univ ≤ r * b + X := by
    refine (ENNReal.add_le_add_iff_right (measure_ne_top T Set.univ)).1 ?_
    rw [hDT, add_comm]
    exact hmass
  -- the root-loss laws
  have hsnd : S.map (cap C) = T.map (cap C) + D.map (cap C) := by
    rw [hSD, Measure.map_add _ _ Measurable.of_discrete, add_comm]
  have hzc : zeroComplete (T.map (cap C)) = zc (T.map (cap C)) (D.map (cap C)) := by
    unfold zeroComplete zc
    congr 2
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ,
      Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ, ← hDT,
      ENNReal.add_sub_cancel_right (measure_ne_top T Set.univ)]
  have hprob : IsProbabilityMeasure (T.map (cap C) + D.map (cap C)) := by
    rw [← hsnd]
    infer_instance
  have hiter := stopLoss_iter (T.map (cap C)) (D.map (cap C)) hprob L g
    (binomial P (q * halfPow t))
  have eR : rangeLawR C lam P g t r q =
      binomial P (q * halfPow t) ∗ natConvPow (S.map (cap C)) g := rfl
  have eR' : truncRadixRoot C lam H t r q = T.map (cap C) := rfl
  rw [eR, eR', hsnd, hzc]
  refine hiter.trans (add_le_add le_rfl ?_)
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete]
  -- the real bound
  have hl0 : (0 : ℝ) ≤ lam := lam.2
  have hq0 : (0 : ℝ) ≤ q := unitInterval.nonneg q
  set A : ℝ := r * (lam : ℝ) * q + (r * (lam : ℝ) * q) ^ 2 with hA
  set B : ℝ := r * (2 ^ t - 1) * poissonTail H lam +
    if 1 < r then poissonTail H (r * (lam : ℝ) * q) else 0 with hB
  have hA0 : 0 ≤ A := by positivity
  have h2t : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
  have hB1 : 0 ≤ (r : ℝ) * (2 ^ t - 1) * poissonTail H lam :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (poissonTail_nonneg hl0 hH)
  have hB2 : 0 ≤ (if 1 < r then poissonTail H (r * (lam : ℝ) * q) else 0) := by
    split_ifs
    · exact poissonTail_nonneg (by positivity) hμH
    · exact le_rfl
  have hB0 : 0 ≤ B := add_nonneg hB1 hB2
  have hmom : ∫⁻ s, ((tot s : ℕ) : ℝ≥0∞) ^ 2 ∂D ≤ ENNReal.ofReal A :=
    (lintegral_mono' hDS le_rfl).trans (radix_moment C lam t r q)
  have hrb : (r : ℝ≥0∞) * b ≤ ENNReal.ofReal ((r : ℝ) * (2 ^ t - 1) * poissonTail H lam) := by
    rw [hb, ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (by linarith)),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]
    gcongr
    · rw [← ENNReal.ofReal_natCast]
      refine le_of_eq ?_
      congr 1
      rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    · exact poisson_tail_le lam H hH
  have hXle : X ≤ ENNReal.ofReal (if 1 < r then poissonTail H (r * (lam : ℝ) * q) else 0) := by
    rw [hX]
    split_ifs
    · exact radix_high_le C lam t r H q hμH
    · exact zero_le
  have hmassR : D Set.univ ≤ ENNReal.ofReal B := by
    refine hDu.trans ?_
    rw [hB, ENNReal.ofReal_add hB1 hB2]
    exact add_le_add hrb hXle
  calc (g : ℝ≥0∞) * ∫⁻ s, ((cap C s : ℕ) : ℝ≥0∞) ∂D
      ≤ (g : ℝ≥0∞) * (ENNReal.ofReal A ^ (1 / 2 : ℝ) * ENNReal.ofReal B ^ (1 / 2 : ℝ)) := by
        gcongr
        exact (lintegral_cap_le C D).trans (by gcongr)
    _ = ENNReal.ofReal (g * Real.sqrt (A * B)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA0 (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hB0 (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← Real.sqrt_eq_rpow,
          ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hA0]
