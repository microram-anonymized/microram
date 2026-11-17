import RebuildBound.Proofs.P10.Tree
import RebuildBound.Proofs.P10.Lipschitz

/-!
# P10: the truncation enclosure

`REPORT.tex`, paragraph "A rigorous terminal truncation enclosure", case `r = 1`.
Write `F = shadowTree C λ t`, `G = truncTree C λ H t` and `B = F - G`.

1. `G ≤ F` (`truncTree_le`), so `F = B + G`, and `B(ℕ²) ≤ (2^t - 1) P(Po(λ) > H)`
   (`truncTree_mass`). Every node total is `Po(λ)` (`shadowTree_tot`).
2. `P(Po(λ) > H) ≤ τ_H(λ)` for `λ < H + 2` (`poisson_tail_le`).
3. Cauchy–Schwarz (`lintegral_snd_le`): `∫ R dB ≤ √(∫ (M + R)² dB · B(ℕ²))`, and
   `∫ (M + R)² dB ≤ ∫ (M + R)² dF ≤ λ + λ²` (`shadowTree_moment`).
4. The root-loss law is `F.map snd = G.map snd + B.map snd`, and the zero completion
   of `G.map snd` puts `B`'s mass at zero. Replacing the defect part by the atom one
   root loss at a time costs at most `∫ R dB` each (`stopLoss_iter`).
5. Assemble in `ℝ≥0∞`, converting `x ^ (1/2)` to `Real.sqrt`.

Probability API: measure-based throughout (`Measure.bind`, `Measure.conv`, `binomial`,
`poissonMeasure`, `Measure.sub`, `lintegral`, Hölder's
`ENNReal.lintegral_mul_le_Lp_mul_Lq`). Obstacles recorded: Mathlib has no
`binomial` convolution identity `Bin(a, p) ∗ Bin(b, p) = Bin(a + b, p)`, no Poisson
thinning `Po(r).bind (Bin(·, p)) = Po(r p)` and no Poisson second moment; all three
are proved here (`P10/Poisson.lean`) from `X1Proof.binomial_succ`, singletons and
`ℝ≥0∞` tsums.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P10Proof

open RebuildBound.Spec

/-- Cauchy–Schwarz against a finite measure on node states: the root loss is at most
the root total. -/
lemma lintegral_snd_le (B : Measure (ℕ × ℕ)) :
    ∫⁻ s, (s.2 : ℝ≥0∞) ∂B ≤
      (∫⁻ s, ((tot s : ℕ) : ℝ≥0∞) ^ 2 ∂B) ^ (1 / 2 : ℝ) * (B Set.univ) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq B Real.HolderConjugate.two_two
    (f := fun s : ℕ × ℕ => (s.2 : ℝ≥0∞)) (g := fun _ => 1) Measurable.of_discrete.aemeasurable
    aemeasurable_const
  simp only [Pi.mul_apply, mul_one, lintegral_const, one_pow, one_mul, ENNReal.rpow_two] at h
  refine h.trans ?_
  gcongr with s
  exact Nat.cast_le.2 (Nat.le_add_left _ _)

end RebuildBound.P10Proof

open RebuildBound.Spec RebuildBound.P10Proof RebuildBound.P11eProof in
theorem RebuildBound.P10 : RebuildBound.Spec.P10_statement := by
  intro C lam P p g t H L hH
  have hFp := isProb_shadowTree C lam t
  set F := shadowTree C lam t with hF
  set G := truncTree C lam H t with hG
  have hGF : G ≤ F := truncTree_le C lam H t
  set B := F - G with hB
  have hFB : F = B + G := (Measure.sub_add_cancel_of_le hGF).symm
  have hBF : B ≤ F := by
    conv_rhs => rw [hFB]
    exact Measure.le_add_right le_rfl
  have : IsFiniteMeasure B := isFiniteMeasure_of_le F hBF
  set τ := poissonMeasure lam {n | H < n} with hτ
  set β : ℝ≥0∞ := ((2 ^ t - 1 : ℕ) : ℝ≥0∞) * τ with hβ
  -- the defect's mass
  have hmass : 1 ≤ G Set.univ + β := truncTree_mass C lam H t
  have hBG : B Set.univ + G Set.univ = 1 := by
    rw [← Measure.add_apply, ← hFB]
    exact measure_univ
  have hBu : B Set.univ ≤ β := by
    refine (ENNReal.add_le_add_iff_right (measure_ne_top G Set.univ)).1 ?_
    rw [hBG, add_comm]
    exact hmass
  -- the root-loss laws
  have hsnd : F.map Prod.snd = G.map Prod.snd + B.map Prod.snd := by
    rw [hFB, Measure.map_add _ _ measurable_snd, add_comm]
  have hzc : zeroComplete (G.map Prod.snd) = zc (G.map Prod.snd) (B.map Prod.snd) := by
    unfold zeroComplete zc
    congr 2
    rw [Measure.map_apply measurable_snd MeasurableSet.univ,
      Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ, ← hBG,
      ENNReal.add_sub_cancel_right (measure_ne_top G Set.univ)]
  have hprob : IsProbabilityMeasure (G.map Prod.snd + B.map Prod.snd) := by
    rw [← hsnd]
    infer_instance
  have hiter := stopLoss_iter (G.map Prod.snd) (B.map Prod.snd) hprob L g (binomial P p)
  unfold rangeLaw
  rw [hsnd, hzc]
  refine hiter.trans (add_le_add le_rfl ?_)
  rw [lintegral_map Measurable.of_discrete measurable_snd]
  -- the real bound
  have hl0 : (0 : ℝ) ≤ lam := lam.2
  set a : ℝ := (lam : ℝ) + (lam : ℝ) ^ 2 with ha
  set b : ℝ := ((2 : ℝ) ^ t - 1) * poissonTail H lam with hb
  have ha0 : 0 ≤ a := by positivity
  have h2t : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
  have hb0 : 0 ≤ b := mul_nonneg (by linarith) (poissonTail_nonneg hl0 hH)
  have hmom : ∫⁻ s, ((tot s : ℕ) : ℝ≥0∞) ^ 2 ∂B ≤ ENNReal.ofReal a := by
    refine (lintegral_mono' hBF le_rfl).trans ((shadowTree_moment C lam t).trans_eq ?_)
    rw [ha, ENNReal.ofReal_add hl0 (by positivity), ENNReal.ofReal_pow hl0,
      ENNReal.ofReal_coe_nnreal]
  have hmassR : B Set.univ ≤ ENNReal.ofReal b := by
    refine hBu.trans ?_
    rw [hβ, hb, ENNReal.ofReal_mul (by linarith)]
    gcongr
    · rw [← ENNReal.ofReal_natCast]
      refine le_of_eq ?_
      congr 1
      rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    · exact poisson_tail_le lam H hH
  calc (g : ℝ≥0∞) * ∫⁻ s, (s.2 : ℝ≥0∞) ∂B
      ≤ (g : ℝ≥0∞) * (ENNReal.ofReal a ^ (1 / 2 : ℝ) * ENNReal.ofReal b ^ (1 / 2 : ℝ)) := by
        gcongr
        exact (lintegral_snd_le B).trans (by gcongr)
    _ = ENNReal.ofReal (g * Real.sqrt (((lam : ℝ) + (lam : ℝ) ^ 2) * (2 ^ t - 1) *
          poissonTail H lam)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg ha0 (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hb0 (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← Real.sqrt_eq_rpow,
          ← Real.sqrt_eq_rpow, ← Real.sqrt_mul ha0, ha, hb, mul_assoc]
