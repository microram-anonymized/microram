import RebuildBound.Spec.P10r
import RebuildBound.Spec.CANumR
import RebuildBound.Proofs.NCA1
import RebuildBound.Proofs.NCA5.Sound
import Mathlib.Data.Int.CardIntervalMod

/-!
# NCA5: one class of the radix range law, from P10r (package NCA5)

`class_bound`: for a class mass `q = qc / 2^51`, the four checks of the radix
node (`checkThin` on NCA1's depth-5 table, `checkConv` for the partial sums
`2..5`) and NCA1's `checkFinal` on the root-loss marginal give
`stopLoss (rangeLawR 64 32 1088 2^8 5 5 q) 64 ≤ tn / td + 3 · 10^-45`, the last
term bounding P10r's truncation term. The steps after the thinning are generic
(`thin_one`, `class_core`, `eps_bound` for any radix, depth, early cap, roots and
target exponent) and shared with TPNum and SelRange3/5/7. `qCount_eq`: the class counts in closed
form, `#{h < M : h ≡ a mod r} = M / r + [a < M mod r]`.
-/

open MeasureTheory ProbabilityTheory RebuildBound.Spec
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.NCA5

open RebuildBound.NCA1

/-! ## The class counts -/

/-- `qCount W b r a = 2^(W-b) / r + [a < 2^(W-b) mod r]` for `a < r`. -/
lemma qCount_eq {W b r a : ℕ} (har : a < r) :
    qCount W b r a = 2 ^ (W - b) / r + if a < 2 ^ (W - b) % r then 1 else 0 := by
  have hr : 0 < r := by omega
  have h := Nat.count_modEq_card (b := 2 ^ (W - b)) hr a
  rw [Nat.mod_eq_of_lt har] at h
  rw [← h, Nat.count_eq_card_filter_range, qCount]
  congr 1
  refine Finset.filter_congr fun h _ => ?_
  rw [Nat.ModEq, Nat.mod_eq_of_lt har]

lemma qMass_coe (W b r a : ℕ) :
    ((qMass W b r a : I) : ℝ) = (qCount W b r a : ℝ) / ((2 ^ (W - b) : ℕ) : ℝ) := by
  simp [qMass]

/-! ## The truncation term -/

/-- The factorial inequality behind `tail_small` (a kernel check at concrete `c`, `e`;
a definition, so that arithmetic tactics never evaluate it). -/
def TailOK (c e : ℕ) : Prop :=
  33 ^ (256 + 1) * 258 * (1122 * c * 10 ^ (2 * e)) ≤ (256 + 1).factorial * 225

/-- `τ_256(ν) ≤ 10^-2e / (1122 c)` for `0 ≤ ν ≤ 33`. -/
lemma tail_small {c e : ℕ} (hce : TailOK c e) {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 33) :
    1122 * c * poissonTail 256 ν ≤ 1 / 10 ^ (2 * e) := by
  have h := poissonTail_le (H := 256) h0 h1 (by norm_num)
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  have hF : (0 : ℝ) < (((256 + 1).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hfac : (33 : ℝ) ^ (256 + 1) * 258 * (1122 * c * 10 ^ (2 * e)) ≤
      (((256 + 1).factorial : ℕ) : ℝ) * 225 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).2 hce
  clear hce
  simp only [Nat.cast_ofNat] at h ⊢
  generalize (33 : ℝ) ^ (256 + 1) = X at hfac ⊢
  generalize (((256 + 1).factorial : ℕ) : ℝ) = F at hF hfac ⊢
  rw [show (1 : ℝ) - 33 / (256 + 2) = 225 / 258 by norm_num, div_div, mul_div_assoc',
    div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **P10r's truncation term** at `λ = 32`, `H = 256` and `g` roots is at most `g / 10^e`
when `μ = r λ q ≤ 33` and `r (2^t - 1) + 1 ≤ c`. -/
lemma eps_bound {r t c e : ℕ} (hce : TailOK c e) (g : ℕ) (q : ℝ) (h0 : 0 ≤ q) (hμ : (r : ℝ) * 32 * q ≤ 33) (hrt : r * (2 ^ t - 1) + 1 ≤ c) :
    ENNReal.ofReal ((g : ℝ) * Real.sqrt
      (((r : ℝ) * ((32 : ℝ≥0) : ℝ) * q + ((r : ℝ) * ((32 : ℝ≥0) : ℝ) * q) ^ 2) *
        ((r : ℝ) * (2 ^ t - 1) * poissonTail 256 ((32 : ℝ≥0) : ℝ) +
          if 1 < r then poissonTail 256 ((r : ℝ) * ((32 : ℝ≥0) : ℝ) * q) else 0))) ≤
      (g : ℝ≥0∞) / 10 ^ e := by
  simp only [NNReal.coe_ofNat]
  set μ : ℝ := r * 32 * q with hμdef
  have hμ0 : 0 ≤ μ := by positivity
  have e1 := tail_small hce (ν := 32) (by norm_num) (by norm_num)
  have e2 := tail_small hce hμ0 hμ
  clear hce
  have hτl0 := poissonTail_nonneg (H := 256) (ν := 32) (by norm_num) (by norm_num)
  have hτ0 := poissonTail_nonneg (H := 256) hμ0 (by push_cast; linarith)
  have h1t : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hrt' : (r : ℝ) * (2 ^ t - 1) + 1 ≤ c := by
    have : ((r * (2 ^ t - 1) + 1 : ℕ) : ℝ) ≤ c := by exact_mod_cast hrt
    rwa [Nat.cast_add, Nat.cast_mul, Nat.cast_sub h1t, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one] at this
  have hr0 : (0 : ℝ) ≤ (r : ℝ) * (2 ^ t - 1) :=
    mul_nonneg (Nat.cast_nonneg r) (by have : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ (by norm_num); linarith)
  have hite : (if 1 < r then poissonTail 256 μ else 0) ≤ poissonTail 256 μ := by
    split_ifs <;> linarith
  have hite0 : 0 ≤ (if 1 < r then poissonTail 256 μ else 0) := by split_ifs <;> linarith
  -- both tails are at most `T = 10^-2e / (1122 c)`
  have hc0 : (0 : ℝ) < c := by nlinarith
  have hc : (0 : ℝ) < 1122 * c := by positivity
  have ha : poissonTail 256 32 ≤ 1 / 10 ^ (2 * e) / (1122 * c) := by
    rw [le_div_iff₀ hc, mul_comm]; exact e1
  have hb : poissonTail 256 μ ≤ 1 / 10 ^ (2 * e) / (1122 * c) := by
    rw [le_div_iff₀ hc, mul_comm]; exact e2
  have hT0 : (0 : ℝ) ≤ 1 / 10 ^ (2 * e) / (1122 * c) := by positivity
  have hX : (μ + μ ^ 2) * ((r : ℝ) * (2 ^ t - 1) * poissonTail 256 32 +
      if 1 < r then poissonTail 256 μ else 0) ≤ (1 / 10 ^ e) ^ 2 := by
    have h2 : μ + μ ^ 2 ≤ 1122 := by nlinarith
    have hS2 : (r : ℝ) * (2 ^ t - 1) * poissonTail 256 32 +
        (if 1 < r then poissonTail 256 μ else 0) ≤ c * (1 / 10 ^ (2 * e) / (1122 * c)) := by
      nlinarith [mul_le_mul_of_nonneg_left ha hr0]
    calc (μ + μ ^ 2) * ((r : ℝ) * (2 ^ t - 1) * poissonTail 256 32 +
          if 1 < r then poissonTail 256 μ else 0)
        ≤ 1122 * (c * (1 / 10 ^ (2 * e) / (1122 * c))) :=
          mul_le_mul h2 hS2 (add_nonneg (mul_nonneg hr0 hτl0) hite0) (by norm_num)
      _ = (1 / 10 ^ e) ^ 2 := by
        rw [div_pow, one_pow, ← pow_mul, mul_comm e 2]; field_simp [hc0.ne']
  refine (eps_le (Nat.cast_nonneg g) (by positivity) hX).trans ?_
  rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.div_lt_top (by simp) (by positivity)).ne,
    ENNReal.toReal_div, ENNReal.toReal_pow]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  rw [mul_one_div]

/-- Comparing `a / 10^e` and `b / 10^f` in `ℝ≥0∞`. -/
lemma div_pow_ten_le {a b e f : ℕ} (h : a * 10 ^ f ≤ b * 10 ^ e) :
    (a : ℝ≥0∞) / 10 ^ e ≤ (b : ℝ≥0∞) / 10 ^ f := by
  have key (n k : ℕ) : (n : ℝ≥0∞) / 10 ^ k = ENNReal.ofReal ((n : ℝ) / 10 ^ k) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]; simp
  rw [key, key]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast h

/-! ## One class -/

/-- The depth-5 tree table of NCA1. -/
lemma tree5 : Bounded (2 ^ 320) Tab.t5 (truncTree 64 32 256 5) := by
  have hD : 0 < 2 ^ 320 := by positivity
  have hlam : ((32 : ℝ≥0) : ℝ) = ((32 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by norm_num
  have h1 : Bounded (2 ^ 320) Tab.t1 (truncTree 64 32 256 1) := by
    rw [truncTree]; exact base_sound hlam hD base
  have h2 := truncTree_step level2 hD h1
  have h3 := truncTree_step level3 hD h2
  have h4 := truncTree_step level4 hD h3
  exact truncTree_step level5 hD h4

/-- The thinned tree law and its first truncated partial sum, from `checkThin`. -/
lemma thin_one {t wT a d : ℕ} {F T : List (List ℕ)} (q : I) (hd : 0 < d)
    (hq : (q : ℝ) = a / d) (hF : Bounded (2 ^ 320) F (truncTree 64 32 256 t))
    (hT : checkThin wT a d 64 256 F T = true) :
    Bounded (2 ^ 320) T ((truncTree 64 32 256 t).bind (thinPair q)) ∧
      Bounded (2 ^ 320) T (truncPairConvPow 256 ((truncTree 64 32 256 t).bind (thinPair q)) 1) := by
  have hν1 := bind_thinPair_univ_le (truncTree_univ_le 64 32 256 t) q
  have : IsFiniteMeasure ((truncTree 64 32 256 t).bind (thinPair q)) :=
    ⟨hν1.trans_lt ENNReal.one_lt_top⟩
  have hν := thin_sound hd hq (by positivity) hT hF
  exact ⟨hν, by rw [truncPairConvPow_one]; exact bounded_restrict hν _⟩

/-- **One class of the radix range law**, from a bound `S` of the `r`-th truncated partial
sum of the thinned tree law: NCA1's final check on its root-loss marginal (early
probability `q 2^-t = qc / 2^(M + t)`) and P10r, whose truncation term is `eps_bound`. -/
theorem class_core (h10r : P10r_statement) {r t i P M qc rr fuel tn td c e : ℕ}
    {S : List (List ℕ)} (q : I) (hq : (q : ℝ) = (qc : ℝ) / ((2 ^ M : ℕ) : ℝ))
    (hμ : r * 32 * qc ≤ 33 * 2 ^ M) (hrt : r * (2 ^ t - 1) + 1 ≤ c)
    (hce : TailOK c e) (htd : 0 < td)
    (hS : Bounded (2 ^ 320) S
      (truncPairConvPow 256 ((truncTree 64 32 256 t).bind (thinPair q)) r))
    (hF : checkFinal 648 (2 ^ 320) 100 rr 32 256 64 (2 ^ i) P qc (2 ^ (M + t)) 32 1 0 fuel tn td 0
      [rootMarg 64 S] = true) :
    stopLoss (rangeLawR 64 32 P (2 ^ i) t r q) 64 ≤
      (tn : ℝ≥0∞) / td + ((2 ^ i : ℕ) : ℝ≥0∞) / 10 ^ e := by
  have hq0 : 0 ≤ (q : ℝ) := q.2.1
  have hμr : (r : ℝ) * 32 * q ≤ 33 := by
    have : ((r * 32 * qc : ℕ) : ℝ) ≤ ((33 * 2 ^ M : ℕ) : ℝ) := by exact_mod_cast hμ
    rw [hq, mul_div_assoc', div_le_iff₀ (by positivity)]
    push_cast at this ⊢
    linarith
  have hν1 := bind_thinPair_univ_le (truncTree_univ_le 64 32 256 t) q
  set ρ := truncRadixRoot 64 32 256 t r q with hρ_def
  have hG := oneRow_bounded (ρ := ρ) (rootMarg_sound hS)
  have hG1 : (ρ.map fun z => ((0 : ℕ), z)) Set.univ ≤ 1 := by
    rw [oneRow_univ, hρ_def, truncRadixRoot,
      Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ]
    exact truncPairConvPow_univ_le 256 hν1 r
  have hlam : ((32 : ℝ≥0) : ℝ) = ((32 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by norm_num
  have hpe : ((q * halfPow t : I) : ℝ) = (qc : ℝ) / ((2 ^ (M + t) : ℕ) : ℝ) := by
    rw [Set.Icc.coe_mul, hq]
    simp only [halfPow]
    push_cast
    rw [pow_add, one_div, inv_pow, ← div_eq_mul_inv, div_div]
  have hfin := final_sound hF hG hG1 hlam hpe htd
  rw [oneRow_snd] at hfin
  refine (h10r 64 32 P (2 ^ i) t r 256 64 q (by norm_num) (by push_cast; linarith)).trans ?_
  gcongr
  · exact le_self_add.trans hfin
  · exact eps_bound hce _ q hq0 hμr hrt

/-- **One class** of the `r = 5` range law. -/
theorem class_bound (h10r : P10r_statement) {qc wT w2 w3 w4 w5 rr tn td : ℕ}
    {T S2 S3 S4 S5 : List (List ℕ)} (q : I) (hq : (q : ℝ) = (qc : ℝ) / ((2 ^ 51 : ℕ) : ℝ))
    (hqc : qc * 160 ≤ 33 * 2 ^ 51) (htd : 0 < td)
    (hT : checkThin wT qc (2 ^ 51) 64 256 Tab.t5 T = true)
    (h2 : checkConv w2 (2 ^ 320) 256 T T S2 = true)
    (h3 : checkConv w3 (2 ^ 320) 256 S2 T S3 = true)
    (h4 : checkConv w4 (2 ^ 320) 256 S3 T S4 = true)
    (h5 : checkConv w5 (2 ^ 320) 256 S4 T S5 = true)
    (hF : checkFinal 648 (2 ^ 320) 100 rr 32 256 64 (2 ^ 8) 1088 qc (2 ^ 56) 32 1 0 9 tn td 0
      [rootMarg 64 S5] = true) :
    stopLoss (rangeLawR 64 32 1088 (2 ^ 8) 5 5 q) 64 ≤ (tn : ℝ≥0∞) / td + 3 / 10 ^ 45 := by
  have hD : 0 < 2 ^ 320 := by positivity
  obtain ⟨hν, hS1⟩ := thin_one q (by positivity) hq tree5 hT
  refine (class_core h10r (r := 5) (t := 5) (M := 51) (c := 156) (e := 47) q hq (by omega)
    (by norm_num) (by unfold TailOK; decide +kernel) htd (conv_sound hD h5 (conv_sound hD h4
      (conv_sound hD h3 (conv_sound hD h2 hS1 hν) hν) hν) hν) hF).trans
    (add_le_add le_rfl ?_)
  refine (div_pow_ten_le (a := 2 ^ 8) (b := 3) (e := 47) (f := 45) (by norm_num)).trans_eq ?_
  norm_num

end RebuildBound.NCA5
