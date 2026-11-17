import RebuildBound.Proofs.NCA1.LevelSound
import RebuildBound.Proofs.P7
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Soundness of `checkFinal` (package NCA1)

From a table bound `Bounded D F G` on a sub-probability law `G` of node states,
the stop-loss of `Bin(P, p) ∗ (zeroComplete (G.map snd))^{∗g}` at `L`:

* the zero-completed root law is coefficientwise at most `1 + Σ_{j≥1} W_j z^j / D`
  with `W` the column sums of `F` (`zc_scaled`);
* `pgf` (in `ℝ≥0∞⟦X⟧`) turns convolution into multiplication, so the law's
  coefficients through `H` are bounded by the rounded binary power
  `powRound` (`powRound_sound`) times the binomial row (`binomRow_sound`);
* the stop-loss is the finite sum through `H` plus `(H+1-L) 2^-(H+1) E 2^Y`
  (P7's `tail_real`), and `E 2^Y ≤ (1+p)^P (1 + W(2))^g ≤ (1+p)^P exp(g W(2))`,
  bounded with NTop's `exp_upper`;
* the truncation term of P10 by NTop's Poisson enclosure (`eps_sound`).

All lemmas hold for every `C, λ, P, p, g, t, H, L` and precision.
-/

open MeasureTheory ProbabilityTheory Finset Polynomial RebuildBound.Spec
open scoped ENNReal NNReal unitInterval BigOperators

namespace RebuildBound.NCA1

/-! ## Small arithmetic facts -/

lemma cdiv_mul_ge (x y : ℕ) (hy : 0 < y) : x ≤ NTop.cdiv x y * y := by
  unfold NTop.cdiv
  have h1 := Nat.div_add_mod (x + (y - 1)) y
  have h2 := Nat.mod_lt (x + (y - 1)) hy
  rw [mul_comm] at h1
  omega

lemma cdiv_zero (y : ℕ) (hy : 0 < y) : NTop.cdiv 0 y = 0 := by
  unfold NTop.cdiv; rw [zero_add]; exact Nat.div_eq_of_lt (by omega)

/-- Cancel a positive natural factor in `ℝ≥0∞`. -/
lemma ennreal_cancel {x : ℝ≥0∞} {y c : ℕ} (hc : 0 < c) (h : x * c ≤ (y : ℝ≥0∞) * c) : x ≤ y :=
  (ENNReal.mul_le_mul_iff_left (by exact_mod_cast hc.ne') (ENNReal.natCast_ne_top _)).mp h

lemma evalL_one (l : List ℕ) : evalL 1 l = l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [evalL, ih]

lemma eval_lpoly (x : ℕ) (l : List ℕ) : (lpoly l).eval x = evalL x l := by
  have := evalL_map (Polynomial.evalRingHom x) X (l.map C)
  simp only [coe_evalRingHom, eval_X, List.map_map] at this
  rw [lpoly, this]
  congr 1
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun n _ => by simp

lemma coeff_lpoly_mul (A B : List ℕ) (k : ℕ) :
    (lpoly A * lpoly B).coeff k = ∑ ij ∈ antidiagonal k, A.getD ij.1 0 * B.getD ij.2 0 := by
  rw [coeff_mul]
  exact sum_congr rfl fun ij _ => by rw [coeff_lpoly, coeff_lpoly]

/-- The digits of a checked packed product are the coefficients of the product. -/
lemma digits_prod {w : ℕ} {A B : List ℕ} (h : A.sum * B.sum < 2 ^ w) (n k : ℕ) (hk : k < n) :
    (digitsL w n (evalL (2 ^ w) A * evalL (2 ^ w) B)).getD k 0 =
      ∑ ij ∈ antidiagonal k, A.getD ij.1 0 * B.getD ij.2 0 := by
  have h1 : (lpoly A * lpoly B).eval 1 < 2 ^ w := by
    rw [eval_mul, eval_lpoly, eval_lpoly, evalL_one, evalL_one]; exact h
  have := digit_of_eval_one h1 n k hk
  rw [eval_mul, eval_lpoly, eval_lpoly, coeff_lpoly_mul] at this
  exact this

/-! ## Point masses on `ℕ` and generating functions -/

/-- The probability generating function, as a formal power series over `ℝ≥0∞`. -/
noncomputable def pgf (μ : Measure ℕ) : PowerSeries ℝ≥0∞ := PowerSeries.mk fun n => μ {n}

lemma coeff_pgf (μ : Measure ℕ) (n : ℕ) : PowerSeries.coeff n (pgf μ) = μ {n} := by
  simp [pgf]

lemma pgf_conv (μ ν : Measure ℕ) : pgf (μ ∗ ν) = pgf μ * pgf ν := by
  ext n
  rw [coeff_pgf, conv_singleton_nat, PowerSeries.coeff_mul]
  simp only [coeff_pgf]

lemma pgf_natConvPow (μ : Measure ℕ) : ∀ g, pgf (natConvPow μ g) = pgf μ ^ g
  | 0 => by
    ext n
    rw [coeff_pgf, natConvPow, pow_zero, PowerSeries.coeff_one,
      Measure.dirac_apply' _ (measurableSet_singleton n)]
    by_cases h : n = 0
    · subst h; simp
    · rw [ite_eq_right h, Set.indicator_of_notMem (by simpa [eq_comm] using h)]
  | g + 1 => by rw [natConvPow, pgf_conv, pgf_natConvPow μ g, pow_succ]

/-- The bound `coeff k f * D ≤ A_k` for all `k ≤ H`. -/
def SerBound (D H : ℕ) (f : PowerSeries ℝ≥0∞) (A : List ℕ) : Prop :=
  ∀ k ≤ H, PowerSeries.coeff k f * D ≤ (A.getD k 0 : ℝ≥0∞)

lemma prod_scaled {D H : ℕ} {f g : PowerSeries ℝ≥0∞} {A B : List ℕ} (hf : SerBound D H f A)
    (hg : SerBound D H g B) {k : ℕ} (hk : k ≤ H) :
    PowerSeries.coeff k (f * g) * D * D ≤
      ((∑ ij ∈ antidiagonal k, A.getD ij.1 0 * B.getD ij.2 0 : ℕ) : ℝ≥0∞) := by
  rw [PowerSeries.coeff_mul, sum_mul, sum_mul]
  push_cast
  refine sum_le_sum fun ij hij => ?_
  have h1 := mem_antidiagonal.mp hij
  calc PowerSeries.coeff ij.1 f * PowerSeries.coeff ij.2 g * D * D
      = (PowerSeries.coeff ij.1 f * D) * (PowerSeries.coeff ij.2 g * D) := by ring
    _ ≤ _ := mul_le_mul' (hf _ (by omega)) (hg _ (by omega))

lemma mulRound_sound {w D H : ℕ} (hD : 0 < D) {A B Cl : List ℕ}
    (h : mulRound w D H A B = some Cl) {f g : PowerSeries ℝ≥0∞} (hf : SerBound D H f A)
    (hg : SerBound D H g B) : SerBound D H (f * g) Cl := by
  unfold mulRound at h
  split_ifs at h with hw
  injection h with h
  subst h
  intro k hk
  rw [getD_map_of_zero (fun x => NTop.cdiv x D) 0 (cdiv_zero D hD), digits_prod hw _ _ (by omega)]
  set x := ∑ ij ∈ antidiagonal k, A.getD ij.1 0 * B.getD ij.2 0
  apply ennreal_cancel hD
  calc PowerSeries.coeff k (f * g) * D * D ≤ (x : ℝ≥0∞) := prod_scaled hf hg hk
    _ ≤ ((NTop.cdiv x D * D : ℕ) : ℝ≥0∞) := by exact_mod_cast cdiv_mul_ge x D hD
    _ = _ := by push_cast; rfl

lemma one_scaled (D H : ℕ) : SerBound D H 1 [D] := by
  intro k _
  rw [PowerSeries.coeff_one]
  cases k with
  | zero => simp
  | succ k => simp

lemma powRound_sound {w D H : ℕ} (hD : 0 < D) {Q : List ℕ} {f : PowerSeries ℝ≥0∞}
    (hf : SerBound D H f Q) :
    ∀ (fuel n : ℕ) (A : List ℕ), powRound w D H Q fuel n = some A → SerBound D H (f ^ n) A
  | 0, n, A, h => by
    unfold powRound at h
    split_ifs at h with hn
    injection h with h
    subst h hn
    simpa using one_scaled D H
  | fuel + 1, n, A, h => by
    unfold powRound at h
    by_cases hn : n = 0
    · rw [ite_eq_left hn] at h
      injection h with h
      subst h hn
      simpa using one_scaled D H
    rw [ite_eq_right hn] at h
    rcases hh : powRound w D H Q fuel (n / 2) with _ | h0
    · rw [hh] at h; simp at h
    rw [hh] at h
    simp only at h
    have ih := powRound_sound hD hf fuel (n / 2) h0 hh
    rcases hs : mulRound w D H h0 h0 with _ | s
    · rw [hs] at h; simp at h
    rw [hs] at h
    simp only at h
    have hsq := mulRound_sound hD hs ih ih
    have hn2 : n = n / 2 + n / 2 + n % 2 := by omega
    by_cases hodd : n % 2 = 1
    · rw [ite_eq_left hodd] at h
      have := mulRound_sound hD h hsq hf
      rw [hn2, hodd, pow_add, pow_add, pow_one]
      exact this
    · rw [ite_eq_right hodd] at h
      injection h with h
      subst h
      have h0' : n % 2 = 0 := by omega
      rw [hn2, h0', add_zero, pow_add]
      exact hsq

/-! ## The root law -/

lemma colSums_getD : ∀ (F : List (List ℕ)) (j : ℕ),
    (colSums F).getD j 0 = ∑ m ∈ range F.length, tab F m j
  | [], j => by simp [colSums]
  | row :: F, j => by
    have ih := colSums_getD F j
    simp only [colSums] at ih ⊢
    rw [List.foldr_cons, addL_getD, ih, List.length_cons, sum_range_succ']
    simp only [tab, List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]

lemma map_snd_scaled {D : ℕ} {F : List (List ℕ)} {G : Measure (ℕ × ℕ)} (hD : 0 < D)
    (hG : Bounded D F G) (j : ℕ) : (G.map Prod.snd) {j} * D ≤ ((colSums F).getD j 0 : ℝ≥0∞) := by
  rw [map_singleton, ← Measure.tsum_indicator_apply_singleton G _ MeasurableSet.of_discrete,
    ENNReal.tsum_prod', colSums_getD]
  have e : ∀ m, ∑' r, (Prod.snd ⁻¹' {j}).indicator (fun x => G {x}) (m, r) = G {(m, j)} := by
    intro m
    rw [← tsum_ite_eq j (fun _ => G {(m, j)})]
    refine tsum_congr fun r => ?_
    by_cases h : r = j
    · subst h; simp
    · rw [Set.indicator_of_notMem (by simpa using h), ite_eq_right h]
  simp_rw [e]
  have hz : ∀ m ∉ range F.length, G {(m, j)} = 0 := by
    intro m hm
    apply mass_zero hD hG
    unfold tab
    rw [mem_range, not_lt] at hm
    have : F.getD m [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hm]; rfl
    rw [this]; rfl
  rw [tsum_eq_sum hz, sum_mul]
  push_cast
  exact sum_le_sum fun m _ => hG m j

/-- `zeroComplete` puts the missing mass at zero. -/
lemma zc_zero (ν : Measure ℕ) : (zeroComplete ν) {0} = ν {0} + (1 - ν Set.univ) := by
  simp [zeroComplete, Measure.dirac_apply_of_mem (Set.mem_singleton (0 : ℕ))]

lemma zc_succ (ν : Measure ℕ) (j : ℕ) : (zeroComplete ν) {j + 1} = ν {j + 1} := by
  rw [zeroComplete, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _
    (measurableSet_singleton _), Set.indicator_of_notMem (by simp)]
  simp

lemma zc_scaled {D : ℕ} {F : List (List ℕ)} {G : Measure (ℕ × ℕ)} (hD : 0 < D)
    (hG : Bounded D F G) (hG1 : G Set.univ ≤ 1) (K : ℕ) :
    SerBound D K (pgf (zeroComplete (G.map Prod.snd))) (D :: (colSums F).tail) := by
  intro k _
  rw [coeff_pgf]
  cases k with
  | zero =>
    rw [zc_zero, List.getD_cons_zero]
    have h1 : (G.map Prod.snd) {0} ≤ (G.map Prod.snd) Set.univ := measure_mono (Set.subset_univ _)
    have h2 : (G.map Prod.snd) Set.univ ≤ 1 := by
      rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ]; exact hG1
    have : (G.map Prod.snd) {0} + (1 - (G.map Prod.snd) Set.univ) ≤ 1 := by
      calc _ ≤ (G.map Prod.snd) Set.univ + (1 - (G.map Prod.snd) Set.univ) := by gcongr
        _ = 1 := add_tsub_cancel_of_le h2
    calc _ ≤ 1 * (D : ℝ≥0∞) := by gcongr
      _ = _ := one_mul _
  | succ j =>
    rw [zc_succ, List.getD_cons_succ]
    have := map_snd_scaled hD hG (j + 1)
    rwa [show (colSums F).getD (j + 1) 0 = ((colSums F).tail).getD j 0 by
      cases colSums F <;> simp] at this

/-! ## The binomial row -/

lemma chooseL_getD (P : ℕ) : ∀ (n j i : ℕ), i < n →
    (chooseL P j (P.choose j) n).getD i 0 = P.choose (j + i)
  | 0, j, i, h => absurd h (Nat.not_lt_zero _)
  | n + 1, j, 0, _ => by simp [chooseL]
  | n + 1, j, i + 1, h => by
    have hc : P.choose j * (P - j) / (j + 1) = P.choose (j + 1) := by
      rw [← Nat.choose_succ_right_eq]; exact Nat.mul_div_cancel _ (by omega)
    rw [chooseL, List.getD_cons_succ, hc, chooseL_getD P n (j + 1) i (by omega)]
    congr 1; omega

lemma chooseL_length (P : ℕ) : ∀ (n j c : ℕ), (chooseL P j c n).length = n
  | 0, _, _ => rfl
  | n + 1, j, c => by simp [chooseL, chooseL_length P n]

lemma binomRow_getD (D P a d H j : ℕ) (hj : j ≤ H) :
    (binomRow D P a d H).getD j 0 =
      NTop.cdiv (D * P.choose j * a ^ j * (d - a) ^ (P - j)) (d ^ P) := by
  have hl : j < (binomRow D P a d H).length := by
    simp [binomRow, chooseL_length]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  simp only [binomRow, List.getElem_zipWith, List.getElem_range]
  have := chooseL_getD P (H + 1) 0 j (by omega)
  rw [Nat.choose_zero_right, zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
    rw [chooseL_length]; omega), Option.getD_some] at this
  rw [this]

lemma binomRow_sound {D P ap dp H : ℕ} {pe : I} (hdp : 0 < dp)
    (hpe : (pe : ℝ) = ap / dp) : SerBound D H (pgf (binomial P pe)) (binomRow D P ap dp H) := by
  intro j hj
  rw [coeff_pgf, binomRow_getD D P ap dp H j hj]
  have hpos : 0 < dp ^ P := Nat.pow_pos hdp
  apply ennreal_cancel hpos
  calc binomial P pe {j} * D * ((dp ^ P : ℕ) : ℝ≥0∞)
      = (binomial P pe {j} * (dp : ℝ≥0∞) ^ P) * D := by push_cast; ring
    _ = ((D * P.choose j * ap ^ j * (dp - ap) ^ (P - j) : ℕ) : ℝ≥0∞) := by
      rw [binom_scaled hdp hpe]; unfold thinCoef; push_cast; ring
    _ ≤ _ := by exact_mod_cast cdiv_mul_ge _ _ hpos

/-! ## The finite part and the tail of the stop-loss -/

lemma stopLoss_split (μ : Measure ℕ) (L H : ℕ) (hLH : L < H + 1) :
    stopLoss μ L ≤ ∑ n ∈ range (H + 1), ((n - L : ℕ) : ℝ≥0∞) * μ {n} +
      ((H + 1 - L : ℕ) : ℝ≥0∞) / 2 ^ (H + 1) * ∫⁻ n, (2 : ℝ≥0∞) ^ n ∂μ := by
  rw [stopLoss, lintegral_countable', lintegral_countable', ← ENNReal.tsum_mul_left]
  have hfin : ∑ n ∈ range (H + 1), ((n - L : ℕ) : ℝ≥0∞) * μ {n} =
      ∑' n, if n < H + 1 then ((n - L : ℕ) : ℝ≥0∞) * μ {n} else 0 := by
    rw [tsum_eq_sum (s := range (H + 1)) (fun n hn => by rw [ite_eq_right (by simpa using hn)])]
    exact sum_congr rfl fun n hn => by rw [ite_eq_left (mem_range.mp hn)]
  rw [hfin, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun n => ?_
  by_cases hn : n < H + 1
  · rw [ite_eq_left hn]; exact le_self_add
  · rw [ite_eq_right hn, zero_add, ← mul_assoc]
    gcongr
    have h := P7aux.tail_real L H n hLH (by omega)
    have h' : ENNReal.ofReal ((n - L : ℕ) : ℝ) ≤
        ENNReal.ofReal (((H + 1 - L : ℕ) : ℝ) / 2 ^ (H + 1) * 2 ^ n) := ENNReal.ofReal_le_ofReal h
    rw [ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos
      (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat] at h'
    exact h'

/-- `E 2^Y`. -/
noncomputable def mgf2 (μ : Measure ℕ) : ℝ≥0∞ := ∫⁻ n, (2 : ℝ≥0∞) ^ n ∂μ

lemma mgf2_conv (μ ν : Measure ℕ) : mgf2 (μ ∗ ν) = mgf2 μ * mgf2 ν := by
  unfold mgf2
  rw [Measure.lintegral_conv Measurable.of_discrete]
  simp_rw [pow_add]
  rw [← lintegral_mul_const _ Measurable.of_discrete]
  exact lintegral_congr fun x => lintegral_const_mul _ Measurable.of_discrete

lemma mgf2_natConvPow (μ : Measure ℕ) : ∀ g, mgf2 (natConvPow μ g) = mgf2 μ ^ g
  | 0 => by simp [mgf2, natConvPow]
  | g + 1 => by rw [natConvPow, mgf2_conv, mgf2_natConvPow μ g, pow_succ]

lemma mgf2_binomial {P ap dp : ℕ} {pe : I} (hdp : 0 < dp) (hpe : (pe : ℝ) = ap / dp) :
    mgf2 (binomial P pe) * (dp : ℝ≥0∞) ^ P = (((dp + ap) ^ P : ℕ) : ℝ≥0∞) := by
  have had := le_of_prob hdp hpe
  unfold mgf2
  rw [lintegral_countable', ← ENNReal.tsum_mul_right]
  have e : ∀ k, (2 : ℝ≥0∞) ^ k * binomial P pe {k} * (dp : ℝ≥0∞) ^ P =
      ((P.choose k * (2 * ap) ^ k * (dp - ap) ^ (P - k) : ℕ) : ℝ≥0∞) := by
    intro k
    rw [mul_assoc, binom_scaled hdp hpe]; unfold thinCoef; push_cast; ring
  simp_rw [e]
  rw [tsum_eq_sum (s := range (P + 1)) (fun k hk => by
    rw [mem_range, not_lt] at hk; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)]
  have : (dp + ap) ^ P = (2 * ap + (dp - ap)) ^ P := by congr 1; omega
  rw [this, add_pow]
  push_cast
  refine sum_congr rfl fun k _ => by ring

lemma mgf2_zc {D : ℕ} {F : List (List ℕ)} {G : Measure (ℕ × ℕ)} (hD : 0 < D)
    (hG : Bounded D F G) (hG1 : G Set.univ ≤ 1) :
    mgf2 (zeroComplete (G.map Prod.snd)) * D ≤
      (D : ℝ≥0∞) + ((evalL (2 : ℕ) (0 :: (colSums F).tail) : ℕ) : ℝ≥0∞) := by
  have hz := zc_scaled hD hG hG1 0
  unfold mgf2
  rw [lintegral_countable', tsum_eq_zero_add' ENNReal.summable, add_mul]
  set cs := (colSums F).tail
  gcongr
  · have := hz 0 le_rfl
    rw [coeff_pgf, List.getD_cons_zero] at this
    simpa using this
  · rw [← ENNReal.tsum_mul_right]
    have hb : ∀ j, (2 : ℝ≥0∞) ^ (j + 1) * (zeroComplete (G.map Prod.snd)) {j + 1} * D ≤
        ((cs.getD j 0 * 2 ^ (j + 1) : ℕ) : ℝ≥0∞) := by
      intro j
      rw [zc_succ, mul_assoc]
      have := map_snd_scaled hD hG (j + 1)
      rw [show (colSums F).getD (j + 1) 0 = cs.getD j 0 by
        simp only [cs]; cases colSums F <;> simp] at this
      push_cast
      rw [mul_comm]
      gcongr
    calc _ ≤ ∑' j, ((cs.getD j 0 * 2 ^ (j + 1) : ℕ) : ℝ≥0∞) := ENNReal.tsum_le_tsum hb
      _ = ∑ j ∈ range cs.length, ((cs.getD j 0 * 2 ^ (j + 1) : ℕ) : ℝ≥0∞) := by
        rw [tsum_eq_sum (s := range cs.length) (fun j hj => by
          rw [mem_range, not_lt] at hj; rw [getD_eq_zero_of_le hj]; simp)]
      _ = _ := by
        rw [evalL, zero_add, evalL_eq_sum, sum_mul]
        push_cast
        refine sum_congr rfl fun j _ => by ring

/-! ## The truncation term -/

lemma eps_sound {D N r H a b t g s : ℕ} {lam : ℝ≥0} (hlam : (lam : ℝ) = a / b) (hD : 0 < D)
    (hb : 0 < b) (hr : 0 < r) (hL : 0 < NTop.lmNum D N r a b) (hab : a < (H + 2) * b)
    (hs : (a * b + a * a) * (2 ^ t - 1) * NTop.pT D a b (NTop.eNum D N r a b) (H + 1) *
      (H + 2) * b * D ≤ s * s * (b * b * ((H + 2) * b - a))) :
    ENNReal.ofReal (g * Real.sqrt (((lam : ℝ) + (lam : ℝ) ^ 2) * (2 ^ t - 1) *
      poissonTail H lam)) ≤ ((g * s : ℕ) : ℝ≥0∞) / D := by
  set pH := NTop.pT D a b (NTop.eNum D N r a b) (H + 1)
  have hpT := NTop.pT_ge hD hb hr (NTop.eNum_ge hD hb hr N hL) (H + 1)
  rw [← hlam] at hpT
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hden : (0 : ℝ) < (H + 2) * b - a := by
    have : (a : ℝ) < (H + 2) * b := by exact_mod_cast hab
    linarith
  have hlam0 : (0 : ℝ) ≤ lam := lam.2
  have hq : (1 : ℝ) - lam / (H + 2) = ((H + 2) * b - a) / ((H + 2) * b) := by
    rw [hlam]; field_simp
  have hq_pos : (0 : ℝ) < 1 - lam / (H + 2) := by
    rw [hq]; positivity
  have htail : poissonTail H lam ≤ (pH : ℝ) / D * ((H + 2) * b / ((H + 2) * b - a)) := by
    calc poissonTail H lam = Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ (H + 1) / ((H + 1).factorial : ℝ) /
          (1 - lam / (H + 2)) := by unfold poissonTail; ring
      _ ≤ ((pH : ℝ) / D) / (1 - lam / (H + 2)) := div_le_div_of_nonneg_right hpT hq_pos.le
      _ = _ := by rw [hq]; field_simp
  have hX : ((lam : ℝ) + (lam : ℝ) ^ 2) * (2 ^ t - 1) * poissonTail H lam ≤ ((s : ℝ) / D) ^ 2 := by
    have h2t : (0 : ℝ) ≤ 2 ^ t - 1 := by
      have : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ (by norm_num); linarith
    calc _ ≤ ((lam : ℝ) + (lam : ℝ) ^ 2) * (2 ^ t - 1) *
          ((pH : ℝ) / D * ((H + 2) * b / ((H + 2) * b - a))) := by gcongr
      _ = ((a * b + a * a) * (2 ^ t - 1) * pH * (H + 2) * b * D : ℝ) /
          (D ^ 2 * (b * b * ((H + 2) * b - a))) := by
        rw [hlam]; field_simp
      _ ≤ ((s * s * (b * b * ((H + 2) * b - a)) : ℕ) : ℝ) / (D ^ 2 * (b * b * ((H + 2) * b - a))) := by
        gcongr
        have hs' : (((a * b + a * a) * (2 ^ t - 1) * pH * (H + 2) * b * D : ℕ) : ℝ) ≤
            ((s * s * (b * b * ((H + 2) * b - a)) : ℕ) : ℝ) := by exact_mod_cast hs
        have e1 : (((2 ^ t - 1 : ℕ)) : ℝ) = 2 ^ t - 1 := by
          rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
        rw [show ((((a * b + a * a) * (2 ^ t - 1) * pH * (H + 2) * b * D : ℕ)) : ℝ) =
          ((a : ℝ) * b + a * a) * (2 ^ t - 1) * pH * (H + 2) * b * D by push_cast [e1]; ring] at hs'
        exact hs'
      _ = ((s : ℝ) / D) ^ 2 := by
        have hden2 : (b : ℝ) * (H + 2) - a ≠ 0 := by nlinarith
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hab.le]
        push_cast
        field_simp
  have hsq : Real.sqrt (((lam : ℝ) + (lam : ℝ) ^ 2) * (2 ^ t - 1) * poissonTail H lam) ≤ s / D := by
    calc _ ≤ Real.sqrt (((s : ℝ) / D) ^ 2) := Real.sqrt_le_sqrt hX
      _ = s / D := Real.sqrt_sq (by positivity)
  calc _ ≤ ENNReal.ofReal ((g : ℝ) * (s / D)) := ENNReal.ofReal_le_ofReal (by gcongr)
    _ = _ := by
      rw [← mul_div_assoc, ENNReal.ofReal_div_of_pos hD', ← Nat.cast_mul, ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]


/-! ## The final check -/

lemma truncTree_univ_le (C : ℕ) (lam : ℝ≥0) (H : ℕ) : ∀ t, truncTree C lam H t Set.univ ≤ 1
  | 0 => by rw [truncTree, measure_univ]
  | 1 => by
    rw [truncTree]
    refine (Measure.restrict_apply_le _ _).trans ?_
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ, measure_univ]
  | t + 2 => by
    simp only [truncTree]
    refine (Measure.restrict_apply_le _ _).trans ?_
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ, conv_univ,
      bind_univ]
    simp_rw [thinPair_univ, lintegral_one]
    have := truncTree_univ_le C lam H (t + 1)
    calc _ ≤ (1 : ℝ≥0∞) * 1 := mul_le_mul' this this
      _ = 1 := one_mul 1

lemma finNum_sound {w H L D : ℕ} {b A : List ℕ} {fin : ℕ} (h : finNum w H L b A = some fin)
    {f g : PowerSeries ℝ≥0∞} (hf : SerBound D H f b) (hg : SerBound D H g A) :
    (∑ n ∈ range (H + 1), ((n - L : ℕ) : ℝ≥0∞) * PowerSeries.coeff n (f * g)) * D * D ≤ fin := by
  unfold finNum at h
  split_ifs at h with hw
  injection h with h
  subst h
  rw [dotL_eq_sum' _ _ (by rw [digitsL_length]), Nat.cast_sum, sum_mul, sum_mul]
  refine sum_le_sum fun n hn => ?_
  have hn' := mem_range.mp hn
  rw [digits_prod hw _ _ hn', getD_map_of_zero (fun i => i - L) 0 (Nat.zero_sub L),
    List.getD_eq_getElem?_getD, List.getElem?_range hn', Option.getD_some, Nat.cast_mul]
  calc ((n - L : ℕ) : ℝ≥0∞) * PowerSeries.coeff n (f * g) * D * D
      = ((n - L : ℕ) : ℝ≥0∞) * (PowerSeries.coeff n (f * g) * D * D) := by ring
    _ ≤ ((n - L : ℕ) : ℝ≥0∞) * ((∑ ij ∈ antidiagonal n, b.getD ij.1 0 * A.getD ij.2 0 : ℕ) : ℝ≥0∞) := by
      gcongr; exact prod_scaled hf hg (by omega)
    _ = _ := mul_comm _ _

/-- `(1 + W2/D)^g ≤ umNum/D`, scaled. -/
lemma pow_mgf_le {x : ℝ≥0∞} {D N r g W2 : ℕ} (hD : 0 < D) (hN : 0 < N) (hr : 0 < r)
    (hW : g * W2 ≤ D * r) (hx : x * D ≤ (D : ℝ≥0∞) + W2) :
    x ^ g * D ≤ (NTop.umNum D N r (g * W2) D : ℝ≥0∞) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hDe : (D : ℝ≥0∞) ≠ 0 := by exact_mod_cast hD.ne'
  have hx' : x ≤ ENNReal.ofReal (1 + (W2 : ℝ) / D) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_div_of_pos hD', ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    rw [ENNReal.le_div_iff_mul_le (Or.inl hDe) (Or.inl (ENNReal.natCast_ne_top D)) |>.symm.trans
      (by rw [ENNReal.add_div, ENNReal.div_self hDe (ENNReal.natCast_ne_top D)])] at hx
    · exact hx
  have he := NTop.exp_upper hD hD hr (a := g * W2) hW hN
  have h1 : (1 + (W2 : ℝ) / D) ^ g ≤ Real.exp ((((g * W2 : ℕ) : ℝ)) / D) := by
    rw [Nat.cast_mul, mul_div_assoc, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ((W2 : ℝ) / D)]) g
  calc x ^ g * D ≤ ENNReal.ofReal (1 + (W2 : ℝ) / D) ^ g * D := by gcongr
    _ = ENNReal.ofReal ((1 + (W2 : ℝ) / D) ^ g * D) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (((NTop.umNum D N r (g * W2) D : ℕ) : ℝ) / D * D) := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
      exact h1.trans he
    _ = _ := by rw [div_mul_cancel₀ _ hD'.ne', ENNReal.ofReal_natCast]

/-- **Soundness of the final check**: for any sub-probability law `G` of node
states bounded by the root table, the stop-loss of `Bin(P, p) ∗ (zero-completed
root loss)^{∗g}` at `L`, plus P10's truncation term, is at most `tn / td`. -/
theorem final_sound {w D N r r' H L g P ap dp a b t fuel tn td s : ℕ} {F : List (List ℕ)}
    (hc : checkFinal w D N r r' H L g P ap dp a b t fuel tn td s F = true)
    {G : Measure (ℕ × ℕ)} (hG : Bounded D F G) (hG1 : G Set.univ ≤ 1)
    {lam : ℝ≥0} (hlam : (lam : ℝ) = a / b) {pe : I} (hpe : (pe : ℝ) = ap / dp) (htd : 0 < td) :
    stopLoss (binomial P pe ∗ natConvPow (zeroComplete (G.map Prod.snd)) g) L +
      ENNReal.ofReal (g * Real.sqrt (((lam : ℝ) + (lam : ℝ) ^ 2) * (2 ^ t - 1) *
        poissonTail H lam)) ≤ (tn : ℝ≥0∞) / td := by
  unfold checkFinal at hc
  rcases hA : powRound w D H (D :: (colSums F).tail) fuel g with _ | A
  · simp [hA] at hc
  rcases hfin : finNum w H L (binomRow D P ap dp H) A with _ | fin
  · simp [hA, hfin] at hc
  simp only [hA, hfin, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hN⟩, hr⟩, hdp⟩, hapdp⟩, hW⟩, hb⟩, hr'⟩, hL⟩, hab⟩, hLH⟩, hs⟩, hfinal⟩ := hc
  set zc := zeroComplete (G.map Prod.snd)
  set cs := (colSums F).tail
  set W2 := evalL 2 (0 :: cs)
  have hDe : (D : ℝ≥0∞) ≠ 0 := by exact_mod_cast hD.ne'
  -- finite part
  have hpow := powRound_sound hD (zc_scaled hD hG hG1 H) fuel g A hA
  have hbin := binomRow_sound (H := H) (P := P) hdp hpe (D := D)
  have hF := finNum_sound hfin hbin hpow
  -- the law's coefficients
  have hcoef : ∀ n, (binomial P pe ∗ natConvPow zc g) {n} =
      PowerSeries.coeff n (pgf (binomial P pe) * pgf zc ^ g) := by
    intro n; rw [← coeff_pgf, pgf_conv, pgf_natConvPow]
  set μ := binomial P pe ∗ natConvPow zc g
  -- tail: `E 2^Y · D · d_p^P ≤ (d_p + a_p)^P · umNum`
  have hmgf : mgf2 μ * D * (dp : ℝ≥0∞) ^ P ≤
      (((dp + ap) ^ P * NTop.umNum D N r (g * W2) D : ℕ) : ℝ≥0∞) := by
    simp only [μ]
    rw [mgf2_conv, mgf2_natConvPow]
    have h1 := mgf2_binomial (P := P) hdp hpe
    have h2 := pow_mgf_le hD hN hr hW (mgf2_zc hD hG hG1)
    calc mgf2 (binomial P pe) * mgf2 zc ^ g * D * (dp : ℝ≥0∞) ^ P
        = (mgf2 (binomial P pe) * (dp : ℝ≥0∞) ^ P) * (mgf2 zc ^ g * D) := by ring
      _ ≤ (((dp + ap) ^ P : ℕ) : ℝ≥0∞) * (NTop.umNum D N r (g * W2) D : ℝ≥0∞) := by
        rw [h1]; gcongr
      _ = _ := by push_cast; ring
  have htail : ((H + 1 - L : ℕ) : ℝ≥0∞) / 2 ^ (H + 1) * mgf2 μ * D ≤
      (tailNum D N r H L g P ap dp W2 : ℝ≥0∞) := by
    have hq : 0 < 2 ^ (H + 1) * dp ^ P := Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos hdp)
    have hcd := cdiv_mul_ge ((H + 1 - L) * (dp + ap) ^ P * NTop.umNum D N r (g * W2) D)
      (2 ^ (H + 1) * dp ^ P) hq
    apply ennreal_cancel hq
    have hc0 : (2 : ℝ≥0∞) ^ (H + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
    have hct : (2 : ℝ≥0∞) ^ (H + 1) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    calc ((H + 1 - L : ℕ) : ℝ≥0∞) / 2 ^ (H + 1) * mgf2 μ * D * ((2 ^ (H + 1) * dp ^ P : ℕ) : ℝ≥0∞)
        = (((H + 1 - L : ℕ) : ℝ≥0∞) / 2 ^ (H + 1) * 2 ^ (H + 1)) *
          (mgf2 μ * D * (dp : ℝ≥0∞) ^ P) := by push_cast; ring
      _ = ((H + 1 - L : ℕ) : ℝ≥0∞) * (mgf2 μ * D * (dp : ℝ≥0∞) ^ P) := by
        rw [ENNReal.div_mul_cancel hc0 hct]
      _ ≤ ((H + 1 - L : ℕ) : ℝ≥0∞) *
          (((dp + ap) ^ P * NTop.umNum D N r (g * W2) D : ℕ) : ℝ≥0∞) := by gcongr
      _ = (((H + 1 - L) * (dp + ap) ^ P * NTop.umNum D N r (g * W2) D : ℕ) : ℝ≥0∞) := by
        push_cast; ring
      _ ≤ _ := by unfold tailNum; exact_mod_cast hcd
  -- the stop-loss, scaled by `D^2`
  have hSL : stopLoss μ L * D * D ≤ (fin : ℝ≥0∞) + D * tailNum D N r H L g P ap dp W2 := by
    have hsplit := stopLoss_split μ L H hLH
    simp_rw [hcoef] at hsplit
    calc stopLoss μ L * D * D
        ≤ (∑ n ∈ range (H + 1), ((n - L : ℕ) : ℝ≥0∞) *
            PowerSeries.coeff n (pgf (binomial P pe) * pgf zc ^ g) +
          ((H + 1 - L : ℕ) : ℝ≥0∞) / 2 ^ (H + 1) * mgf2 μ) * D * D := by
          gcongr; exact hsplit
      _ = (∑ n ∈ range (H + 1), ((n - L : ℕ) : ℝ≥0∞) *
            PowerSeries.coeff n (pgf (binomial P pe) * pgf zc ^ g)) * D * D +
          D * (((H + 1 - L : ℕ) : ℝ≥0∞) / 2 ^ (H + 1) * mgf2 μ * D) := by ring
      _ ≤ _ := by gcongr
  -- the truncation term, scaled by `D^2`
  have heps := eps_sound (g := g) hlam hD hb hr' hL hab hs
  have heps' : ENNReal.ofReal (g * Real.sqrt (((lam : ℝ) + (lam : ℝ) ^ 2) * (2 ^ t - 1) *
      poissonTail H lam)) * D * D ≤ D * (g * s : ℕ) := by
    have : ENNReal.ofReal (g * Real.sqrt (((lam : ℝ) + (lam : ℝ) ^ 2) * (2 ^ t - 1) *
        poissonTail H lam)) * D ≤ (g * s : ℕ) := by
      calc _ ≤ ((g * s : ℕ) : ℝ≥0∞) / D * D := by gcongr
        _ = _ := ENNReal.div_mul_cancel hDe (ENNReal.natCast_ne_top D)
    calc _ = D * (ENNReal.ofReal (g * Real.sqrt (((lam : ℝ) + (lam : ℝ) ^ 2) * (2 ^ t - 1) *
        poissonTail H lam)) * D) := by ring
      _ ≤ _ := by gcongr
  -- combine
  have htd' : (td : ℝ≥0∞) ≠ 0 := by exact_mod_cast htd.ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl htd') (Or.inl (ENNReal.natCast_ne_top td))]
  have hDD : 0 < D * D := Nat.mul_pos hD hD
  apply ennreal_cancel hDD
  have hfinal' : (((fin + D * (tailNum D N r H L g P ap dp W2 + g * s)) * td : ℕ) : ℝ≥0∞) ≤
      ((tn * D ^ 2 : ℕ) : ℝ≥0∞) := by exact_mod_cast hfinal
  calc (stopLoss μ L + ENNReal.ofReal (g * Real.sqrt (((lam : ℝ) + (lam : ℝ) ^ 2) * (2 ^ t - 1) *
        poissonTail H lam))) * td * ((D * D : ℕ) : ℝ≥0∞)
      = (stopLoss μ L * D * D + ENNReal.ofReal (g * Real.sqrt (((lam : ℝ) + (lam : ℝ) ^ 2) *
          (2 ^ t - 1) * poissonTail H lam)) * D * D) * td := by push_cast; ring
    _ ≤ (((fin : ℝ≥0∞) + D * tailNum D N r H L g P ap dp W2) + D * (g * s : ℕ)) * td := by
      gcongr
    _ = (((fin + D * (tailNum D N r H L g P ap dp W2 + g * s)) * td : ℕ) : ℝ≥0∞) := by
      push_cast; ring
    _ ≤ ((tn * D ^ 2 : ℕ) : ℝ≥0∞) := hfinal'
    _ = _ := by push_cast; ring

end RebuildBound.NCA1
