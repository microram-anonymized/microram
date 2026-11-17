import RebuildBound.Proofs.NCA5.Checker
import RebuildBound.Proofs.NCA1.Series
import RebuildBound.Spec.Prob.TruncRadix

/-!
# Soundness of the terminal radix checkers (package NCA5)

`Bounded D F μ` (NCA1): every point mass of `μ`, scaled by `D`, is at most the
table entry `F[m][r]`. For every thinning probability `α/d`, cap `C`, cutoff
`K`, scale `D` and digit width `w`:

* `thin_sound`: `checkThin` turns a bound of `μ` into a bound of
  `μ.bind (thinPair (α/d))`; the exact thinned coefficients are NCA1's `thinP`
  (`child_bound`), read off the packed integers as base-`2^w` digits;
* `conv_sound`: `checkConv` turns bounds of `μ` and `ν` into a bound of
  `(μ ∗ ν).restrict (lowTotal K)`;
* `rootMarg_sound`: the root-loss marginal `v + (u - C)₊` of a bounded law is
  bounded by `rootMarg C`;
* `truncPairConvPow_one`, `truncPairConvPow_univ_le`: the first partial sum and
  the sub-probability property of `truncPairConvPow`;
* `oneRow_bounded`: a law on `ℕ` bounded by a list is the second marginal of a
  law on `ℕ × ℕ` bounded by a one-row table, so NCA1's `final_sound` applies;
* `poissonTail_le`, `eps_le`: the truncation term of P10r through
  `e^-ν ≤ 1` and monotonicity in `ν`.
-/

open MeasureTheory ProbabilityTheory Finset Polynomial RebuildBound.Spec
open scoped ENNReal NNReal unitInterval BigOperators

namespace RebuildBound.NCA5

open RebuildBound.NCA1

/-! ## Thinning -/

lemma thinOut_X (a d K : ℕ) (F : List (List ℕ)) : thinOut (X : ℕ[X]) a d K F = thinP a d K F :=
  rfl

lemma thinOut_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (x : R)
    (a d K : ℕ) (F : List (List ℕ)) : (thinOut x a d K F).map φ = thinOut (φ x) a d K F := by
  simp only [thinOut, mthin_map, rows_map, basis_map, map_natCast]

/-- **Soundness of the thinning check**, for every thinning probability `α/d`,
cutoffs `Z`, `K`, scale `D` and digit width `w`. -/
theorem thin_sound {w a d D Z K : ℕ} {p : I} (hd : 0 < d) (hp : (p : ℝ) = a / d) (hD : 0 < D)
    {F T : List (List ℕ)} (hc : checkThin w a d Z K F T = true) {μ : Measure (ℕ × ℕ)}
    (hμ : Bounded D F μ) : Bounded D T (μ.bind (thinPair p)) := by
  unfold checkThin at hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at hc
  obtain ⟨⟨⟨hF, hrows⟩, hbound⟩, hrow⟩ := hc
  intro i b
  have hO := child_bound hd hp hD hF hrows hμ i b
  set c : ℕ := d ^ (Z + K) with hc_def
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.pow_pos hd).ne'
  have hDc : (D : ℝ≥0∞) * (d : ℝ≥0∞) ^ (Z + K) = (D : ℝ≥0∞) * c := by
    simp only [c]; push_cast; ring
  rw [hDc, ← mul_assoc] at hO
  suffices hcoef : (((thinP a d K F).getD i 0).coeff b : ℝ≥0∞) ≤ (tab T i b : ℝ≥0∞) * c from
    (ENNReal.mul_le_mul_iff_left hc0 (ENNReal.natCast_ne_top _)).mp (hO.trans hcoef)
  by_cases hi : i ≤ Z
  · by_cases hb : b ≤ K
    · have hev : ∀ x : ℕ, thinOut x a d K F = (thinP a d K F).map (Polynomial.evalRingHom x) := by
        intro x; rw [← thinOut_X, thinOut_map]; simp
      have h1 : ((thinP a d K F).getD i 0).eval 1 < 2 ^ w := by
        have := lt_of_all_lt (Nat.two_pow_pos w) hbound i
        rw [hev 1, getD_map_zero] at this
        simpa using this
      have hdig : ((thinP a d K F).getD i 0).coeff b =
          (digitsL w (K + 1) ((thinOut (2 ^ w) a d K F).getD i 0)).getD b 0 := by
        rw [hev (2 ^ w), getD_map_zero, coe_evalRingHom, digit_of_eval_one h1 _ _ (by omega)]
      have hle := rowLe_spec _ _ _ (hrow i (by omega)) b (by rw [digitsL_length]; omega)
      rw [← hdig] at hle
      exact_mod_cast hle
    · have h0 : ((thinP a d K F).getD i 0).coeff b = 0 := by
        rw [coeff_thinP a d K hF hrows]
        refine sum_eq_zero fun m _ => sum_eq_zero fun r hr => ?_
        have : r < b := by have := mem_range.mp hr; omega
        simp [thinCoef, Nat.choose_eq_zero_of_lt this]
      rw [h0]; simp
  · have h0 : (thinP a d K F).getD i 0 = 0 :=
      getD_eq_zero_of_le (by rw [thinP_length, hF]; omega)
    rw [h0]; simp

/-! ## One partial sum of the radix node -/

lemma rows_lpoly_map (x : ℕ) (A : List (List ℕ)) :
    (A.map lpoly).map (Polynomial.evalRingHom x) = A.map (evalL x) := by
  rw [List.map_map]
  exact List.map_congr_left fun l _ => by simp [eval_lpoly]

lemma coeff_convL_lpoly (A B : List (List ℕ)) (u v : ℕ) :
    ((convL (A.map lpoly) (B.map lpoly)).getD u 0).coeff v =
      ∑ ij ∈ antidiagonal u, ∑ kl ∈ antidiagonal v, tab A ij.1 kl.1 * tab B ij.2 kl.2 := by
  rw [convL_getD, finsetSum_coeff]
  refine sum_congr rfl fun ij _ => ?_
  rw [getD_map_of_zero lpoly [] lpoly_nil, getD_map_of_zero lpoly [] lpoly_nil, coeff_mul]
  refine sum_congr rfl fun kl _ => ?_
  rw [coeff_lpoly, coeff_lpoly]
  rfl

/-- **Soundness of the convolution check**, for every cutoff `K`, scale `D` and
digit width `w`. -/
theorem conv_sound {w D K : ℕ} (hD : 0 < D) {A B A' : List (List ℕ)}
    (hc : checkConv w D K A B A' = true) {μ ν : Measure (ℕ × ℕ)} (hμ : Bounded D A μ)
    (hν : Bounded D B ν) : Bounded D A' ((μ ∗ ν).restrict (lowTotal K)) := by
  unfold checkConv at hc
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at hc
  obtain ⟨hbound, hrow⟩ := hc
  intro u v
  rw [restrict_singleton]
  by_cases hx : (u, v) ∈ lowTotal K
  swap
  · rw [Set.indicator_of_notMem hx, zero_mul]; exact zero_le
  rw [Set.indicator_of_mem hx]
  have huv : u + v ≤ K := hx
  have hev : ∀ x : ℕ, convL (A.map (evalL x)) (B.map (evalL x)) =
      (convL (A.map lpoly) (B.map lpoly)).map (Polynomial.evalRingHom x) := by
    intro x; rw [convL_map, rows_lpoly_map, rows_lpoly_map]
  have h1 : ((convL (A.map lpoly) (B.map lpoly)).getD u 0).eval 1 < 2 ^ w := by
    have hs : ∀ L : List (List ℕ), L.map List.sum = L.map (evalL 1) := fun L =>
      List.map_congr_left fun l _ => (evalL_one l).symm
    have := lt_of_all_lt (Nat.two_pow_pos w) hbound u
    rw [hs, hs, hev 1, getD_map_zero] at this
    simpa using this
  have hdig : ((convL (A.map lpoly) (B.map lpoly)).getD u 0).coeff v =
      (digitsL w (K + 1 - u) ((convL (A.map (evalL (2 ^ w))) (B.map (evalL (2 ^ w)))).getD u 0)).getD
        v 0 := by
    rw [hev, getD_map_zero, coe_evalRingHom, digit_of_eval_one h1 _ _ (by omega)]
  have hle := rowLe_spec _ _ _ (hrow u (by omega)) v (by rw [digitsL_length]; omega)
  rw [← hdig, coeff_convL_lpoly] at hle
  apply ennreal_cancel hD
  calc (μ ∗ ν) {(u, v)} * D * D
      ≤ ((∑ ij ∈ antidiagonal u, ∑ kl ∈ antidiagonal v,
          tab A ij.1 kl.1 * tab B ij.2 kl.2 : ℕ) : ℝ≥0∞) := by
        rw [conv_singleton_pair, sum_mul, sum_mul]
        push_cast
        refine sum_le_sum fun ij _ => ?_
        rw [sum_mul, sum_mul]
        refine sum_le_sum fun kl _ => ?_
        calc μ {(ij.1, kl.1)} * ν {(ij.2, kl.2)} * D * D
            = (μ {(ij.1, kl.1)} * D) * (ν {(ij.2, kl.2)} * D) := by ring
          _ ≤ _ := mul_le_mul' (hμ _ _) (hν _ _)
    _ ≤ ((tab A' u v * D : ℕ) : ℝ≥0∞) := by exact_mod_cast hle
    _ = _ := by push_cast; rfl

/-! ## The root-loss marginal -/

lemma shiftSum_getD : ∀ (rows : List (List ℕ)) (z : ℕ),
    (shiftSum rows).getD z 0 = ∑ i ∈ range (z + 1), tab rows i (z - i)
  | [], z => by simp [shiftSum, tab]
  | r :: rs, 0 => by
    rw [shiftSum, addL_getD]
    simp [tab]
  | r :: rs, z + 1 => by
    rw [shiftSum, addL_getD, List.getD_cons_succ, shiftSum_getD rs z]
    symm
    rw [sum_range_succ']
    simp only [tab, List.getD_cons_succ, List.getD_cons_zero, Nat.sub_zero,
      Nat.add_sub_add_right]
    rw [add_comm]

lemma colSums_take_getD : ∀ (C : ℕ) (A : List (List ℕ)) (z : ℕ),
    (colSums (A.take C)).getD z 0 = ∑ u ∈ range C, tab A u z
  | 0, A, z => by simp [colSums]
  | C + 1, [], z => by simp [colSums, tab]
  | C + 1, a :: A, z => by
    rw [List.take_succ_cons, colSums, List.foldr_cons, addL_getD, sum_range_succ']
    have := colSums_take_getD C A z
    simp only [colSums] at this
    rw [this]
    simp only [tab, List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]

lemma rootMarg_getD (C : ℕ) (A : List (List ℕ)) (z : ℕ) :
    (rootMarg C A).getD z 0 =
      ∑ u ∈ range C, tab A u z + ∑ i ∈ range (z + 1), tab A (C + i) (z - i) := by
  rw [rootMarg, addL_getD, colSums_take_getD, shiftSum_getD]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  have : (A.drop C).getD i [] = A.getD (C + i) [] := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  simp only [tab, this]

/-- **The root-loss marginal**: for a law bounded by `A`, the law of
`v + (u - C)₊` is bounded by `rootMarg C A`. -/
theorem rootMarg_sound {D C : ℕ} {A : List (List ℕ)} {μ : Measure (ℕ × ℕ)}
    (hμ : Bounded D A μ) (z : ℕ) :
    (μ.map fun s => s.2 + (s.1 - C)) {z} * D ≤ ((rootMarg C A).getD z 0 : ℝ≥0∞) := by
  rw [NCA1.map_singleton, rootMarg_getD]
  set S₁ := (range C).image fun u => (u, z)
  set S₂ := (range (z + 1)).image fun i => (C + i, z - i)
  have hsub : (fun s : ℕ × ℕ => s.2 + (s.1 - C)) ⁻¹' {z} ⊆ (↑S₁ : Set (ℕ × ℕ)) ∪ ↑S₂ := by
    rintro ⟨u, v⟩ h
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h
    simp only [S₁, S₂, coe_image, coe_range, Set.mem_union, Set.mem_image, Set.mem_Iio,
      Prod.mk.injEq]
    by_cases hu : u < C
    · left; exact ⟨u, hu, rfl, by omega⟩
    · right; exact ⟨u - C, by omega, by omega, by omega⟩
  have hi₁ : Set.InjOn (fun u => (u, z)) (↑(range C) : Set ℕ) := by
    intro i _ j _ h; simpa using h
  have hi₂ : Set.InjOn (fun i => (C + i, z - i)) (↑(range (z + 1)) : Set ℕ) := by
    intro i _ j _ h; simp only [Prod.mk.injEq] at h; omega
  calc μ ((fun s : ℕ × ℕ => s.2 + (s.1 - C)) ⁻¹' {z}) * D
      ≤ (μ ↑S₁ + μ ↑S₂) * D := by gcongr; exact (measure_mono hsub).trans (measure_union_le _ _)
    _ = (∑ u ∈ range C, μ {(u, z)}) * D + (∑ i ∈ range (z + 1), μ {(C + i, z - i)}) * D := by
      rw [measure_finset, measure_finset, sum_image hi₁, sum_image hi₂, add_mul]
    _ ≤ ∑ u ∈ range C, (tab A u z : ℝ≥0∞) + ∑ i ∈ range (z + 1), (tab A (C + i) (z - i) : ℝ≥0∞) := by
      rw [sum_mul, sum_mul]
      gcongr with u _ i _
      · exact hμ u z
      · exact hμ (C + i) (z - i)
    _ = _ := by push_cast; rfl

/-! ## One-row tables -/

lemma addL_nil_right {R : Type*} [CommSemiring R] (l : List R) : addL l [] = l := by
  cases l <;> rfl

lemma colSums_single (R : List ℕ) : colSums [R] = R := by
  simp [colSums, addL_nil_right]

/-- A law on `ℕ` bounded by the list `R` gives a law on `ℕ × ℕ` bounded by `[R]`. -/
lemma oneRow_bounded {D : ℕ} {R : List ℕ} {ρ : Measure ℕ}
    (h : ∀ z, ρ {z} * D ≤ (R.getD z 0 : ℝ≥0∞)) :
    Bounded D [R] (ρ.map fun z => ((0 : ℕ), z)) := by
  intro m r
  rw [NCA1.map_singleton]
  cases m with
  | zero =>
    have : (fun z => ((0 : ℕ), z)) ⁻¹' {((0 : ℕ), r)} = {r} := by ext z; simp
    rw [this]
    exact h r
  | succ m =>
    have : (fun z => ((0 : ℕ), z)) ⁻¹' {(m + 1, r)} = ∅ := by ext z; simp
    rw [this, measure_empty, zero_mul]
    exact zero_le

lemma oneRow_snd (ρ : Measure ℕ) : (ρ.map fun z => ((0 : ℕ), z)).map Prod.snd = ρ := by
  rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  exact Measure.map_id

lemma oneRow_univ (ρ : Measure ℕ) : (ρ.map fun z => ((0 : ℕ), z)) Set.univ = ρ Set.univ := by
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ]

/-! ## The truncated radix sum -/

lemma bounded_restrict {D : ℕ} {F : List (List ℕ)} {μ : Measure (ℕ × ℕ)} (h : Bounded D F μ)
    (s : Set (ℕ × ℕ)) : Bounded D F (μ.restrict s) :=
  fun m r => (mul_le_mul_left (Measure.restrict_apply_le _ _) _).trans (h m r)

lemma truncPairConvPow_one (H : ℕ) (ν : Measure (ℕ × ℕ)) [SFinite ν] :
    truncPairConvPow H ν 1 = ν.restrict (lowTotal H) := by
  rw [truncPairConvPow, truncPairConvPow, ← Prod.zero_eq_mk, Measure.dirac_zero_conv]

lemma truncPairConvPow_univ_le (H : ℕ) {ν : Measure (ℕ × ℕ)} (hν : ν Set.univ ≤ 1) :
    ∀ n, truncPairConvPow H ν n Set.univ ≤ 1
  | 0 => by simp [truncPairConvPow]
  | n + 1 => by
    have : IsFiniteMeasure ν := ⟨hν.trans_lt ENNReal.one_lt_top⟩
    rw [truncPairConvPow]
    refine (Measure.restrict_apply_le _ _).trans ?_
    rw [conv_univ]
    calc _ ≤ (1 : ℝ≥0∞) * 1 := mul_le_mul' (truncPairConvPow_univ_le H hν n) hν
      _ = 1 := one_mul 1

lemma bind_thinPair_univ_le {μ : Measure (ℕ × ℕ)} (hμ : μ Set.univ ≤ 1) (p : I) :
    (μ.bind (thinPair p)) Set.univ ≤ 1 := by
  rw [bind_univ]
  simp_rw [thinPair_univ, lintegral_one]
  exact hμ

/-! ## The truncation term of P10r -/

lemma poissonTail_le {H : ℕ} {ν m : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ m) (h2 : m < H + 2) :
    poissonTail H ν ≤ m ^ (H + 1) / (H + 1).factorial / (1 - m / (H + 2)) := by
  unfold poissonTail
  have hH : (0 : ℝ) < H + 2 := by positivity
  have hq : 0 < 1 - m / (H + 2) := by rw [sub_pos, div_lt_one hH]; exact h2
  have hq' : 1 - m / (H + 2) ≤ 1 - ν / (H + 2) := by gcongr
  have he : Real.exp (-ν) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hf : (0 : ℝ) < (H + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  calc Real.exp (-ν) * ν ^ (H + 1) / (H + 1).factorial / (1 - ν / (H + 2))
      ≤ 1 * m ^ (H + 1) / (H + 1).factorial / (1 - m / (H + 2)) := by
        have hm : 0 ≤ m := h0.trans h1
        gcongr
    _ = _ := by rw [one_mul]

lemma poissonTail_nonneg {H : ℕ} {ν : ℝ} (h0 : 0 ≤ ν) (h : ν < H + 2) : 0 ≤ poissonTail H ν := by
  unfold poissonTail
  have : ν / (H + 2) < 1 := by rw [div_lt_one (by positivity)]; exact h
  have : (0 : ℝ) < 1 - ν / (H + 2) := by linarith
  positivity

/-- `g √X ≤ g y` from `X ≤ y²`. -/
lemma eps_le {g X y : ℝ} (hg : 0 ≤ g) (hy : 0 ≤ y) (hX : X ≤ y ^ 2) :
    ENNReal.ofReal (g * Real.sqrt X) ≤ ENNReal.ofReal (g * y) := by
  apply ENNReal.ofReal_le_ofReal
  gcongr
  calc Real.sqrt X ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt hX
    _ = y := Real.sqrt_sq hy

end RebuildBound.NCA5
