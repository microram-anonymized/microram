import RebuildBound.Proofs.NCA1.Poly
import RebuildBound.Proofs.NCA1.Mass

/-!
# Soundness of `checkLevel` and `checkInit` (package NCA1)

`Bounded D F μ`: every point mass of `μ`, scaled by `D`, is at most the table
entry `F[m][r]`. `level_sound`: if `checkLevel` accepts `F → F'` and `μ` is
bounded by `F`, then the next truncated level of `μ` (thin by `α/d`,
self-convolve, cap at `Z`, restrict to totals `≤ K`) is bounded by `F'`. For
every thinning probability `α/d`, cap `Z`, cutoff `K`, scale `D` and width `w`.
`base_sound`: the same for the depth-one law against `checkInit`.

The checker's packed integers are the values at `2^w` of the polynomials
`thinP`, `sqP` (`levelOut_map`); the point masses are bounded by their
coefficients (`child_bound`, `conv_bound`, `map_bound`), and the coefficients
are the base-`2^w` digits since their sum (the value at `1`) is `< 2^w`.
-/

open MeasureTheory ProbabilityTheory Finset Polynomial RebuildBound.Spec
open scoped ENNReal NNReal unitInterval BigOperators

namespace RebuildBound.NCA1

/-- Table entry `F[m][r]` (zero outside the table). -/
def tab (F : List (List ℕ)) (m r : ℕ) : ℕ := (F.getD m []).getD r 0

/-- `μ ≤ F / D` pointwise. -/
def Bounded (D : ℕ) (F : List (List ℕ)) (μ : Measure (ℕ × ℕ)) : Prop :=
  ∀ m r, μ {(m, r)} * D ≤ tab F m r

/-! ## Lists -/

section Lists
variable {R : Type*} [CommSemiring R]

lemma addL_length : ∀ (l₁ l₂ : List R), (addL l₁ l₂).length = max l₁.length l₂.length
  | [], l => by simp [addL]
  | a :: as, [] => by simp [addL]
  | a :: as, b :: bs => by simp [addL, addL_length as bs, Nat.succ_max_succ]

lemma mthin_length (α β d : R) : ∀ (rs : List R), (mthin α β d rs).length = rs.length
  | [] => rfl
  | r :: rest => by
    simp [mthin, addL_length, mulLin, smulL, mthin_length α β d rest]

lemma convL_length_ge : ∀ (p q : List R), q ≠ [] → p.length ≤ (convL p q).length
  | [], _, _ => by simp
  | a :: as, q, hq => by
    have := convL_length_ge as q hq
    simp only [convL, addL_length, smulL, List.length_map, List.length_cons]
    omega

lemma getD_map_cast (l : List ℕ) (i : ℕ) :
    (l.map (Nat.cast : ℕ → R)).getD i 0 = ((l.getD i 0 : ℕ) : R) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

lemma getD_map_of_zero {α : Type*} (f : α → R) (d : α) (hf : f d = 0) (l : List α) (i : ℕ) :
    (l.map f).getD i 0 = f (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hf]

lemma basis_getD (x : R) (a d K r : ℕ) (hr : r < K + 1) :
    (basis x a d K).getD r 0 = (d : R) ^ (K - r) * (((d - a : ℕ) : R) + (a : R) * x) ^ r := by
  rw [basis, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr]
  rfl

lemma getD_drop' (l : List R) (n i : ℕ) : (l.drop n).getD i 0 = l.getD (n + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

end Lists

lemma lt_of_all_lt {l : List ℕ} {B : ℕ} (hB : 0 < B) (h : ∀ x ∈ l, x < B) (m : ℕ) :
    l.getD m 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  cases hm : l[m]? with
  | none => simpa using hB
  | some x => exact h x (List.mem_of_getElem? hm)

lemma rowLe_spec (c : ℕ) : ∀ (xs ys : List ℕ), rowLe c xs ys = true →
    ∀ v < xs.length, xs.getD v 0 ≤ ys.getD v 0 * c
  | [], _, _, v, hv => absurd hv (Nat.not_lt_zero _)
  | x :: xs, [], h, v, hv => by
    simp only [rowLe, Bool.and_eq_true, beq_iff_eq] at h
    cases v with
    | zero => simp [h.1]
    | succ v =>
      have := rowLe_spec c xs [] h.2 v (by simpa using hv)
      simpa using this
  | x :: xs, y :: ys, h, v, hv => by
    simp only [rowLe, Bool.and_eq_true, decide_eq_true_eq] at h
    cases v with
    | zero => simpa using h.1
    | succ v => simpa using rowLe_spec c xs ys h.2 v (by simpa using hv)

/-! ## The polynomials of one level -/

lemma C_nat (n : ℕ) : (C n : ℕ[X]) = (n : ℕ[X]) := by
  have := map_natCast (C : ℕ →+* ℕ[X]) n
  rwa [Nat.cast_id] at this

lemma getD_row_length {F : List (List ℕ)} {K : ℕ} (hrows : ∀ row ∈ F, row.length ≤ K + 1) (m : ℕ) :
    (F.getD m []).length ≤ K + 1 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : F[m]? with
  | none => simp
  | some row => exact hrows row (List.mem_of_getElem? h)

section Poly
variable (a d K : ℕ)

/-- Row `m` thinned along the shadow count: `Σ_r F[m][r] d^(K-r) (β + α X)^r`. -/
noncomputable def rowP (row : List ℕ) : ℕ[X] := dotL (row.map Nat.cast) (basis X a d K)

/-- Both coordinates thinned: entry `i` is the polynomial of main count `i`. -/
noncomputable def thinP (F : List (List ℕ)) : List ℕ[X] :=
  mthin (a : ℕ[X]) ((d - a : ℕ) : ℕ[X]) (d : ℕ[X]) (F.map (rowP a d K))

/-- The joint self-convolution: entry `u` is the polynomial of main count `u`. -/
noncomputable def sqP (F : List (List ℕ)) : List ℕ[X] := convL (thinP a d K F) (thinP a d K F)

lemma levelOut_X (Z : ℕ) (F : List (List ℕ)) :
    levelOut (X : ℕ[X]) a d Z K F = (sqP a d K F).take Z ++ [evalL X ((sqP a d K F).drop Z)] := rfl

lemma rowP_nil : rowP a d K [] = 0 := rfl

lemma coeff_rowP (row : List ℕ) (hrow : row.length ≤ K + 1) (b : ℕ) :
    (rowP a d K row).coeff b =
      ∑ r ∈ range (K + 1), row.getD r 0 * (d ^ (K - r) * thinCoef a d r b) := by
  rw [rowP, dotL_eq_sum' _ _ (by simpa using hrow), finsetSum_coeff]
  refine sum_congr rfl fun r hr => ?_
  rw [getD_map_cast, basis_getD _ _ _ _ _ (mem_range.mp hr)]
  have e : ((row.getD r 0 : ℕ) : ℕ[X]) * ((d : ℕ[X]) ^ (K - r) *
      (((d - a : ℕ) : ℕ[X]) + (a : ℕ[X]) * X) ^ r) =
      C (row.getD r 0 * d ^ (K - r)) * (C ((d - a : ℕ)) + C (a : ℕ) * X) ^ r := by
    simp only [map_mul, map_pow, C_nat]; ring
  rw [e, coeff_C_mul, coeff_lin_pow]
  simp only [thinCoef, Nat.cast_id]
  ring

lemma coeff_thinP {Z : ℕ} {F : List (List ℕ)} (hF : F.length = Z + 1)
    (hrows : ∀ row ∈ F, row.length ≤ K + 1) (i b : ℕ) :
    ((thinP a d K F).getD i 0).coeff b = ∑ m ∈ range (Z + 1), ∑ r ∈ range (K + 1),
      tab F m r * (d ^ (Z - m) * thinCoef a d m i) * (d ^ (K - r) * thinCoef a d r b) := by
  rw [thinP, mthin_getD, List.length_map, hF, finsetSum_coeff]
  refine sum_congr rfl fun m hm => ?_
  rw [getD_map_of_zero (rowP a d K) [] (rowP_nil a d K)]
  have hlen := getD_row_length hrows m
  have e : rowP a d K (F.getD m []) * (d : ℕ[X]) ^ (Z + 1 - 1 - m) *
      (((m.choose i : ℕ) : ℕ[X]) * (a : ℕ[X]) ^ i * ((d - a : ℕ) : ℕ[X]) ^ (m - i)) =
      rowP a d K (F.getD m []) * C (d ^ (Z - m) * thinCoef a d m i) := by
    simp only [map_mul, map_pow, C_nat, thinCoef, Nat.add_sub_cancel]
    ring
  rw [e, coeff_mul_C, coeff_rowP a d K _ hlen, sum_mul]
  refine sum_congr rfl fun r _ => ?_
  simp only [tab]
  ring

lemma coeff_sqP (F : List (List ℕ)) (u v : ℕ) :
    ((sqP a d K F).getD u 0).coeff v = ∑ ij ∈ antidiagonal u, ∑ kl ∈ antidiagonal v,
      ((thinP a d K F).getD ij.1 0).coeff kl.1 * ((thinP a d K F).getD ij.2 0).coeff kl.2 := by
  rw [sqP, convL_getD, finsetSum_coeff]
  exact sum_congr rfl fun ij _ => coeff_mul _ _ _

lemma coeff_evalL_X (l : List ℕ[X]) (v : ℕ) :
    (evalL X l).coeff v = ∑ i ∈ range (v + 1), (l.getD i 0).coeff (v - i) := by
  rw [evalL_eq_sum' X l (le_max_left l.length (v + 1)), finsetSum_coeff]
  simp_rw [coeff_mul_X_pow']
  rw [sum_ite, sum_const_zero, add_zero]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  omega

lemma thinP_length (F : List (List ℕ)) : (thinP a d K F).length = F.length := by
  rw [thinP, mthin_length, List.length_map]

lemma levelOut_X_getD_lt {Z : ℕ} {F : List (List ℕ)} (hF : F.length = Z + 1) {m : ℕ} (hm : m < Z) :
    (levelOut (X : ℕ[X]) a d Z K F).getD m 0 = (sqP a d K F).getD m 0 := by
  have hne : thinP a d K F ≠ [] := by
    intro h; have := thinP_length a d K F; rw [h, hF] at this; simp at this
  have hlen : Z < (sqP a d K F).length := by
    have := convL_length_ge (thinP a d K F) (thinP a d K F) hne
    rw [thinP_length, hF] at this
    exact lt_of_lt_of_le (Nat.lt_succ_self Z) this
  rw [levelOut_X, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hm]

lemma levelOut_X_getD_Z {Z : ℕ} {F : List (List ℕ)} (hF : F.length = Z + 1) :
    (levelOut (X : ℕ[X]) a d Z K F).getD Z 0 = evalL X ((sqP a d K F).drop Z) := by
  have hne : thinP a d K F ≠ [] := by
    intro h; have := thinP_length a d K F; rw [h, hF] at this; simp at this
  have hlen : Z < (sqP a d K F).length := by
    have := convL_length_ge (thinP a d K F) (thinP a d K F) hne
    rw [thinP_length, hF] at this
    exact lt_of_lt_of_le (Nat.lt_succ_self Z) this
  have ht : ((sqP a d K F).take Z).length = Z := by simp; omega
  rw [levelOut_X, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), ht]
  simp

end Poly

/-! ## Point masses of one level -/

section Masses
variable {a d D Z K : ℕ} {p : I} {F : List (List ℕ)} {μ : Measure (ℕ × ℕ)}

lemma tab_eq_zero (hF : F.length = Z + 1) (hrows : ∀ row ∈ F, row.length ≤ K + 1) {m r : ℕ}
    (h : Z + 1 ≤ m ∨ K + 1 ≤ r) : tab F m r = 0 := by
  unfold tab
  rcases h with h | h
  · have : F.getD m [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [this]; rfl
  · exact getD_eq_zero_of_le (by have := getD_row_length hrows m; omega)

lemma mass_zero (hD : 0 < D) (hμ : Bounded D F μ) {m r : ℕ} (h : tab F m r = 0) :
    μ {(m, r)} = 0 := by
  have := hμ m r
  rw [h, Nat.cast_zero, nonpos_iff_eq_zero, mul_eq_zero] at this
  rcases this with h1 | h1
  · exact h1
  · exact absurd h1 (by exact_mod_cast hD.ne')

lemma child_bound (hd : 0 < d) (hp : (p : ℝ) = a / d) (hD : 0 < D) (hF : F.length = Z + 1)
    (hrows : ∀ row ∈ F, row.length ≤ K + 1) (hμ : Bounded D F μ) (i b : ℕ) :
    (μ.bind (thinPair p)) {(i, b)} * ((D : ℝ≥0∞) * (d : ℝ≥0∞) ^ (Z + K)) ≤
      (((thinP a d K F).getD i 0).coeff b : ℝ≥0∞) := by
  rw [bind_singleton, coeff_thinP a d K hF hrows]
  have hz : ∀ y ∉ (range (Z + 1)) ×ˢ (range (K + 1)), μ {y} * thinPair p y {(i, b)} = 0 := by
    rintro ⟨m, r⟩ hy
    rw [mem_product, mem_range, mem_range, not_and_or, not_lt, not_lt] at hy
    rw [mass_zero hD hμ (tab_eq_zero hF hrows hy), zero_mul]
  rw [tsum_eq_sum hz, sum_product, sum_mul]
  push_cast
  refine sum_le_sum fun m hm => ?_
  rw [sum_mul]
  refine sum_le_sum fun r hr => ?_
  have hm' : m ≤ Z := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hr' : r ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hr)
  have hpow : (d : ℝ≥0∞) ^ (Z + K) = d ^ m * d ^ (Z - m) * (d ^ r * d ^ (K - r)) := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  rw [thinPair_singleton]
  calc μ {(m, r)} * (binomial (m, r).1 p {i} * binomial (m, r).2 p {b}) * (D * d ^ (Z + K))
      = (μ {(m, r)} * D) * ((binomial m p {i} * d ^ m) * (binomial r p {b} * d ^ r) *
          (d ^ (Z - m) * d ^ (K - r))) := by rw [hpow]; ring
    _ = (μ {(m, r)} * D) * ((thinCoef a d m i : ℝ≥0∞) * (thinCoef a d r b : ℝ≥0∞) *
          (d ^ (Z - m) * d ^ (K - r))) := by
        rw [binom_scaled hd hp, binom_scaled hd hp]
    _ ≤ (tab F m r : ℝ≥0∞) * ((thinCoef a d m i : ℝ≥0∞) * (thinCoef a d r b : ℝ≥0∞) *
          (d ^ (Z - m) * d ^ (K - r))) := by gcongr; exact hμ m r
    _ = _ := by ring

lemma conv_bound (hd : 0 < d) (hp : (p : ℝ) = a / d) (hD : 0 < D) (hF : F.length = Z + 1)
    (hrows : ∀ row ∈ F, row.length ≤ K + 1) (hμ : Bounded D F μ) (u v : ℕ) :
    ((μ.bind (thinPair p)) ∗ (μ.bind (thinPair p))) {(u, v)} *
        ((D : ℝ≥0∞) * (d : ℝ≥0∞) ^ (Z + K)) ^ 2 ≤
      (((sqP a d K F).getD u 0).coeff v : ℝ≥0∞) := by
  rw [conv_singleton_pair, coeff_sqP, sum_mul]
  push_cast
  refine sum_le_sum fun ij _ => ?_
  rw [sum_mul]
  refine sum_le_sum fun kl _ => ?_
  rw [pow_two]
  calc (μ.bind (thinPair p)) {(ij.1, kl.1)} * (μ.bind (thinPair p)) {(ij.2, kl.2)} *
        ((D * d ^ (Z + K)) * (D * d ^ (Z + K)))
      = ((μ.bind (thinPair p)) {(ij.1, kl.1)} * (D * d ^ (Z + K))) *
        ((μ.bind (thinPair p)) {(ij.2, kl.2)} * (D * d ^ (Z + K))) := by ring
    _ ≤ _ := mul_le_mul' (child_bound hd hp hD hF hrows hμ _ _) (child_bound hd hp hD hF hrows hμ _ _)

lemma cap_preimage_lt {m v : ℕ} (hm : m < Z) : capPair Z ⁻¹' {(m, v)} = {(m, v)} := by
  ext ⟨u, w⟩
  simp only [Set.mem_preimage, capPair, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    have : u = m := by omega
    subst this
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨by simp; omega, by omega⟩

lemma cap_preimage_eq (v : ℕ) :
    capPair Z ⁻¹' {(Z, v)} ⊆ ↑((range (v + 1)).image fun i => (Z + i, v - i)) := by
  rintro ⟨u, w⟩ h
  simp only [Set.mem_preimage, capPair, Set.mem_singleton_iff, Prod.mk.injEq] at h
  simp only [coe_image, coe_range, Set.mem_image, Set.mem_Iio, Prod.mk.injEq]
  refine ⟨u - Z, by omega, by omega, by omega⟩

lemma cap_preimage_gt {m v : ℕ} (hm : Z < m) : capPair Z ⁻¹' {(m, v)} = ∅ := by
  ext ⟨u, w⟩
  simp only [Set.mem_preimage, capPair, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro h; omega

lemma map_bound (hd : 0 < d) (hp : (p : ℝ) = a / d) (hD : 0 < D) (hF : F.length = Z + 1)
    (hrows : ∀ row ∈ F, row.length ≤ K + 1) (hμ : Bounded D F μ) {m : ℕ} (hm : m ≤ Z) (v : ℕ) :
    (((μ.bind (thinPair p)) ∗ (μ.bind (thinPair p))).map (capPair Z)) {(m, v)} *
        ((D : ℝ≥0∞) * (d : ℝ≥0∞) ^ (Z + K)) ^ 2 ≤
      (((levelOut (X : ℕ[X]) a d Z K F).getD m 0).coeff v : ℝ≥0∞) := by
  rw [map_singleton]
  rcases lt_or_eq_of_le hm with hm | rfl
  · rw [cap_preimage_lt hm, levelOut_X_getD_lt a d K hF hm]
    exact conv_bound hd hp hD hF hrows hμ m v
  · rw [levelOut_X_getD_Z a d K hF, coeff_evalL_X]
    have hinj : Set.InjOn (fun i => (m + i, v - i)) ↑(range (v + 1)) := by
      intro i hi j hj h
      simp only [Prod.mk.injEq] at h
      omega
    calc _ ≤ ((μ.bind (thinPair p)) ∗ (μ.bind (thinPair p)))
            ↑((range (v + 1)).image fun i => (m + i, v - i)) * ((D : ℝ≥0∞) * d ^ (m + K)) ^ 2 := by
          gcongr; exact cap_preimage_eq v
      _ = ∑ i ∈ range (v + 1), ((μ.bind (thinPair p)) ∗ (μ.bind (thinPair p))) {(m + i, v - i)} *
            ((D : ℝ≥0∞) * d ^ (m + K)) ^ 2 := by
          rw [measure_finset, sum_image hinj, sum_mul]
      _ ≤ ∑ i ∈ range (v + 1), ((((sqP a d K F).drop m).getD i 0).coeff (v - i) : ℝ≥0∞) := by
          refine sum_le_sum fun i _ => ?_
          rw [getD_drop']
          exact conv_bound hd hp hD hF hrows hμ (m + i) (v - i)
      _ = _ := by push_cast; rfl

end Masses

/-! ## Soundness -/

/-- **Soundness of one level check**, for every thinning probability `α/d`,
cap `Z`, cutoff `K`, scale `D` and digit width `w`. -/
theorem level_sound {w a d D Z K : ℕ} {p : I} (hd : 0 < d) (hp : (p : ℝ) = a / d) (hD : 0 < D)
    {F F' : List (List ℕ)} (hc : checkLevel w a d D Z K F F' = true) {μ : Measure (ℕ × ℕ)}
    (hμ : Bounded D F μ) :
    Bounded D F' ((((μ.bind (thinPair p)) ∗ (μ.bind (thinPair p))).map (capPair Z)).restrict
      (lowTotal K)) := by
  unfold checkLevel at hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at hc
  obtain ⟨⟨⟨hF, hrows⟩, hbound⟩, hrow⟩ := hc
  intro m v
  rw [restrict_singleton]
  by_cases hx : (m, v) ∈ lowTotal K
  swap
  · rw [Set.indicator_of_notMem hx, zero_mul]; exact zero_le
  rw [Set.indicator_of_mem hx]
  have hmv : m + v ≤ K := hx
  by_cases hmZ : Z < m
  · rw [map_singleton, cap_preimage_gt hmZ, measure_empty, zero_mul]; exact zero_le
  push Not at hmZ
  have hO := map_bound hd hp hD hF hrows hμ hmZ v
  -- the coefficient is a digit of the checker's packed integer
  have hev : ∀ (x : ℕ), levelOut x a d Z K F =
      (levelOut (X : ℕ[X]) a d Z K F).map (Polynomial.evalRingHom x) := by
    intro x; rw [levelOut_map]; simp
  have h1 : ((levelOut (X : ℕ[X]) a d Z K F).getD m 0).eval 1 < 2 ^ w := by
    have := lt_of_all_lt (Nat.two_pow_pos w) hbound m
    rw [hev 1, getD_map_zero] at this
    simpa using this
  have hdig : ((levelOut (X : ℕ[X]) a d Z K F).getD m 0).coeff v =
      (digitsL w (K + 1 - m) ((levelOut (2 ^ w) a d Z K F).getD m 0)).getD v 0 := by
    rw [hev (2 ^ w), getD_map_zero, coe_evalRingHom, digit_of_eval_one h1 _ _ (by omega)]
  have hle := rowLe_spec _ _ _ (hrow m (by omega)) v (by rw [digitsL_length]; omega)
  rw [← hdig] at hle
  -- combine
  set c' : ℕ := D * d ^ (2 * (K + Z))
  have hc' : (c' : ℝ≥0∞) ≠ 0 := by
    have : 0 < c' := Nat.mul_pos hD (Nat.pow_pos hd)
    exact_mod_cast this.ne'
  have hsq : ((D : ℝ≥0∞) * (d : ℝ≥0∞) ^ (Z + K)) ^ 2 = (D : ℝ≥0∞) * c' := by
    simp only [c']; push_cast; rw [mul_pow, ← pow_mul]; ring_nf
  have hle' : (((levelOut (X : ℕ[X]) a d Z K F).getD m 0).coeff v : ℝ≥0∞) ≤ (tab F' m v : ℝ≥0∞) * c' := by
    exact_mod_cast hle
  rw [hsq] at hO
  have := hO.trans hle'
  rw [← mul_assoc] at this
  exact (ENNReal.mul_le_mul_iff_left hc' (ENNReal.natCast_ne_top _)).mp this

/-- **Soundness of the base check**: the depth-one law is bounded by `F`. -/
theorem base_sound {D N r a b Z K : ℕ} {lam : ℝ≥0} (hlam : (lam : ℝ) = a / b) (hD : 0 < D)
    {F : List (List ℕ)} (hc : checkInit D N r a b Z K F = true) :
    Bounded D F (((poissonMeasure lam).map (fun n => capPair Z (n, 0))).restrict (lowTotal K)) := by
  unfold checkInit at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨hL, hb⟩, hr⟩, hc⟩ := hc
  intro m v
  rw [restrict_singleton]
  by_cases hx : (m, v) ∈ lowTotal K
  swap
  · rw [Set.indicator_of_notMem hx, zero_mul]; exact zero_le
  rw [Set.indicator_of_mem hx, map_singleton]
  have hmv : m + v ≤ K := hx
  have hsub : (fun n => capPair Z (n, 0)) ⁻¹' {(m, v)} ⊆ {m + v} := by
    intro n hn
    simp only [Set.mem_preimage, capPair, Set.mem_singleton_iff, Prod.mk.injEq] at hn ⊢
    omega
  by_cases hf : capPair Z (m + v, 0) = (m, v)
  · have htab : tab F m v = (F.getD (min (m + v) Z) []).getD (m + v - Z) 0 := by
      simp only [capPair, Prod.mk.injEq] at hf
      obtain ⟨h1, h2⟩ := hf
      rw [tab, h1]
      congr 1; omega
    calc poissonMeasure lam ((fun n => capPair Z (n, 0)) ⁻¹' {(m, v)}) * D
        ≤ poissonMeasure lam {m + v} * D := by gcongr
      _ ≤ (NTop.pT D a b (NTop.eNum D N r a b) (m + v) : ℝ≥0∞) := pois_scaled hlam hD hb hr hL _
      _ ≤ (tab F m v : ℝ≥0∞) := by rw [htab]; exact_mod_cast hc (m + v) (by omega)
  · have : (fun n => capPair Z (n, 0)) ⁻¹' {(m, v)} = ∅ := by
      ext n
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hn
      have := hsub (show n ∈ (fun n => capPair Z (n, 0)) ⁻¹' {(m, v)} from hn)
      rw [Set.mem_singleton_iff] at this
      subst this
      exact hf hn
    rw [this, measure_empty, zero_mul]; exact zero_le

end RebuildBound.NCA1
