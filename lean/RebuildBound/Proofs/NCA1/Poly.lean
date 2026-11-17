import RebuildBound.Proofs.NCA1.Checker
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Sum

/-!
# Semantics of the NCA1 list computations

* getD formulas for `addL`, `smulL`, `convL`, `evalL`, `dotL`, `mthin`;
* `lpoly`: a list as a polynomial, and `coeff_lin_pow`, the coefficients of
  `(β + α X)^m`;
* ring-hom naturality of every generic computation (`levelOut_map`), so the
  checker's packed integers are evaluations of polynomials at `2^w`;
* digit extraction: a polynomial over `ℕ` whose low coefficients are `< B` has
  them as its base-`B` digits (`digit_eval`, `digitsL_getD`), and coefficients
  are bounded by the value at `1` (`coeff_le_eval_one`).
-/

open Polynomial Finset
open scoped BigOperators

namespace RebuildBound.NCA1

section Generic
variable {R : Type*} [CommSemiring R]

lemma addL_getD : ∀ (l₁ l₂ : List R) (i : ℕ), (addL l₁ l₂).getD i 0 = l₁.getD i 0 + l₂.getD i 0
  | [], l, i => by simp [addL]
  | a :: as, [], i => by simp [addL]
  | a :: as, b :: bs, 0 => by simp [addL]
  | a :: as, b :: bs, i + 1 => by
    rw [addL, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, addL_getD as bs i]

lemma smulL_getD (c : R) : ∀ (l : List R) (i : ℕ), (smulL c l).getD i 0 = c * l.getD i 0
  | [], i => by simp [smulL]
  | a :: as, 0 => by simp [smulL]
  | a :: as, i + 1 => by simpa [smulL] using smulL_getD c as i

lemma convL_getD : ∀ (p q : List R) (k : ℕ),
    (convL p q).getD k 0 = ∑ ij ∈ antidiagonal k, p.getD ij.1 0 * q.getD ij.2 0
  | [], q, k => by simp [convL]
  | a :: as, q, k => by
    rw [convL, addL_getD, smulL_getD]
    cases k with
    | zero => simp
    | succ k =>
      rw [List.getD_cons_succ, convL_getD as q k, Finset.Nat.sum_antidiagonal_succ]
      simp

lemma getD_eq_zero_of_le {l : List R} {i : ℕ} (h : l.length ≤ i) : l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

lemma evalL_eq_sum (x : R) : ∀ (l : List R), evalL x l = ∑ i ∈ range l.length, l.getD i 0 * x ^ i
  | [] => by simp [evalL]
  | a :: l => by
    rw [evalL, evalL_eq_sum x l, List.length_cons, sum_range_succ', sum_mul]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ, mul_assoc]
    rw [add_comm]

lemma sum_range_getD_extend (f : ℕ → R → R) (hf : ∀ i, f i 0 = 0) (l : List R) {N : ℕ}
    (hN : l.length ≤ N) : ∑ i ∈ range N, f i (l.getD i 0) = ∑ i ∈ range l.length, f i (l.getD i 0) := by
  symm
  apply sum_subset (range_subset_range.mpr hN)
  intro i _ hi
  rw [mem_range, not_lt] at hi
  rw [getD_eq_zero_of_le hi, hf]

lemma evalL_eq_sum' (x : R) (l : List R) {N : ℕ} (hN : l.length ≤ N) :
    evalL x l = ∑ i ∈ range N, l.getD i 0 * x ^ i := by
  rw [evalL_eq_sum, sum_range_getD_extend (fun i c => c * x ^ i) (fun i => zero_mul _) l hN]

lemma dotL_eq_sum : ∀ (l₁ l₂ : List R), dotL l₁ l₂ = ∑ i ∈ range l₁.length, l₁.getD i 0 * l₂.getD i 0
  | [], l₂ => by simp [dotL]
  | a :: as, [] => by simp [dotL]
  | a :: as, b :: bs => by
    rw [dotL, dotL_eq_sum as bs, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]

lemma dotL_eq_sum' (l₁ l₂ : List R) {N : ℕ} (hN : l₁.length ≤ N) :
    dotL l₁ l₂ = ∑ i ∈ range N, l₁.getD i 0 * l₂.getD i 0 := by
  rw [dotL_eq_sum, sum_range_getD_extend (fun i c => c * l₂.getD i 0) (fun i => zero_mul _) l₁ hN]

/-- A list as a polynomial. -/
noncomputable def lpoly (l : List R) : R[X] := evalL X (l.map C)

@[simp] lemma lpoly_nil : lpoly ([] : List R) = 0 := rfl

lemma lpoly_cons (a : R) (l : List R) : lpoly (a :: l) = C a + lpoly l * X := rfl

lemma coeff_lpoly : ∀ (l : List R) (k : ℕ), (lpoly l).coeff k = l.getD k 0
  | [], k => by simp
  | a :: l, 0 => by simp [lpoly_cons]
  | a :: l, k + 1 => by
    rw [lpoly_cons, coeff_add, coeff_C, coeff_mul_X, coeff_lpoly l k]
    simp

lemma lpoly_ext {l₁ l₂ : List R} (h : ∀ k, l₁.getD k 0 = l₂.getD k 0) : lpoly l₁ = lpoly l₂ := by
  ext k; rw [coeff_lpoly, coeff_lpoly, h]

lemma lpoly_addL (l₁ l₂ : List R) : lpoly (addL l₁ l₂) = lpoly l₁ + lpoly l₂ := by
  ext k; rw [coeff_add, coeff_lpoly, coeff_lpoly, coeff_lpoly, addL_getD]

lemma lpoly_smulL (c : R) (l : List R) : lpoly (smulL c l) = C c * lpoly l := by
  ext k; rw [coeff_C_mul, coeff_lpoly, coeff_lpoly, smulL_getD]

lemma lpoly_mulLin (α β : R) (c : List R) :
    lpoly (mulLin α β c) = (C β + C α * X) * lpoly c := by
  rw [mulLin, lpoly_addL, lpoly_smulL, lpoly_cons, lpoly_smulL]
  simp only [map_zero, zero_add]
  ring

lemma lpoly_mthin (α β d : R) : ∀ (rs : List R),
    lpoly (mthin α β d rs) = ∑ m ∈ range rs.length,
      C (rs.getD m 0 * d ^ (rs.length - 1 - m)) * (C β + C α * X) ^ m
  | [] => by simp [mthin]
  | r :: rest => by
    rw [mthin, lpoly_addL, lpoly_mulLin, lpoly_mthin α β d rest, List.length_cons,
      sum_range_succ', mul_sum]
    have h1 : lpoly [r * d ^ rest.length] = C (r * d ^ rest.length) := by
      simp [lpoly_cons]
    rw [h1]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, Nat.add_sub_cancel,
      Nat.sub_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun m hm => ?_
    have : rest.length - (m + 1) = rest.length - 1 - m := by omega
    rw [this, pow_succ]
    ring

/-- The coefficients of `(β + α X)^m`. -/
lemma coeff_lin_pow (α β : R) (m a : ℕ) :
    ((C β + C α * X) ^ m).coeff a = (m.choose a : R) * α ^ a * β ^ (m - a) := by
  rw [add_comm, add_pow, finsetSum_coeff]
  have hterm : ∀ k ∈ range (m + 1), ((C α * X) ^ k * C β ^ (m - k) * (m.choose k : R[X])).coeff a =
      if a = k then (m.choose a : R) * α ^ a * β ^ (m - a) else 0 := by
    intro k _
    have : (C α * X) ^ k * C β ^ (m - k) * (m.choose k : R[X]) =
        C (α ^ k * β ^ (m - k) * (m.choose k : R)) * X ^ k := by
      rw [← map_natCast (C : R →+* R[X]), mul_pow, ← C_pow, ← C_pow]
      simp only [map_mul]
      ring
    rw [this, coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · rfl
  rw [sum_congr rfl hterm, sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [mem_range, not_lt] at h
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma mthin_getD (α β d : R) (rs : List R) (a : ℕ) :
    (mthin α β d rs).getD a 0 = ∑ m ∈ range rs.length,
      rs.getD m 0 * d ^ (rs.length - 1 - m) * ((m.choose a : R) * α ^ a * β ^ (m - a)) := by
  rw [← coeff_lpoly, lpoly_mthin, finsetSum_coeff]
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_C_mul, coeff_lin_pow]

/-! ### Naturality under ring homs -/

variable {S : Type*} [CommSemiring S] (φ : R →+* S)

lemma addL_map : ∀ (l₁ l₂ : List R), (addL l₁ l₂).map φ = addL (l₁.map φ) (l₂.map φ)
  | [], l => by simp [addL]
  | a :: as, [] => by simp [addL]
  | a :: as, b :: bs => by simp [addL, addL_map as bs]

lemma smulL_map (c : R) (l : List R) : (smulL c l).map φ = smulL (φ c) (l.map φ) := by
  simp [smulL, Function.comp_def]

lemma convL_map : ∀ (p q : List R), (convL p q).map φ = convL (p.map φ) (q.map φ)
  | [], q => by simp [convL]
  | a :: as, q => by
    simp only [convL, List.map_cons, addL_map, smulL_map, convL_map as q, map_zero]

lemma evalL_map (x : R) : ∀ (l : List R), φ (evalL x l) = evalL (φ x) (l.map φ)
  | [] => by simp [evalL]
  | a :: l => by simp [evalL, evalL_map x l]

lemma dotL_map : ∀ (l₁ l₂ : List R), φ (dotL l₁ l₂) = dotL (l₁.map φ) (l₂.map φ)
  | [], l₂ => by simp [dotL]
  | a :: as, [] => by simp [dotL]
  | a :: as, b :: bs => by simp [dotL, dotL_map as bs]

lemma mulLin_map (α β : R) (c : List R) : (mulLin α β c).map φ = mulLin (φ α) (φ β) (c.map φ) := by
  simp only [mulLin, addL_map, smulL_map, List.map_cons, map_zero]

lemma mthin_map (α β d : R) : ∀ (rs : List R), (mthin α β d rs).map φ = mthin (φ α) (φ β) (φ d) (rs.map φ)
  | [] => by simp [mthin]
  | r :: rest => by
    simp only [mthin, addL_map, mulLin_map, mthin_map α β d rest, List.map_cons, List.map_nil,
      map_mul, map_pow, List.length_map]

lemma basis_map (x : R) (α d K : ℕ) : (basis x α d K).map φ = basis (φ x) α d K := by
  simp [basis, Function.comp_def]

lemma rows_map (B : List R) (F : List (List ℕ)) :
    (F.map fun row => dotL (row.map Nat.cast) B).map φ =
      F.map fun row => dotL (row.map Nat.cast) (B.map φ) := by
  rw [List.map_map]
  refine List.map_congr_left fun row _ => ?_
  simp only [Function.comp_apply, dotL_map, List.map_map]
  congr 1
  exact List.map_congr_left fun n _ => by simp

lemma levelOut_map (x : R) (α d Z K : ℕ) (F : List (List ℕ)) :
    (levelOut x α d Z K F).map φ = levelOut (φ x) α d Z K F := by
  simp only [levelOut, List.map_append, List.map_take, List.map_drop, List.map_cons, List.map_nil,
    convL_map, mthin_map, rows_map, basis_map, map_natCast, evalL_map]

lemma getD_map_zero (l : List R) (i : ℕ) : (l.map φ).getD i 0 = φ (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

end Generic

/-! ### Digits -/

lemma eval_divX (p : ℕ[X]) (B : ℕ) : p.eval B = p.coeff 0 + B * (divX p).eval B := by
  conv_lhs => rw [← divX_mul_X_add p]
  simp [eval_add, eval_mul, eval_X]
  ring

/-- A polynomial over `ℕ` whose coefficients up to `v` are `< B` has them as
its base-`B` digits. -/
lemma digit_eval (B : ℕ) : ∀ (v : ℕ) (p : ℕ[X]), (∀ i ≤ v, p.coeff i < B) →
    p.eval B / B ^ v % B = p.coeff v
  | 0, p, h => by
    rw [pow_zero, Nat.div_one, eval_divX, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 0 le_rfl)]
  | v + 1, p, h => by
    have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (h 0 (Nat.zero_le _))
    have h1 : p.eval B / B = (divX p).eval B := by
      rw [eval_divX, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (h 0 (Nat.zero_le _)), zero_add]
    rw [pow_succ', ← Nat.div_div_eq_div_mul, h1, digit_eval B v (divX p) (fun i hi => by
      rw [coeff_divX]; exact h (i + 1) (by omega)), coeff_divX]

lemma digitsL_getD (w : ℕ) : ∀ (n x v : ℕ), v < n →
    (digitsL w n x).getD v 0 = x / (2 ^ w) ^ v % 2 ^ w
  | 0, x, v, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, 0, _ => by
    simp [digitsL, Nat.and_two_pow_sub_one_eq_mod]
  | n + 1, x, v + 1, h => by
    rw [digitsL, List.getD_cons_succ, digitsL_getD w n _ v (by omega), Nat.shiftRight_eq_div_pow,
      Nat.div_div_eq_div_mul, ← pow_succ']

lemma digitsL_length (w : ℕ) : ∀ (n x : ℕ), (digitsL w n x).length = n
  | 0, x => rfl
  | n + 1, x => by simp [digitsL, digitsL_length w n]

lemma coeff_le_eval_one (p : ℕ[X]) (i : ℕ) : p.coeff i ≤ p.eval 1 := by
  rw [eval_eq_sum_range]
  by_cases hi : i ≤ p.natDegree
  · have := single_le_sum (f := fun j => p.coeff j * 1 ^ j) (fun j _ => Nat.zero_le _)
      (mem_range.mpr (Nat.lt_succ_of_le hi))
    simpa using this
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact Nat.zero_le _

/-- Digit `v` of the packed value of `p` at `2^w` is its coefficient, if
`p(1) < 2^w`. -/
lemma digit_of_eval_one {p : ℕ[X]} {w : ℕ} (h : p.eval 1 < 2 ^ w) (n v : ℕ) (hv : v < n) :
    (digitsL w n (p.eval (2 ^ w))).getD v 0 = p.coeff v := by
  rw [digitsL_getD w n _ v hv]
  exact digit_eval (2 ^ w) v p fun i _ => lt_of_le_of_lt (coeff_le_eval_one p i) h

end RebuildBound.NCA1
