import RebuildBound.Spec.Prob.Series
import RebuildBound.Proofs.P7alg
import RebuildBound.Proofs.NTop.Checker
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Soundness of the NTop checker

`phi_sound`: `Phi K n C (a/b) S ≤ phiNum … / D`. Each rounded quantity is at
least (or, for the lower chain, at most) the real one and every step is
monotone in nonnegative inputs.
-/

open scoped BigOperators
open Finset RebuildBound.Spec

namespace RebuildBound.NTop

lemma cdiv_ge (x y : ℕ) (hy : 0 < y) : (x : ℝ) / y ≤ (cdiv x y : ℝ) := by
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  have h1 := Nat.div_add_mod (x + (y' + 1 - 1)) (y' + 1)
  have h2 := Nat.mod_lt (x + (y' + 1 - 1)) (show 0 < y' + 1 by omega)
  have h3 : x ≤ (y' + 1) * cdiv x (y' + 1) := by
    unfold cdiv; simp only [Nat.add_sub_cancel] at *
    generalize (y' + 1) * ((x + y') / (y' + 1)) = t at *
    omega
  rw [div_le_iff₀ (by positivity)]
  have : (x : ℝ) ≤ ((y' + 1) * cdiv x (y' + 1) : ℕ) := by exact_mod_cast h3
  push_cast at this ⊢
  linarith

lemma sum_div' {ι : Type*} (s : Finset ι) (f : ι → ℝ) (d : ℝ) :
    (∑ i ∈ s, f i) / d = ∑ i ∈ s, f i / d := by
  simp [div_eq_mul_inv, Finset.sum_mul]

lemma ssum_cast (f : ℕ → ℕ) (N : ℕ) : (ssum f N : ℝ) = ∑ i ∈ range N, (f i : ℝ) := by
  induction N with
  | zero => simp [ssum]
  | succ n ih => simp [ssum, sum_range_succ, ih]

section
variable {D : ℕ} (hD : 0 < D)
include hD

lemma mulUp_le {x y : ℝ} {X Y : ℕ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hX : x ≤ X / D) (hY : y ≤ Y / D) :
    x * y ≤ (cdiv (X * Y) D : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h := cdiv_ge (X * Y) D hD
  have : x * y ≤ (X / D) * (Y / D) := mul_le_mul hX hY hy (by positivity)
  refine this.trans ?_
  rw [le_div_iff₀ hD']
  have h' : ((X : ℝ) * Y) / D ≤ cdiv (X * Y) D := by exact_mod_cast h
  calc (X / D) * (Y / D) * D = (X * Y : ℝ) / D := by field_simp
    _ ≤ _ := by push_cast at h'; exact h'

lemma mulLo_le {x y : ℝ} {X Y : ℕ} (hx : 0 ≤ (X : ℝ) / D) (hy : 0 ≤ (Y : ℝ) / D)
    (hX : (X : ℝ) / D ≤ x) (hY : (Y : ℝ) / D ≤ y) :
    ((X * Y / D : ℕ) : ℝ) / D ≤ x * y := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : ((X * Y / D : ℕ) : ℝ) ≤ (X * Y : ℕ) / (D : ℝ) := Nat.cast_div_le
  have : (X / D) * (Y / D) ≤ x * y := mul_le_mul hX hY hy (hx.trans hX)
  calc ((X * Y / D : ℕ) : ℝ) / D ≤ ((X * Y : ℕ) / (D : ℝ)) / D := by gcongr
    _ = (X / D) * (Y / D) := by push_cast; field_simp
    _ ≤ _ := this

lemma powUp_le {x : ℝ} {X : ℕ} (hx : 0 ≤ x) (hX : x ≤ X / D) (m : ℕ) :
    x ^ m ≤ (powUp D X m : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  induction m with
  | zero => simp [powUp, hD'.ne']
  | succ m ih =>
    rw [pow_succ]; unfold powUp
    exact mulUp_le hD (by positivity) hx ih hX

lemma powLo_le {x : ℝ} {X : ℕ} (hx : 0 ≤ (X : ℝ) / D) (hX : (X : ℝ) / D ≤ x) (m : ℕ) :
    (powLo D X m : ℝ) / D ≤ x ^ m ∧ 0 ≤ (powLo D X m : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  induction m with
  | zero => simp [powLo, hD'.ne']
  | succ m ih =>
    rw [pow_succ]; unfold powLo
    exact ⟨mulLo_le hD ih.2 hx ih.1 hX, by positivity⟩

end


section exp
variable {D : ℕ} (hD : 0 < D) {a b r : ℕ} (hb : 0 < b) (hr : 0 < r)
include hD hb hr

lemma upT_ge (i : ℕ) :
    ((a : ℝ) / (b * r)) ^ i / (i.factorial : ℝ) ≤ (upT D a b r i : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  induction i with
  | zero => simp [upT, hD'.ne']
  | succ i ih =>
    have hq : 0 < b * r * (i + 1) := by positivity
    have h := cdiv_ge (upT D a b r i * a) (b * r * (i + 1)) hq
    unfold upT
    have hx : 0 ≤ (a : ℝ) / (b * r) := by positivity
    have e1 : ((a : ℝ) / (b * r)) ^ (i + 1) / ((i + 1).factorial : ℝ)
        = (((a : ℝ) / (b * r)) ^ i / (i.factorial : ℝ)) * ((a : ℝ) / (b * r)) / (i + 1) := by
      rw [Nat.factorial_succ, pow_succ]; push_cast; field_simp
    rw [e1]
    have h2 : (((a : ℝ) / (b * r)) ^ i / (i.factorial : ℝ)) * ((a : ℝ) / (b * r)) / (i + 1)
        ≤ ((upT D a b r i : ℝ) / D) * ((a : ℝ) / (b * r)) / (i + 1) := by
      gcongr
    refine h2.trans ?_
    push_cast at h
    have e2 : ((upT D a b r i : ℝ) / D) * ((a : ℝ) / (b * r)) / (i + 1)
        = ((upT D a b r i : ℝ) * a / (b * r * (i + 1))) / D := by
      field_simp
    rw [e2]
    gcongr

lemma loT_le (i : ℕ) :
    (loT D a b r i : ℝ) / D ≤ ((a : ℝ) / (b * r)) ^ i / (i.factorial : ℝ) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  induction i with
  | zero => simp [loT, hD'.ne']
  | succ i ih =>
    have hx : 0 ≤ (a : ℝ) / (b * r) := by positivity
    have e1 : ((a : ℝ) / (b * r)) ^ (i + 1) / ((i + 1).factorial : ℝ)
        = (((a : ℝ) / (b * r)) ^ i / (i.factorial : ℝ)) * ((a : ℝ) / (b * r)) / (i + 1) := by
      rw [Nat.factorial_succ, pow_succ]; push_cast; field_simp
    rw [e1]
    unfold loT
    have h1 : ((loT D a b r i * a / (b * r * (i + 1)) : ℕ) : ℝ)
        ≤ ((loT D a b r i * a : ℕ) : ℝ) / ((b * r * (i + 1) : ℕ) : ℝ) := Nat.cast_div_le
    push_cast at h1
    have e2 : ((loT D a b r i : ℝ) * a / (b * r * (i + 1))) / D
        = ((loT D a b r i : ℝ) / D) * ((a : ℝ) / (b * r)) / (i + 1) := by
      field_simp
    calc _ ≤ ((loT D a b r i : ℝ) * a / (b * r * (i + 1))) / D := by gcongr
      _ = _ := e2
      _ ≤ _ := by gcongr

omit hD in
lemma exp_split : Real.exp ((a : ℝ) / b) = Real.exp ((a : ℝ) / (b * r)) ^ r := by
  rw [← Real.exp_nat_mul]; congr 1; field_simp

lemma exp_lower (N : ℕ) :
    (lmNum D N r a b : ℝ) / D ≤ Real.exp ((a : ℝ) / b) ∧ 0 ≤ (lmNum D N r a b : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hx : 0 ≤ (a : ℝ) / (b * r) := by positivity
  have hs : (ssum (loT D a b r) N : ℝ) / D ≤ Real.exp ((a : ℝ) / (b * r)) := by
    rw [ssum_cast, sum_div']
    have : ∑ i ∈ range N, (loT D a b r i : ℝ) / D
        ≤ ∑ i ∈ range N, ((a : ℝ) / (b * r)) ^ i / (i.factorial : ℝ) :=
      sum_le_sum fun i _ => loT_le hD hb hr i
    exact this.trans (Real.sum_le_exp_of_nonneg hx N)
  have := powLo_le hD (x := Real.exp ((a : ℝ) / (b * r))) (X := ssum (loT D a b r) N)
    (by positivity) hs r
  rw [exp_split hb hr]
  exact this

lemma exp_upper (har : a ≤ b * r) {N : ℕ} (hN : 0 < N) :
    Real.exp ((a : ℝ) / b) ≤ (umNum D N r a b : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hx : 0 ≤ (a : ℝ) / (b * r) := by positivity
  have hx1 : (a : ℝ) / (b * r) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast har
  have hb' := Real.exp_bound (x := (a : ℝ) / (b * r)) (by rw [abs_of_nonneg hx]; exact hx1) hN
  have h1 := (abs_le.mp hb').2
  rw [abs_of_nonneg hx] at h1
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hfN : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  have hsum : ∑ i ∈ range N, ((a : ℝ) / (b * r)) ^ i / (i.factorial : ℝ)
      ≤ (ssum (upT D a b r) N : ℝ) / D := by
    rw [ssum_cast, sum_div']
    exact sum_le_sum fun i _ => upT_ge hD hb hr i
  have hrem : ((a : ℝ) / (b * r)) ^ N * ((N.succ : ℝ) / ((N.factorial : ℝ) * N))
      ≤ (cdiv (upT D a b r N * (N + 1)) N : ℝ) / D := by
    have h := cdiv_ge (upT D a b r N * (N + 1)) N hN
    push_cast at h
    have e : ((a : ℝ) / (b * r)) ^ N * ((N.succ : ℝ) / ((N.factorial : ℝ) * N))
        = (((a : ℝ) / (b * r)) ^ N / (N.factorial : ℝ)) * (((N : ℝ) + 1) / N) := by
      push_cast; field_simp
    rw [e]
    have := upT_ge hD hb hr (a := a) N
    calc _ ≤ ((upT D a b r N : ℝ) / D) * (((N : ℝ) + 1) / N) := by gcongr
      _ = ((upT D a b r N : ℝ) * ((N : ℝ) + 1) / N) / D := by field_simp
      _ ≤ _ := by gcongr
  have hle : Real.exp ((a : ℝ) / (b * r)) ≤ (usNum D N r a b : ℝ) / D := by
    have h2 : Real.exp ((a : ℝ) / (b * r)) ≤
        ∑ i ∈ range N, ((a : ℝ) / (b * r)) ^ i / (i.factorial : ℝ) +
          ((a : ℝ) / (b * r)) ^ N * ((N.succ : ℝ) / ((N.factorial : ℝ) * N)) := by
      linarith
    unfold usNum; push_cast
    rw [add_div]
    linarith
  have := powUp_le hD (Real.exp_pos _).le hle r
  rw [exp_split hb hr]
  exact this

lemma eNum_ge (N : ℕ) (hL : 0 < lmNum D N r a b) :
    Real.exp (-((a : ℝ) / b)) ≤ (eNum D N r a b : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  obtain ⟨h1, h2⟩ := exp_lower hD hb hr (a := a) N
  have hL' : (0 : ℝ) < (lmNum D N r a b : ℝ) := by exact_mod_cast hL
  have h3 := cdiv_ge (D * D) (lmNum D N r a b) hL
  unfold eNum
  rw [Real.exp_neg]
  push_cast at h3
  have hpos : 0 < Real.exp ((a : ℝ) / b) := Real.exp_pos _
  have hpos' : 0 < (lmNum D N r a b : ℝ) / D := by positivity
  have h5 : (Real.exp ((a : ℝ) / b))⁻¹ ≤ ((lmNum D N r a b : ℝ) / D)⁻¹ := inv_anti₀ hpos' h1
  have h6 : ((lmNum D N r a b : ℝ) / D)⁻¹ = ((D : ℝ) * D / lmNum D N r a b) / D := by
    field_simp
  rw [h6] at h5
  calc _ ≤ _ := h5
    _ ≤ _ := by gcongr

lemma pT_ge {E : ℕ} (hE : Real.exp (-((a : ℝ) / b)) ≤ (E : ℝ) / D) (m : ℕ) :
    Real.exp (-((a : ℝ) / b)) * ((a : ℝ) / b) ^ m / (m.factorial : ℝ) ≤ (pT D a b E m : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  induction m with
  | zero => simpa [pT] using hE
  | succ m ih =>
    have hq : 0 < b * (m + 1) := by positivity
    have h := cdiv_ge (pT D a b E m * a) (b * (m + 1)) hq
    push_cast at h
    unfold pT
    have e1 : Real.exp (-((a : ℝ) / b)) * ((a : ℝ) / b) ^ (m + 1) / ((m + 1).factorial : ℝ)
        = (Real.exp (-((a : ℝ) / b)) * ((a : ℝ) / b) ^ m / (m.factorial : ℝ)) * ((a : ℝ) / b) / (m + 1) := by
      rw [Nat.factorial_succ, pow_succ]; push_cast; field_simp
    rw [e1]
    have hl : 0 ≤ (a : ℝ) / b := by positivity
    have e2 : ((pT D a b E m : ℝ) / D) * ((a : ℝ) / b) / (m + 1)
        = ((pT D a b E m : ℝ) * a / (b * (m + 1))) / D := by
      field_simp
    calc _ ≤ ((pT D a b E m : ℝ) / D) * ((a : ℝ) / b) / (m + 1) := by gcongr
      _ = _ := e2
      _ ≤ _ := by push_cast; gcongr

end exp


lemma seriesW_nonneg (C : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) (j : ℕ) : 0 ≤ seriesW C lam j := by
  unfold seriesW; positivity

lemma seriesCoeff_succ (n C : ℕ) (lam : ℝ) (k : ℕ) :
    seriesCoeff n C lam (k + 1) = (n : ℝ) / ((k + 1 : ℕ) : ℝ) *
      ∑ i ∈ Finset.range (k + 1),
        ((i + 1 : ℕ) : ℝ) * seriesW C lam (i + 1) * seriesCoeff n C lam (k - i) := by
  rw [seriesCoeff]

lemma dot_ge {D : ℕ} (hD : 0 < D) (f g : ℕ → ℝ) :
    ∀ (m : ℕ) (xs ys : List ℕ), m ≤ xs.length → m ≤ ys.length →
      (∀ i < m, 0 ≤ f i ∧ f i ≤ (xs.getD i 0 : ℝ) / D) →
      (∀ i < m, 0 ≤ g i ∧ g i ≤ (ys.getD i 0 : ℝ) / D) →
      ∑ i ∈ range m, f i * g i ≤ (dot xs ys : ℝ) / D ^ 2 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  intro m
  induction m generalizing f g with
  | zero => intro xs ys _ _ _ _; simp; positivity
  | succ m ih =>
    intro xs ys hx hy hf hg
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases ys with
      | nil => simp at hy
      | cons y ys =>
        rw [sum_range_succ']
        have h0 := hf 0 (by omega)
        have h0' := hg 0 (by omega)
        have ih' := ih (fun i => f (i + 1)) (fun i => g (i + 1)) xs ys
          (by simpa using hx) (by simpa using hy)
          (fun i hi => by simpa using hf (i + 1) (by omega))
          (fun i hi => by simpa using hg (i + 1) (by omega))
        simp only [List.getD_cons_zero] at h0 h0'
        have h1 : f 0 * g 0 ≤ (x : ℝ) / D * (y / D) :=
          mul_le_mul h0.2 h0'.2 h0'.1 (by positivity)
        have e : (dot (x :: xs) (y :: ys) : ℝ) / D ^ 2
            = (x : ℝ) / D * (y / D) + (dot xs ys : ℝ) / D ^ 2 := by
          simp [dot]; field_simp
        rw [e]
        linarith

section series
variable {D : ℕ} (hD : 0 < D) (n C S : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) (jw : List Nat)
  (hjw : ∀ i, i < jw.length → ((i + 1 : ℕ) : ℝ) * seriesW C lam (i + 1) ≤ (jw.getD i 0 : ℝ) / D)
include hD hlam hjw

/-- Invariant of the iteration after `t` steps. -/
def Inv (D n C S : ℕ) (lam : ℝ) (t : ℕ) (st : List ℕ × ℕ) : Prop :=
  st.1.length = t + 1 ∧
  (∀ i < t + 1, seriesCoeff n C lam (t - i) ≤ (st.1.getD i 0 : ℝ) / D) ∧
  ∑ k ∈ Icc (S + 1) t, ((k - S : ℕ) : ℝ) * seriesCoeff n C lam k ≤ (st.2 : ℝ) / D

lemma step_inv (t : ℕ) (st : List ℕ × ℕ) (ht : t + 1 ≤ jw.length)
    (h : Inv D n C S lam t st) : Inv D n C S lam (t + 1) (step D n S jw st) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  obtain ⟨cs, acc⟩ := st
  obtain ⟨hlen, hc, hacc⟩ := h
  simp only at hlen hc hacc
  -- the new coefficient
  have hnew : seriesCoeff n C lam (t + 1) ≤
      (cdiv (n * dot jw cs) (cs.length * D) : ℝ) / D := by
    rw [seriesCoeff_succ]
    have hsum := dot_ge hD (fun i => ((i + 1 : ℕ) : ℝ) * seriesW C lam (i + 1))
      (fun i => seriesCoeff n C lam (t - i)) (t + 1) jw cs (by omega) (by omega)
      (fun i hi => ⟨by have := seriesW_nonneg C hlam (i + 1); positivity,
        hjw i (by omega)⟩)
      (fun i hi => ⟨seriesCoeff_nonneg n C hlam _, hc i hi⟩)
    have hk : 0 < cs.length * D := by rw [hlen]; positivity
    have hcd := cdiv_ge (n * dot jw cs) (cs.length * D) hk
    push_cast at hcd
    rw [hlen] at hcd ⊢
    push_cast at hcd ⊢
    have hn : (0 : ℝ) ≤ (n : ℝ) / ((t : ℝ) + 1) := by positivity
    push_cast at hsum
    calc _ ≤ (n : ℝ) / ((t : ℝ) + 1) * ((dot jw cs : ℝ) / D ^ 2) := mul_le_mul_of_nonneg_left hsum hn
      _ = ((n : ℝ) * dot jw cs / (((t : ℝ) + 1) * D)) / D := by field_simp
      _ ≤ _ := by gcongr
  refine ⟨by simp [step, hlen], ?_, ?_⟩
  · intro i hi
    simp only [step]
    cases i with
    | zero => simpa using hnew
    | succ i =>
      have := hc i (by omega)
      have e : t + 1 - (i + 1) = t - i := by omega
      simpa [e] using this
  · simp only [step, hlen]
    have hcn : (0 : ℝ) ≤ seriesCoeff n C lam (t + 1) := seriesCoeff_nonneg n C hlam _
    by_cases hS : S < t + 1
    · rw [if_pos hS, Finset.sum_Icc_succ_top (by omega)]
      push_cast
      have e : (((t + 1 - S : ℕ) : ℝ)) * seriesCoeff n C lam (t + 1)
          ≤ ((t + 1 - S : ℕ) : ℝ) * ((cdiv (n * dot jw cs) ((t + 1) * D) : ℕ) : ℝ) / D := by
        rw [mul_div_assoc]; gcongr
        have := hnew; rw [hlen] at this; exact this
      have e2 : (((acc + (t + 1 - S) * cdiv (n * dot jw cs) ((t + 1) * D) : ℕ)) : ℝ) / D
          = (acc : ℝ) / D + ((t + 1 - S : ℕ) : ℝ) * ((cdiv (n * dot jw cs) ((t + 1) * D) : ℕ) : ℝ) / D := by
        push_cast; ring
      rw [add_div]
      linarith
    · rw [if_neg hS, Finset.Icc_eq_empty (by omega)]
      simp only [Finset.sum_empty, add_zero]
      positivity


omit hD hlam hjw in
lemma iter_step (D n S : ℕ) (jw : List ℕ) (t : ℕ) :
    ∀ s, iter D n S jw t (step D n S jw s) = step D n S jw (iter D n S jw t s) := by
  induction t with
  | zero => intro s; rfl
  | succ t ih => intro s; simp only [iter]; rw [ih (step D n S jw s)]

lemma iter_inv (K : ℕ) (hK : K ≤ jw.length) :
    ∀ t ≤ K, Inv D n C S lam t (iter D n S jw t ([D], 0)) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨by simp [iter], ?_, ?_⟩
    · intro i hi
      have : i = 0 := by omega
      subst this; simp [iter, seriesCoeff, hD'.ne']
    · rw [Finset.Icc_eq_empty (by omega)]; simp [iter]
  | succ t ih =>
    intro ht
    simp only [iter]
    rw [iter_step]
    exact step_inv hD n C S hlam jw hjw t _ (by omega) (ih (by omega))

end series

lemma tail_le {D : ℕ} (hD : 0 < D) (N r K n C S a b : ℕ) (hb : 0 < b) (hr : 0 < r)
    (har : a ≤ b * r) (hN : 0 < N) :
    ((K + 1 - S : ℕ) : ℝ) / 2 ^ (K + 1) * Real.exp ((n : ℝ) / 2 ^ C * Real.exp ((a : ℝ) / b))
      ≤ (tailNum D N r K n C S a b : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hU := exp_upper hD hb hr har hN
  unfold tailNum
  simp only
  set um := umNum D N r a b
  have h2C : (0 : ℝ) < 2 ^ C := by positivity
  have hY : (n : ℝ) / 2 ^ C * Real.exp ((a : ℝ) / b) ≤ (cdiv (n * um) (2 ^ C) : ℝ) / D := by
    have h := cdiv_ge (n * um) (2 ^ C) (by positivity)
    push_cast at h
    calc (n : ℝ) / 2 ^ C * Real.exp ((a : ℝ) / b) ≤ (n : ℝ) / 2 ^ C * ((um : ℝ) / D) := by gcongr
      _ = ((n : ℝ) * um / 2 ^ C) / D := by field_simp
      _ ≤ _ := by gcongr
  set Y := cdiv (n * um) (2 ^ C)
  have hm : (Y : ℝ) / D ≤ (cdiv Y D : ℝ) := cdiv_ge Y D hD
  have hexp : Real.exp ((n : ℝ) / 2 ^ C * Real.exp ((a : ℝ) / b)) ≤ 3 ^ (cdiv Y D) := by
    calc _ ≤ Real.exp (cdiv Y D : ℕ) := Real.exp_le_exp.mpr (hY.trans hm)
      _ = Real.exp 1 ^ (cdiv Y D) := by
        rw [← Real.exp_nat_mul]; simp
      _ ≤ 3 ^ (cdiv Y D) := by
        gcongr
        have := Real.exp_one_lt_d9
        linarith [show (2.7182818286 : ℝ) ≤ 3 by norm_num]
  have h2K : (0 : ℝ) < 2 ^ (K + 1) := by positivity
  have h := cdiv_ge ((K + 1 - S) * 3 ^ (cdiv Y D) * D) (2 ^ (K + 1)) (by positivity)
  push_cast at h
  calc _ ≤ ((K + 1 - S : ℕ) : ℝ) / 2 ^ (K + 1) * 3 ^ (cdiv Y D) := by gcongr
    _ = (((K + 1 - S : ℕ) : ℝ) * 3 ^ (cdiv Y D) * D / 2 ^ (K + 1)) / D := by field_simp
    _ ≤ _ := by push_cast; gcongr

/-- **Soundness.** -/
theorem phi_sound {D : ℕ} (hD : 0 < D) (N r K n C S a b : ℕ) (hb : 0 < b) (hr : 0 < r)
    (har : a ≤ b * r) (hN : 0 < N) (hL : 0 < lmNum D N r a b) :
    Phi K n C ((a : ℝ) / b) S ≤ (phiNum D N r K n C S a b : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hlam : 0 ≤ (a : ℝ) / b := by positivity
  have hE := eNum_ge hD hb hr N hL
  have hjw : ∀ i, i < (jwList D N r K C a b).length →
      ((i + 1 : ℕ) : ℝ) * seriesW C ((a : ℝ) / b) (i + 1)
        ≤ ((jwList D N r K C a b).getD i 0 : ℝ) / D := by
    intro i hi
    have hiK : i < K := by simpa [jwList] using hi
    have hget : (jwList D N r K C a b).getD i 0
        = (i + 1) * pT D a b (eNum D N r a b) (C + i + 1) := by
      simp [jwList, hiK]
    rw [hget]
    have := pT_ge hD hb hr (E := eNum D N r a b) hE (C + (i + 1))
    unfold seriesW
    push_cast
    have hn : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
    calc _ ≤ ((i : ℝ) + 1) * ((pT D a b (eNum D N r a b) (C + (i + 1)) : ℝ) / D) := by
          gcongr
      _ = _ := by ring_nf
  have hlen : K ≤ (jwList D N r K C a b).length := by simp [jwList]
  have hinv := iter_inv hD n C S hlam _ hjw K hlen K le_rfl
  have hfin := hinv.2.2
  unfold Phi phiNum
  push_cast
  rw [add_div]
  have ht := tail_le hD N r K n C S a b hb hr har hN
  have : (finNum D N r K n C S a b : ℝ) = ((iter D n S (jwList D N r K C a b) K ([D], 0)).2 : ℝ) := rfl
  rw [this]
  linarith

end RebuildBound.NTop
