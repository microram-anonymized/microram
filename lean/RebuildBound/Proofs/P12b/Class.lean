import RebuildBound.Spec.P12
import RebuildBound.Proofs.ShadowNet.Fiber

/-!
# P12b, the class average

`classAvg q` is the product law on `K → Fin r`, key `x` of class `u` with
probability `q u`. Two facts:

* **Thinning** (`classAvg_cnt_filter`): averaging a function of the count vector
  of the keys of class `a` is binomial thinning of every node with survival
  probability `q a`; the weighted analogue of P11a's `avgB_cnt_filter`, by the
  same induction over the key set.
* **The early count** (`classAvg_early`): if, given the classes, the early count
  is `Bin(#{x ∈ E : c x = a}, p)`, and the rest does not read the classes of
  `E`, then the early count is `Bin(|E|, q_a p)`: induction over `E`, using
  Pascal's rule on both sides.

Both rest on resampling one coordinate (`classAvg_resample`), which needs
`∑ q = 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P12bProof

open RebuildBound.Spec RebuildBound.X1Proof RebuildBound.P11aProof

section Class

variable {K : Type} [Fintype K] [DecidableEq K] {r : ℕ}

/-- The weight of a class assignment. -/
noncomputable def wt (q : Fin r → I) (c : K → Fin r) : ℝ≥0∞ :=
  ∏ x, ENNReal.ofReal (q (c x))

lemma classAvg_eq (q : Fin r → I) (F : (K → Fin r) → ℝ≥0∞) :
    classAvg q F = ∑ c, wt q c * F c := rfl

lemma sum_ofReal_q (q : Fin r → I) (hq : ∑ a, (q a : ℝ) = 1) :
    ∑ u, ENNReal.ofReal (q u) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => (q u).2.1), hq, ENNReal.ofReal_one]

lemma sum_erase_ofReal_q (q : Fin r → I) (hq : ∑ a, (q a : ℝ) = 1) (a : Fin r) :
    ∑ u ∈ Finset.univ.erase a, ENNReal.ofReal (q u) = qe (q a) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => (q u).2.1), qe]
  congr 1
  have := Finset.add_sum_erase Finset.univ (fun u => (q u : ℝ)) (Finset.mem_univ a)
  linarith

lemma wt_update (q : Fin r → I) (c : K → Fin r) (x0 : K) (u : Fin r) :
    wt q (Function.update c x0 u) * ENNReal.ofReal (q (c x0)) =
      wt q c * ENNReal.ofReal (q u) := by
  unfold wt
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x0),
    ← Finset.mul_prod_erase Finset.univ (fun x => ENNReal.ofReal (q (c x))) (Finset.mem_univ x0),
    Function.update_self]
  have : ∏ x ∈ Finset.univ.erase x0, ENNReal.ofReal (q (Function.update c x0 u x)) =
      ∏ x ∈ Finset.univ.erase x0, ENNReal.ofReal (q (c x)) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this]
  ring

/-- Resampling the class of one key preserves the class average. -/
lemma classAvg_resample (q : Fin r → I) (hq : ∑ a, (q a : ℝ) = 1) (x0 : K)
    (G : (K → Fin r) → ℝ≥0∞) :
    classAvg q G = classAvg q (fun c => ∑ u, ENNReal.ofReal (q u) * G (Function.update c x0 u)) := by
  have hinv : Function.Involutive
      (fun cu : (K → Fin r) × Fin r => (Function.update cu.1 x0 cu.2, cu.1 x0)) := by
    rintro ⟨c, u⟩
    simp
  have hsum := Equiv.sum_comp (hinv.toPerm _)
    (fun cu : (K → Fin r) × Fin r => wt q cu.1 * ENNReal.ofReal (q cu.2) * G cu.1)
  simp only [Function.Involutive.coe_toPerm] at hsum
  rw [classAvg_eq, classAvg_eq]
  symm
  calc ∑ c, wt q c * ∑ u, ENNReal.ofReal (q u) * G (Function.update c x0 u)
      = ∑ cu : (K → Fin r) × Fin r,
          wt q cu.1 * ENNReal.ofReal (q cu.2) * G (Function.update cu.1 x0 cu.2) := by
        rw [Fintype.sum_prod_type' (fun c u =>
          wt q c * ENNReal.ofReal (q u) * G (Function.update c x0 u))]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        ring
    _ = ∑ cu : (K → Fin r) × Fin r,
          wt q (Function.update cu.1 x0 cu.2) * ENNReal.ofReal (q (cu.1 x0)) *
            G (Function.update cu.1 x0 cu.2) := by
        refine Finset.sum_congr rfl fun cu _ => ?_
        rw [wt_update]
    _ = ∑ cu : (K → Fin r) × Fin r, wt q cu.1 * ENNReal.ofReal (q cu.2) * G cu.1 := hsum
    _ = ∑ c, wt q c * G c := by
        rw [Fintype.sum_prod_type' (fun c u => wt q c * ENNReal.ofReal (q u) * G c)]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum, sum_ofReal_q q hq, mul_one]

lemma classAvg_add (q : Fin r → I) (F1 F2 : (K → Fin r) → ℝ≥0∞) :
    classAvg q (fun c => F1 c + F2 c) = classAvg q F1 + classAvg q F2 := by
  simp only [classAvg_eq, mul_add, Finset.sum_add_distrib]

lemma classAvg_const_mul (q : Fin r → I) (k : ℝ≥0∞) (F : (K → Fin r) → ℝ≥0∞) :
    classAvg q (fun c => k * F c) = k * classAvg q F := by
  simp only [classAvg_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma classAvg_mono (q : Fin r → I) {F G : (K → Fin r) → ℝ≥0∞} (h : ∀ c, F c ≤ G c) :
    classAvg q F ≤ classAvg q G := by
  simp only [classAvg_eq]
  gcongr with c
  exact h c

lemma classAvg_const (q : Fin r → I) (hq : ∑ a, (q a : ℝ) = 1) (k : ℝ≥0∞) :
    classAvg q (K := K) (fun _ => k) = k := by
  rw [classAvg_eq, ← Finset.sum_mul]
  have : ∑ c : K → Fin r, wt q c = 1 := by
    unfold wt
    rw [← Fintype.prod_sum (fun (_ : K) (u : Fin r) => ENNReal.ofReal (q u))]
    simp [sum_ofReal_q q hq]
  rw [this, one_mul]

/-- The class of `x0` is `a` with probability `q a`, independently of the rest. -/
lemma classAvg_split (q : Fin r → I) (hq : ∑ a, (q a : ℝ) = 1) (x0 : K) (a : Fin r)
    (F1 F2 : (K → Fin r) → ℝ≥0∞)
    (h1 : ∀ c u, F1 (Function.update c x0 u) = F1 c)
    (h2 : ∀ c u, F2 (Function.update c x0 u) = F2 c) :
    classAvg q (fun c => if c x0 = a then F1 c else F2 c) =
      pe (q a) * classAvg q F1 + qe (q a) * classAvg q F2 := by
  rw [classAvg_resample q hq x0, ← classAvg_const_mul, ← classAvg_const_mul, ← classAvg_add]
  congr 1
  funext c
  simp only [Function.update_self, h1, h2]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
  simp only [↓reduceIte]
  have : ∑ u ∈ Finset.univ.erase a, ENNReal.ofReal (q u) * (if u = a then F1 c else F2 c) =
      ∑ u ∈ Finset.univ.erase a, ENNReal.ofReal (q u) * F2 c := by
    refine Finset.sum_congr rfl fun u hu => ?_
    simp [Finset.ne_of_mem_erase hu]
  rw [this, ← Finset.sum_mul, sum_erase_ofReal_q q hq, pe]

/-- **Thinning by the class.** Averaging a function of the count vector of the
keys of class `a` is binomial thinning of every node with probability `q a`. -/
theorem classAvg_cnt_filter (q : Fin r → I) (hq : ∑ a, (q a : ℝ) = 1)
    {ι : Type*} [DecidableEq ι] (l : List ι) (hl : l.Nodup) (sl : K → ι × Slot)
    (hsl : ∀ x, (sl x).1 ∈ l) (a : Fin r) (S : Finset K) (G : States ι → ℝ≥0∞) :
    classAvg q (fun c => G (cnt (S.filter (fun x => c x = a)) sl)) =
      thinAll l (fun _ => q a) G (cnt S sl) := by
  induction S using Finset.induction_on generalizing G with
  | empty =>
    simp only [Finset.filter_empty, cnt_empty, classAvg_const q hq, thinAll_zero]
  | insert x0 S hx0 ih =>
    have hfilt : ∀ c : K → Fin r, cnt ((insert x0 S).filter (fun x => c x = a)) sl =
        if c x0 = a then cnt (S.filter (fun x => c x = a)) sl + unitVec (sl x0)
        else cnt (S.filter (fun x => c x = a)) sl := by
      intro c
      rw [Finset.filter_insert]
      split_ifs with h
      · exact cnt_insert (fun hm => hx0 (Finset.mem_of_mem_filter _ hm)) sl
      · rfl
    have hinv : ∀ (c : K → Fin r) u, (S.filter (fun x => Function.update c x0 u x = a)) =
        S.filter (fun x => c x = a) := by
      intro c u
      refine Finset.filter_congr fun x hx => ?_
      have : x ≠ x0 := fun e => hx0 (e ▸ hx)
      rw [Function.update_of_ne this]
    have : (fun c : K → Fin r => G (cnt ((insert x0 S).filter (fun x => c x = a)) sl)) =
        fun c => if c x0 = a then G (cnt (S.filter (fun x => c x = a)) sl + unitVec (sl x0))
          else G (cnt (S.filter (fun x => c x = a)) sl) := by
      funext c
      rw [hfilt]
      split_ifs <;> rfl
    rw [this, classAvg_split q hq x0 a _ _ (fun c u => by simp only [hinv])
        (fun c u => by simp only [hinv]),
      ih (fun y => G (y + unitVec (sl x0))), ih G, cnt_insert hx0,
      thinAll_add_on l hl _ G _ (hsl x0), add_comm]

lemma pe_mul (p q : I) : pe (q * p) = pe q * pe p := by
  simp only [pe, Set.Icc.coe_mul]
  exact ENNReal.ofReal_mul q.2.1

lemma qe_mul (p q : I) : qe (q * p) = pe q * qe p + qe q := by
  simp only [pe, qe, Set.Icc.coe_mul]
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hq1 : (q : ℝ) ≤ 1 := q.2.2
  rw [← ENNReal.ofReal_mul q.2.1, ← ENNReal.ofReal_add (mul_nonneg q.2.1 (by linarith))
    (by linarith)]
  congr 1
  ring

/-- **The early count.** If the rest `Ψ e` does not read the classes of `E`,
the early count `Bin(#{x ∈ E : c x = a}, p)` averages to `Bin(|E|, q_a p)`. -/
theorem classAvg_early (q : Fin r → I) (hq : ∑ a, (q a : ℝ) = 1) (a : Fin r) (p : I)
    (E : Finset K) (Ψ : ℕ → (K → Fin r) → ℝ≥0∞)
    (hΨ : ∀ e c, ∀ x ∈ E, ∀ u, Ψ e (Function.update c x u) = Ψ e c) :
    classAvg q (fun c => ∫⁻ e, Ψ e c ∂(binomial (E.filter (fun x => c x = a)).card p)) =
      classAvg q (fun c => ∫⁻ e, Ψ e c ∂(binomial E.card (q a * p))) := by
  induction E using Finset.induction_on generalizing Ψ with
  | empty =>
    simp only [Finset.filter_empty, Finset.card_empty, binomial_zero]
  | insert x0 E hx0 ih =>
    have hΨE : ∀ e c, ∀ x ∈ E, ∀ u, Ψ e (Function.update c x u) = Ψ e c :=
      fun e c x hx u => hΨ e c x (Finset.mem_insert_of_mem hx) u
    have hΨ1E : ∀ e c, ∀ x ∈ E, ∀ u, Ψ (e + 1) (Function.update c x u) = Ψ (e + 1) c :=
      fun e c x hx u => hΨE (e + 1) c x hx u
    have hinv : ∀ (c : K → Fin r) u, (E.filter (fun x => Function.update c x0 u x = a)) =
        E.filter (fun x => c x = a) := by
      intro c u
      refine Finset.filter_congr fun x hx => ?_
      have : x ≠ x0 := fun e => hx0 (e ▸ hx)
      rw [Function.update_of_ne this]
    have hfilt : ∀ c : K → Fin r,
        ∫⁻ e, Ψ e c ∂(binomial ((insert x0 E).filter (fun x => c x = a)).card p) =
          if c x0 = a then ∫⁻ e, Ψ e c ∂(binomial ((E.filter (fun x => c x = a)).card + 1) p)
          else ∫⁻ e, Ψ e c ∂(binomial (E.filter (fun x => c x = a)).card p) := by
      intro c
      rw [Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (fun hm => hx0 (Finset.mem_of_mem_filter _ hm))]
      · rfl
    have hx0' := Finset.mem_insert_self x0 E
    rw [funext hfilt, classAvg_split q hq x0 a _ _
        (fun c u => by simp only [hinv, hΨ _ c x0 hx0' u])
        (fun c u => by simp only [hinv, hΨ _ c x0 hx0' u])]
    simp only [lintegral_binomial_succ, Finset.card_insert_of_notMem hx0]
    rw [classAvg_add, classAvg_add, classAvg_const_mul, classAvg_const_mul, classAvg_const_mul,
      classAvg_const_mul, ih Ψ hΨE, ih (fun e c => Ψ (e + 1) c) hΨ1E, pe_mul, qe_mul]
    ring

end Class

end RebuildBound.P12bProof
