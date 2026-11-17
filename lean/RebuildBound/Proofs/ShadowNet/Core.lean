import RebuildBound.Proofs.X1
import RebuildBound.Spec.P11

/-!
# P11a, the core averaging lemma

Averaging a function of the selected counts over uniform coin flips
`β : K → Bool` is binomial thinning (with survival probability `1/2`) of the
counts of all records: `avgB (G (cnt (S.filter (β · = t)) c)) = thinAll l half G (cnt S c)`.
Proved by induction over the key set `S`, one key (one unit increment) at a time.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P11aProof

open RebuildBound.Spec RebuildBound.X1Proof

/-! ### Uniform average over coin flips -/

section Avg

variable {K : Type} [Fintype K] [DecidableEq K]

/-- The uniform average over all `β : K → Bool`. -/
noncomputable def avgB (F : (K → Bool) → ℝ≥0∞) : ℝ≥0∞ :=
  (Fintype.card (K → Bool) : ℝ≥0∞)⁻¹ * ∑ β, F β

lemma card_ne_zero' : (Fintype.card (K → Bool) : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

lemma card_ne_top' : (Fintype.card (K → Bool) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _

lemma avgB_const (c : ℝ≥0∞) : avgB (K := K) (fun _ => c) = c := by
  unfold avgB
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel card_ne_zero' card_ne_top', one_mul]

/-- Flipping the coin of key `x0`. -/
def flipAt (x0 : K) (β : K → Bool) : K → Bool := Function.update β x0 (!β x0)

omit [Fintype K] in
lemma flipAt_invol (x0 : K) : Function.Involutive (flipAt x0) := by
  intro β
  funext x
  by_cases hx : x = x0
  · subst hx; simp [flipAt]
  · simp [flipAt, Function.update_of_ne hx]

lemma sum_ite_eq_half (x0 : K) (t : Bool) (F : (K → Bool) → ℝ≥0∞)
    (hF : ∀ β v, F (Function.update β x0 v) = F β) :
    ∑ β, (if β x0 = t then F β else 0) = 2⁻¹ * ∑ β, F β := by
  have hflip : ∑ β, (if β x0 = t then F β else 0) = ∑ β, (if β x0 = !t then F β else 0) := by
    rw [← Equiv.sum_comp (Function.Involutive.toPerm _ (flipAt_invol x0))]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [Function.Involutive.coe_toPerm, flipAt, Function.update_self, hF]
    cases β x0 <;> cases t <;> simp
  have htot : ∑ β, F β = ∑ β, (if β x0 = t then F β else 0) +
      ∑ β, (if β x0 = !t then F β else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    cases h : β x0 <;> cases t <;> simp
  rw [htot, ← hflip, ← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
    one_mul]

lemma avgB_split (x0 : K) (t : Bool) (F1 F2 : (K → Bool) → ℝ≥0∞)
    (h1 : ∀ β v, F1 (Function.update β x0 v) = F1 β)
    (h2 : ∀ β v, F2 (Function.update β x0 v) = F2 β) :
    avgB (fun β => if β x0 = t then F1 β else F2 β) = 2⁻¹ * avgB F1 + 2⁻¹ * avgB F2 := by
  unfold avgB
  have : ∑ β, (if β x0 = t then F1 β else F2 β) =
      ∑ β, (if β x0 = t then F1 β else 0) + ∑ β, (if β x0 = !t then F2 β else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    cases h : β x0 <;> cases t <;> simp
  rw [this, sum_ite_eq_half x0 t F1 h1, sum_ite_eq_half x0 (!t) F2 h2]
  ring

end Avg

/-! ### Count vectors -/

section Cnt

variable {K : Type} {ι : Type*} [DecidableEq ι]

/-- The count vector of the keys `S` placed at coordinates `c`. -/
def cnt (S : Finset K) (c : K → ι × Slot) : States ι := ∑ x ∈ S, unitVec (c x)

lemma cnt_apply [DecidableEq K] (S : Finset K) (c : K → ι × Slot) (q : ι × Slot) :
    cnt S c q = (S.filter (fun x => c x = q)).card := by
  unfold cnt
  rw [Finset.sum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [unitVec_apply]
  by_cases h : c x = q
  · simp [h]
  · simp [h, Ne.symm h]

@[simp] lemma cnt_empty (c : K → ι × Slot) : cnt ∅ c = 0 := by simp [cnt]

lemma cnt_insert [DecidableEq K] {x0 : K} {S : Finset K} (h : x0 ∉ S) (c : K → ι × Slot) :
    cnt (insert x0 S) c = cnt S c + unitVec (c x0) := by
  unfold cnt
  rw [Finset.sum_insert h, add_comm]

end Cnt

/-! ### Thinning a unit increment -/

section Thin

variable {ι : Type*} [DecidableEq ι]

lemma thinAll_zero (l : List ι) (p : ι → I) (G : States ι → ℝ≥0∞) :
    thinAll l p G 0 = G 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show thinAt a (p a) (thinAll l p G) 0 = G 0
    unfold thinAt
    have h0 : setNode a 0 0 (0 : States ι) = 0 := by
      funext q
      obtain ⟨v, s⟩ := q
      by_cases hv : v = a
      · subst hv; cases s <;> simp
      · rw [setNode_of_ne _ _ _ _ hv]
    simp only [Pi.zero_apply, binomial_zero, lintegral_dirac, h0, ih]

lemma thinAll_add_off (l : List ι) (p : ι → I) (G : States ι → ℝ≥0∞) (x : States ι)
    {q : ι × Slot} (hq : q.1 ∉ l) :
    thinAll l p G (x + unitVec q) = thinAll l p (fun y => G (y + unitVec q)) x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    have ha : q.1 ≠ a := fun e => hq (e ▸ List.mem_cons_self)
    have hl : q.1 ∉ l := fun e => hq (List.mem_cons_of_mem _ e)
    show thinAt a (p a) (thinAll l p G) (x + unitVec q) =
      thinAt a (p a) (thinAll l p (fun y => G (y + unitVec q))) x
    rw [thinAt_eq, thinAt_eq, Ex_add_off ha]
    unfold Ex
    simp only [ih _ hl]

lemma thinAll_add_on (l : List ι) (hl : l.Nodup) (p : ι → I) (G : States ι → ℝ≥0∞)
    (x : States ι) {q : ι × Slot} (hq : q.1 ∈ l) :
    thinAll l p G (x + unitVec q) = qe (p q.1) * thinAll l p G x +
      pe (p q.1) * thinAll l p (fun y => G (y + unitVec q)) x := by
  induction l generalizing x with
  | nil => simp at hq
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    show thinAt a (p a) (thinAll l p G) (x + unitVec q) =
      qe (p q.1) * thinAt a (p a) (thinAll l p G) x +
        pe (p q.1) * thinAt a (p a) (thinAll l p (fun y => G (y + unitVec q))) x
    by_cases ha : q.1 = a
    · have hql : q.1 ∉ l := ha ▸ hl.1
      rw [thinAt_eq, thinAt_eq, thinAt_eq, Ex_add_on ha, ha]
      congr 2
      unfold Ex
      simp only [thinAll_add_off l p G _ hql]
    · have hql : q.1 ∈ l := by
        rcases List.mem_cons.mp hq with h | h
        · exact absurd h ha
        · exact h
      rw [thinAt_eq, thinAt_eq, thinAt_eq, Ex_add_off ha]
      unfold Ex
      simp only [ih hl.2 _ hql]
      simp only [lintegral_add_nat, lintegral_const_mul_nat]

end Thin

/-! ### The core lemma -/

lemma pe_half : pe half = 2⁻¹ := by
  simp [pe, half, ENNReal.ofReal_inv_of_pos]

lemma qe_half : qe half = 2⁻¹ := by
  have : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  simp only [qe, half]
  rw [this]
  simp [ENNReal.ofReal_inv_of_pos]

theorem avgB_cnt_filter {K : Type} [Fintype K] [DecidableEq K] {ι : Type*} [DecidableEq ι]
    (l : List ι) (hl : l.Nodup) (c : K → ι × Slot) (hc : ∀ x, (c x).1 ∈ l) (t : Bool)
    (S : Finset K) (G : States ι → ℝ≥0∞) :
    avgB (fun β => G (cnt (S.filter (fun x => β x = t)) c)) =
      thinAll l (fun _ => half) G (cnt S c) := by
  induction S using Finset.induction_on generalizing G with
  | empty =>
    simp only [Finset.filter_empty, cnt_empty, avgB_const, thinAll_zero]
  | insert x0 S hx0 ih =>
    have hfilt : ∀ β : K → Bool, cnt ((insert x0 S).filter (fun x => β x = t)) c =
        if β x0 = t then cnt (S.filter (fun x => β x = t)) c + unitVec (c x0)
        else cnt (S.filter (fun x => β x = t)) c := by
      intro β
      rw [Finset.filter_insert]
      split_ifs with h
      · exact cnt_insert (fun hm => hx0 (Finset.mem_of_mem_filter _ hm)) c
      · rfl
    have hinv : ∀ (β : K → Bool) v, (S.filter (fun x => Function.update β x0 v x = t)) =
        S.filter (fun x => β x = t) := by
      intro β v
      refine Finset.filter_congr fun x hx => ?_
      have : x ≠ x0 := fun e => hx0 (e ▸ hx)
      rw [Function.update_of_ne this]
    have : (fun β : K → Bool => G (cnt ((insert x0 S).filter (fun x => β x = t)) c)) =
        fun β => if β x0 = t then G (cnt (S.filter (fun x => β x = t)) c + unitVec (c x0))
          else G (cnt (S.filter (fun x => β x = t)) c) := by
      funext β
      rw [hfilt]
      split_ifs <;> rfl
    rw [this, avgB_split x0 t _ _ (fun β v => by simp only [hinv]) (fun β v => by simp only [hinv]),
      ih (fun y => G (y + unitVec (c x0))), ih G, cnt_insert hx0,
      thinAll_add_on l hl _ G _ (hc x0), pe_half, qe_half, add_comm]

end RebuildBound.P11aProof
