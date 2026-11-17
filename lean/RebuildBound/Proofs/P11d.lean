import RebuildBound.Proofs.NetworkAverage
import RebuildBound.Proofs.P5a
import RebuildBound.Proofs.P5b
import RebuildBound.Proofs.P11c
import RebuildBound.Spec.P11de
import RebuildBound.Proofs.ShadowLaw.Unit

/-!
# P11d: Poissonization of the phantom arrivals

* **Bridge.** For a finite type `A` and `d : A → κ` with law `law d` (the push-forward of
  the uniform law on `A`), the uniform average over `Fin n → A` of `F (Σ_i e_{d (g i)})`
  is `∫ F ∂convList (replicate n (unitLaw (law d)))`: induction on `n`, splitting off the
  first coordinate with `Fin.consEquiv` and `Measure.lintegral_conv`.
* **One key.** A pair (old-home bits, word bits) is `a : Fin (k + 1) → Bool × Bool`; the
  destination at stage `lo + 1` is coordinatewise, `dd a i = phi i (a i)`, so the fiber
  of `V` is a `piFinset` with at most `2^k * 4` elements out of `4^(k+1)`: every
  coordinate below `k` fixes one of the two bits, the top coordinate is forced to `true`.
  Only this upper bound is needed (`lo < k` is not used).
* **Chain.** P5a (with P11c's class facts), P5b_split, P5b_conv (`n` times) and P5b_pad.

No obstacle: the measure-based API sufficed. `poissonMeasure 0 = dirac 0` is not in
Mathlib, so the empty key set is handled directly by monotonicity.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RebuildBound.P11dProof

open RebuildBound.Spec

section OneKey

/-- Coordinate `i` of a key's destination at stage `lo + 1`, from the pair
(old-home bit, word bit) `q`: the word below `lo + 1`, then the old home, with the
top bit forced to `true`. -/
def phi (k lo : ℕ) (i : Fin (k + 1)) (q : Bool × Bool) : Bool :=
  if i.val < lo + 1 then q.2 else if i = Fin.last k then true else q.1

/-- A key's destination at stage `lo + 1`. -/
def dd (k lo : ℕ) (a : Fin (k + 1) → Bool × Bool) : Bits (k + 1) := fun i => phi k lo i (a i)

lemma card_snd_le (b : Bool) :
    (Finset.univ.filter (fun q : Bool × Bool => q.2 = b)).card ≤ 2 := by
  cases b <;> decide

lemma card_fst_le (b : Bool) :
    (Finset.univ.filter (fun q : Bool × Bool => q.1 = b)).card ≤ 2 := by
  cases b <;> decide

lemma fiber_card_le (k lo : ℕ) (V : Bits (k + 1)) :
    (Finset.univ.filter (fun a => dd k lo a = V)).card ≤ 2 ^ k * 4 := by
  have hset : Finset.univ.filter (fun a => dd k lo a = V) =
      Fintype.piFinset (fun i => Finset.univ.filter (fun q => phi k lo i q = V i)) := by
    ext a
    simp [Fintype.mem_piFinset, dd, funext_iff]
  rw [hset, Fintype.card_piFinset, Fin.prod_univ_castSucc]
  refine Nat.mul_le_mul ?_ ?_
  · calc ∏ j : Fin k, (Finset.univ.filter
            (fun q => phi k lo j.castSucc q = V j.castSucc)).card
        ≤ ∏ _j : Fin k, 2 := by
          refine Finset.prod_le_prod fun j _ => ?_
          have hne := Fin.castSucc_ne_last j
          by_cases h1 : (j : ℕ) < lo + 1
          · simp only [phi, Fin.val_castSucc, h1, ↓reduceIte]
            exact card_snd_le _
          · simp only [phi, Fin.val_castSucc, h1, hne, ↓reduceIte]
            exact card_fst_le _
      _ = 2 ^ k := by simp
  · exact (Finset.card_le_univ _).trans (by simp)

lemma card_A (k : ℕ) :
    Fintype.card (Fin (k + 1) → Bool × Bool) = 2 ^ (k + 1) * 2 ^ (k + 1) := by
  simp [← mul_pow]

lemma law_bound (k lo : ℕ) (n : ℕ) (lam : ℝ≥0) (hn : (n : ℝ≥0) ≤ lam * 2 ^ k)
    (V : Bits (k + 1)) : (n : ℝ≥0) * law (dd k lo) V ≤ lam := by
  unfold law
  rw [card_A, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  have hf : ((Finset.univ.filter (fun a => dd k lo a = V)).card : ℝ≥0) ≤ 2 ^ k * 4 := by
    exact_mod_cast fiber_card_le k lo V
  calc (n : ℝ≥0) * ((Finset.univ.filter (fun a => dd k lo a = V)).card : ℝ≥0)
      ≤ (lam * 2 ^ k) * (2 ^ k * 4) := mul_le_mul' hn hf
    _ = lam * ((2 ^ (k + 1) * 2 ^ (k + 1) : ℕ) : ℝ≥0) := by push_cast; ring

variable {K : Type} [Fintype K]

/-- Splitting a joint assignment into old homes and words. -/
def splitEquiv (K : Type) (b : ℕ) :
    (K → Fin b → Bool × Bool) ≃ (K → Bits b) × (K → Bits b) where
  toFun g := (fun x i => (g x i).1, fun x i => (g x i).2)
  invFun p := fun x i => (p.1 x i, p.2 x i)
  left_inv _ := rfl
  right_inv _ := rfl

lemma rawArrivals_unit {b : ℕ} (pos h : K → Bits b) (j : ℕ) :
    rawArrivals pos h j = ∑ x, unitVec (dest pos h j x) := by
  funext V
  rw [Finset.sum_apply]
  simp only [rawArrivals, unitVec, Pi.single_apply]
  rw [Finset.sum_boole, Nat.cast_id]
  congr 1
  ext x
  simp [eq_comm]

/-- The double word average as one uniform average over joint assignments `K → A`, for an
old-home map `up` under which a key's destination at stage `j` is `D` of its pair. -/
lemma lhs_gen [DecidableEq K] {b : ℕ} (up : Bits b → Bits b) (j : ℕ)
    (D : (Fin b → Bool × Bool) → Bits b)
    (hD : ∀ (o h : K → Bits b) x, dest (fun x => up (o x)) h j x = D fun i => (o x i, h x i))
    (F : (Bits b → ℕ) → ℝ≥0∞) :
    wordAvg (fun o : K → Bits b => wordAvg (fun h : K → Bits b =>
      F (rawArrivals (fun x => up (o x)) h j))) =
      ∫⁻ v, F v ∂(convList (List.replicate (Fintype.card K) (unitLaw (law D)))) := by
  rw [bridge]
  set A := Fin b → Bool × Bool
  rw [RebuildBound.NetworkAverage.wordAvg_pair_equiv (splitEquiv K b), Fintype.card_fun,
    Nat.cast_pow]
  congr 1
  simp only [rawArrivals_unit, hD, splitEquiv, Equiv.coe_fn_mk]
  refine Fintype.sum_equiv ((Fintype.equivFin K).arrowCongr (Equiv.refl A)) _ _ fun g => ?_
  congr 1
  exact Fintype.sum_equiv (Fintype.equivFin K) _ _ fun x => by simp [Equiv.arrowCongr_apply]

/-- The double word average for P11d. -/
lemma lhs_eq [DecidableEq K] (k lo : ℕ) (F : (Bits (k + 1) → ℕ) → ℝ≥0∞) :
    wordAvg (fun o : K → Bits (k + 1) => wordAvg (fun h : K → Bits (k + 1) =>
      F (rawArrivals (fun x => Function.update (o x) (Fin.last k) true) h (lo + 1)))) =
      ∫⁻ v, F v ∂(convList (List.replicate (Fintype.card K) (unitLaw (law (dd k lo))))) :=
  lhs_gen (fun v => Function.update v (Fin.last k) true) (lo + 1) (dd k lo)
    (fun o h x => by funext i; simp [dest, dd, phi, Function.update_apply]) F

end OneKey

end RebuildBound.P11dProof

open RebuildBound.Spec RebuildBound.P11dProof in
theorem RebuildBound.P11d : RebuildBound.Spec.P11d_statement := by
  intro K _ _ k C P L lo R lam _hlo hK
  obtain ⟨hmono, hconv, hbound⟩ := RebuildBound.P11c_class C P L lo R
  have hfin : ∀ y, firstArrivalTest C P L lo R y ≠ ∞ := fun y =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top P,
      ENNReal.sum_ne_top.2 fun _ _ => ENNReal.natCast_ne_top _⟩) (hbound y)
  have hU := unitLaw_prob (law (dd k lo)) (sum_law _)
  rw [lhs_eq]
  -- P5a: key-by-key Pois(1) replacement at base point `0`.
  have h5a := RebuildBound.P5a (firstArrivalTest C P L lo R) hconv hfin
    (List.replicate (Fintype.card K) (unitLaw (law (dd k lo))))
    (fun μ hμ => (List.eq_of_mem_replicate hμ) ▸ hU) 0
  simp only [zero_add, List.map_replicate] at h5a
  -- P5b: splitting, then sums (in `poisson_chain`) and padding.
  rw [RebuildBound.P5b_split 1 _ (sum_law _)] at h5a
  refine h5a.trans (poisson_chain _ hmono _ _ lam ?_)
  intro V
  simp only [Pi.smul_apply, nsmul_eq_mul, one_mul]
  exact law_bound k lo _ lam hK V
