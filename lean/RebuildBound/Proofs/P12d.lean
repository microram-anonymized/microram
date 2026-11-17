import RebuildBound.Proofs.ShadowLaw.Unit
import RebuildBound.Spec.P12

/-!
# P12d: Poissonization of the phantom arrivals in `r` blocks

The conditional `P12d_of : P12c → P12d`, adapted from P11d (`Proofs/P11d.lean`), whose
bridge (`P11dProof.bridge`, uniform averages as convolutions of `unitLaw (law d)`) and
Poisson chain (`P11dProof.poisson_chain`) are reused verbatim.

* **One key.** A key's data is `a : S × Bits b` (starting node in `S`, word); its
  destination at stage `lo + 1` is `dd S lo a`. The fiber of a node `V` injects into
  `Bits b` via `a ↦ (bits < lo + 1 of a.1, bits ≥ lo + 1 of a.2)`, because the fiber
  fixes the block, the start's bits `≥ lo + 1` and the word's bits `< lo + 1`. So the
  fiber has at most `2^b` elements out of `|S| 2^b`, and each node's mean is at most
  `|K| / |S| ≤ λ`. (`lo < b` is not used.)
* **Chain.** P5a (with P12c's class facts), P5b_split, P5b_conv and P5b_pad, as in P11d.

No obstacle: the measure-based API sufficed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RebuildBound.P12dProof

open RebuildBound.Spec RebuildBound.P11dProof

variable {r b : ℕ}

/-- A key's destination at stage `lo + 1` from its starting node in `S` and its word. -/
def dd (S : Finset (RNode r b)) (lo : ℕ) (a : S × Bits b) : RNode r b :=
  ((a.1 : RNode r b).1, fun i => if i.val < lo + 1 then a.2 i else (a.1 : RNode r b).2 i)

lemma fiber_card_le (S : Finset (RNode r b)) (lo : ℕ) (V : RNode r b) :
    (Finset.univ.filter (fun a : S × Bits b => dd S lo a = V)).card ≤ 2 ^ b := by
  have hle : (Finset.univ.filter (fun a : S × Bits b => dd S lo a = V)).card ≤
      (Finset.univ : Finset (Bits b)).card := by
    refine Finset.card_le_card_of_injOn
      (fun a i => if i.val < lo + 1 then (a.1 : RNode r b).2 i else a.2 i)
      (by intro a _; exact Finset.mem_coe.2 (Finset.mem_univ _)) ?_
    intro a ha a' ha' heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha ha'
    have hd := ha.trans ha'.symm
    simp only [dd, Prod.mk.injEq, funext_iff] at hd heq
    obtain ⟨h1, h2⟩ := hd
    refine Prod.ext (Subtype.ext (Prod.ext h1 (funext fun i => ?_))) (funext fun i => ?_)
    · by_cases hi : i.val < lo + 1
      · simpa [hi] using heq i
      · simpa [hi] using h2 i
    · by_cases hi : i.val < lo + 1
      · simpa [hi] using h2 i
      · simpa [hi] using heq i
  simpa using hle

lemma card_A (S : Finset (RNode r b)) : Fintype.card (S × Bits b) = S.card * 2 ^ b := by
  simp

lemma law_bound (S : Finset (RNode r b)) (hS : S.Nonempty) (lo n : ℕ) (lam : ℝ≥0)
    (hn : (n : ℝ≥0) ≤ lam * S.card) (V : RNode r b) : (n : ℝ≥0) * law (dd S lo) V ≤ lam := by
  unfold law
  have hpos : (0 : ℝ≥0) < ((S.card * 2 ^ b : ℕ) : ℝ≥0) :=
    Nat.cast_pos.mpr (Nat.mul_pos hS.card_pos (Nat.two_pow_pos b))
  rw [card_A, ← mul_div_assoc, div_le_iff₀ hpos]
  have hf : ((Finset.univ.filter (fun a => dd S lo a = V)).card : ℝ≥0) ≤ 2 ^ b := by
    exact_mod_cast fiber_card_le S lo V
  calc (n : ℝ≥0) * ((Finset.univ.filter (fun a => dd S lo a = V)).card : ℝ≥0)
      ≤ (lam * S.card) * 2 ^ b := mul_le_mul' hn hf
    _ = lam * ((S.card * 2 ^ b : ℕ) : ℝ≥0) := by push_cast; ring

variable {K : Type} [Fintype K]

/-- Splitting a joint assignment into starting nodes and words. -/
def splitEquiv (K : Type) (S : Finset (RNode r b)) :
    (K → S × Bits b) ≃ (K → S) × (K → Bits b) where
  toFun g := (fun x => (g x).1, fun x => (g x).2)
  invFun p := fun x => (p.1 x, p.2 x)
  left_inv _ := rfl
  right_inv _ := rfl

lemma rrawArrivals_eq (S : Finset (RNode r b)) (lo : ℕ) (g : K → S × Bits b) :
    rrawArrivals (fun x => ((splitEquiv K S g).1 x : RNode r b)) (splitEquiv K S g).2
        (lo + 1) =
      ∑ x, unitVec (dd S lo (g x)) := by
  have hdest : ∀ x, rdest (fun x => ((splitEquiv K S g).1 x : RNode r b))
      (splitEquiv K S g).2 (lo + 1) x = dd S lo (g x) := fun x => rfl
  funext V
  rw [Finset.sum_apply]
  simp only [rrawArrivals, hdest, unitVec, Pi.single_apply]
  rw [Finset.sum_boole, Nat.cast_id]
  congr 1
  ext x
  simp [eq_comm]

/-- The double average as one uniform average over joint assignments `K → S × Bits b`. -/
lemma lhs_eq [DecidableEq K] (S : Finset (RNode r b)) (hS : S.Nonempty) (lo : ℕ)
    (F : (RNode r b → ℕ) → ℝ≥0∞) :
    uniformAvg (fun o : K → S => wordAvg (fun h : K → Bits b =>
      F (rrawArrivals (fun x => (o x : RNode r b)) h (lo + 1)))) =
      ∫⁻ v, F v ∂(convList (List.replicate (Fintype.card K) (unitLaw (law (dd S lo))))) := by
  have : Nonempty S := hS.to_subtype
  rw [bridge]
  set A := S × Bits b
  have hc : (Fintype.card (K → S) : ℝ≥0∞) * Fintype.card (K → Bits b) =
      (Fintype.card A : ℝ≥0∞) ^ Fintype.card K := by
    have h1 := Fintype.card_congr (splitEquiv K S)
    rw [Fintype.card_prod, Fintype.card_fun] at h1
    exact_mod_cast h1.symm
  unfold uniformAvg wordAvg
  rw [Finset.mul_sum, ← hc]
  simp only [← mul_assoc]
  rw [← Finset.mul_sum, ENNReal.mul_inv (by simp) (by simp)]
  congr 1
  rw [← Fintype.sum_prod_type', ← (splitEquiv K S).sum_comp]
  simp only [rrawArrivals_eq]
  refine Fintype.sum_equiv ((Fintype.equivFin K).arrowCongr (Equiv.refl A)) _ _ fun g => ?_
  congr 1
  exact Fintype.sum_equiv (Fintype.equivFin K) _ _ fun x => by simp [Equiv.arrowCongr_apply]

end RebuildBound.P12dProof

open RebuildBound.Spec RebuildBound.P11dProof RebuildBound.P12dProof in
theorem RebuildBound.P12d_of (hc : RebuildBound.Spec.P12c_statement) :
    RebuildBound.Spec.P12d_statement := by
  intro K _ _ r b C P L lo R q lam S hS _hlo hK
  obtain ⟨hmono, hconv, hbound⟩ := hc (r := r) (b := b) C P L lo R q
  have hfin : ∀ y, rFirstArrivalTest C P L lo R q y ≠ ∞ := fun y =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top P,
      ENNReal.sum_ne_top.2 fun _ _ => ENNReal.natCast_ne_top _⟩) (hbound y)
  have : Nonempty S := hS.to_subtype
  have hU := unitLaw_prob (law (dd S lo)) (sum_law _)
  rw [lhs_eq S hS]
  -- P5a: key-by-key Pois(1) replacement at base point `0`.
  have h5a := RebuildBound.P5a (rFirstArrivalTest C P L lo R q) hconv hfin
    (List.replicate (Fintype.card K) (unitLaw (law (dd S lo))))
    (fun μ hμ => (List.eq_of_mem_replicate hμ) ▸ hU) 0
  simp only [zero_add, List.map_replicate] at h5a
  -- P5b: splitting, then sums (in `poisson_chain`) and padding.
  rw [RebuildBound.P5b_split 1 _ (sum_law _)] at h5a
  refine h5a.trans (poisson_chain _ hmono _ _ lam ?_)
  intro V
  simp only [Pi.smul_apply, nsmul_eq_mul, one_mul]
  exact law_bound S hS lo _ lam hK V
