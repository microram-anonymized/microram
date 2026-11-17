import RebuildBound.Proofs.P12d
import RebuildBound.Proofs.ShadowLaw.Block
import RebuildBound.Spec.P13

/-!
# P13d and P13g: Poissonization for the cap-free first-arrival test

The conditionals `P13d_of`, `P13g_of : P13c → …`. The chain of `P12d_of` (resp. `P11g`) is
generic in the test given monotone, directionally convex and bounded by `P + Σ N`, so the
lemmas of `P12dProof` and `P11fgProof` are reused. For P13g each key has its own law on
`RNode r b` (its block is fixed, the word's low bits replace the start's).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RebuildBound.P13dgProof

open RebuildBound.Spec RebuildBound.P11dProof RebuildBound.P11fgProof

variable {r b : ℕ}

/-- A key's destination from its start `p` and word `w`. -/
def dR (lo : ℕ) (p : RNode r b) (w : Bits b) : RNode r b := (p.1, dG lo p.2 w)

lemma sum_law_boundR (lo : ℕ) (hlo : lo < b) (lam : ℝ≥0) {K : Type} [Fintype K]
    (pos : K → RNode r b)
    (hpos : ∀ v, ((Finset.univ.filter fun x => pos x = v).card : ℝ≥0) ≤ lam) (V : RNode r b) :
    ∑ x, law (dR lo (pos x)) V ≤ lam := by
  classical
  let T := {x : K // (pos x).1 = V.1}
  have h1 : ∑ x, law (dR lo (pos x)) V = ∑ x : T, law (dG lo (pos x.1).2) V.2 := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun x => (pos x).1 = V.1)]
    have h0 : ∑ x : {x // ¬ (pos x).1 = V.1}, law (dR lo (pos x.1)) V = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      unfold law
      have : (Finset.univ.filter fun w => dR lo (pos x.1) w = V) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun w _ hw => ?_
        have hw' : dR lo (pos x.1) w = V := hw
        have h1 := congrArg Prod.fst hw'
        exact x.2 h1
      simp [this]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold law
    have hset : (Finset.univ.filter fun w => dR lo (pos x.1) w = V) =
        Finset.univ.filter fun w => dG lo (pos x.1).2 w = V.2 := by
      refine Finset.filter_congr fun w _ => ?_
      constructor
      · intro h; exact congrArg Prod.snd h
      · intro h; exact Prod.ext x.2 h
    rw [hset]
  rw [h1]
  refine sum_law_bound lo hlo lam (fun x : T => (pos x.1).2) ?_ V.2
  intro v
  refine le_trans ?_ (hpos (V.1, v))
  have : (Finset.univ.filter fun x : T => (pos x.1).2 = v).card =
      (Finset.univ.filter fun x : K => pos x = (V.1, v)).card := by
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact Prod.ext x.2 hx
    · intro x _ y _ h; exact Subtype.ext h
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact ⟨⟨y, by rw [hy]⟩, by simp [hy], rfl⟩
  exact_mod_cast this.le

lemma rrawArrivals_unit {K : Type} [Fintype K] [DecidableEq K] (pos : K → RNode r b)
    (h : K → Bits b) (j : ℕ) :
    rrawArrivals pos h j = ∑ x, unitVec (rdest pos h j x) := by
  funext V
  rw [Finset.sum_apply]
  simp only [rrawArrivals, unitVec, Pi.single_apply]
  rw [Finset.sum_boole, Nat.cast_id]
  congr 1
  ext x
  simp [eq_comm]

end RebuildBound.P13dgProof

open RebuildBound.Spec RebuildBound.P12dProof RebuildBound.P11dProof in
theorem RebuildBound.P13d_of (hc : RebuildBound.Spec.P13c_statement) :
    RebuildBound.Spec.P13d_statement := by
  intro K _ _ r b C P L lo R q lam S hS _hlo hK
  obtain ⟨hmono, hconv, hbound⟩ := hc (r := r) (b := b) C P L lo R q
  have hfin : ∀ y, rFirstArrivalTest0 C P L lo R q y ≠ ∞ := fun y =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top P,
      ENNReal.sum_ne_top.2 fun _ _ => ENNReal.natCast_ne_top _⟩) (hbound y)
  have : Nonempty S := hS.to_subtype
  have hU := unitLaw_prob (law (dd S lo)) (sum_law _)
  rw [lhs_eq S hS]
  have h5a := RebuildBound.P5a (rFirstArrivalTest0 C P L lo R q) hconv hfin
    (List.replicate (Fintype.card K) (unitLaw (law (dd S lo))))
    (fun μ hμ => (List.eq_of_mem_replicate hμ) ▸ hU) 0
  simp only [zero_add, List.map_replicate] at h5a
  rw [RebuildBound.P5b_split 1 _ (sum_law _)] at h5a
  refine h5a.trans (poisson_chain _ hmono _ _ lam ?_)
  intro V
  simp only [Pi.smul_apply, nsmul_eq_mul, one_mul]
  exact law_bound S hS lo _ lam hK V

open RebuildBound.Spec RebuildBound.P11fgProof RebuildBound.P11dProof RebuildBound.P13dgProof in
theorem RebuildBound.P13g_of (hc : RebuildBound.Spec.P13c_statement) :
    RebuildBound.Spec.P13g_statement := by
  intro K _ _ r b C P L lo R q lam pos hlo hpos
  obtain ⟨hmono, hconv, hbound⟩ := hc (r := r) (b := b) C P L lo R q
  have hfin : ∀ y, rFirstArrivalTest0 C P L lo R q y ≠ ∞ := fun y =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top P,
      ENNReal.sum_ne_top.2 fun _ _ => ENNReal.natCast_ne_top _⟩) (hbound y)
  set e := Fintype.equivFin K
  set d : Fin (Fintype.card K) → Bits b → RNode r b := fun i => dR lo (pos (e.symm i)) with hd
  have hlhs : wordAvg (fun h : K → Bits b =>
      rFirstArrivalTest0 C P L lo R q (rrawArrivals pos h (lo + 1))) =
      ∫⁻ v, rFirstArrivalTest0 C P L lo R q v
        ∂(convList (List.ofFn fun i => unitLaw (law (d i)))) := by
    simp only [rrawArrivals_unit]
    exact wordAvg_bridgeH (fun x => dR lo (pos x)) (rFirstArrivalTest0 C P L lo R q)
  rw [hlhs]
  haveI := fun (n : ℕ) (d : Fin n → Bits b → RNode r b) => prob_ofFn n d
  have h5a := RebuildBound.P5a (rFirstArrivalTest0 C P L lo R q) hconv hfin
    (List.ofFn fun i => unitLaw (law (d i)))
    (fun μ hμ => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hμ
      exact unitLaw_prob _ (sum_law _)) 0
  simp only [zero_add, List.map_ofFn, Function.comp_def, cp_law] at h5a
  refine h5a.trans (poisson_chainH _ hmono _ _ lam ?_)
  intro V
  rw [Equiv.sum_comp e.symm (fun x => law (dR lo (pos x)) V)]
  exact sum_law_boundR lo hlo lam pos hpos V
