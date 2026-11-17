import RebuildBound.Proofs.P11d
import RebuildBound.Spec.P8c
import RebuildBound.Proofs.ShadowLaw.Block

/-!
# P11f and P11g: variants of P11d

Same route as P11d (bridge to a convolution of unit laws, P5a, P5b_split, P5b_conv, P5b_pad).
P11f: the joint (old home, word) pair `a : Fin b → Bool × Bool` per key, uniform on all
buckets. P11g: per key the word `Bits b` alone, with its own law (heterogeneous bridge over
`Fin n`), uniform on the aligned block of `2^(lo+1)` buckets around `pos x`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RebuildBound.P11fgProof

open RebuildBound.Spec RebuildBound.P11dProof

/-! ## P11f -/

section F

variable {K : Type} [Fintype K]

def phiF (b lo : ℕ) (i : Fin b) (q : Bool × Bool) : Bool :=
  if i.val < lo + 1 then q.2 else q.1

def ddF (b lo : ℕ) (a : Fin b → Bool × Bool) : Bits b := fun i => phiF b lo i (a i)

lemma fiber_card_leF (b lo : ℕ) (V : Bits b) :
    (Finset.univ.filter (fun a => ddF b lo a = V)).card ≤ 2 ^ b := by
  have hset : Finset.univ.filter (fun a => ddF b lo a = V) =
      Fintype.piFinset (fun i => Finset.univ.filter (fun q => phiF b lo i q = V i)) := by
    ext a
    simp [Fintype.mem_piFinset, ddF, funext_iff]
  rw [hset, Fintype.card_piFinset]
  calc ∏ j : Fin b, (Finset.univ.filter (fun q => phiF b lo j q = V j)).card
      ≤ ∏ _j : Fin b, 2 := by
        refine Finset.prod_le_prod' fun j _ => ?_
        by_cases h1 : (j : ℕ) < lo + 1
        · simp only [phiF, h1, ↓reduceIte]
          exact card_snd_le _
        · simp only [phiF, h1, ↓reduceIte]
          exact card_fst_le _
    _ = 2 ^ b := by simp

lemma card_AF (b : ℕ) :
    Fintype.card (Fin b → Bool × Bool) = 2 ^ b * 2 ^ b := by
  simp [← mul_pow]

lemma law_boundF (b lo : ℕ) (n : ℕ) (lam : ℝ≥0) (hn : (n : ℝ≥0) ≤ lam * 2 ^ b)
    (V : Bits b) : (n : ℝ≥0) * law (ddF b lo) V ≤ lam := by
  unfold law
  rw [card_AF, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  have hf : ((Finset.univ.filter (fun a => ddF b lo a = V)).card : ℝ≥0) ≤ 2 ^ b := by
    exact_mod_cast fiber_card_leF b lo V
  calc (n : ℝ≥0) * ((Finset.univ.filter (fun a => ddF b lo a = V)).card : ℝ≥0)
      ≤ (lam * 2 ^ b) * (2 ^ b) := mul_le_mul' hn hf
    _ = lam * ((2 ^ b * 2 ^ b : ℕ) : ℝ≥0) := by push_cast; ring

lemma lhs_eqF [DecidableEq K] (b lo : ℕ) (F : (Bits b → ℕ) → ℝ≥0∞) :
    wordAvg (fun o : K → Bits b => wordAvg (fun h : K → Bits b =>
      F (rawArrivals o h (lo + 1)))) =
      ∫⁻ v, F v ∂(convList (List.replicate (Fintype.card K) (unitLaw (law (ddF b lo))))) :=
  lhs_gen id (lo + 1) (ddF b lo) (fun o h x => by funext i; simp [dest, ddF, phiF]) F

end F

end RebuildBound.P11fgProof

open RebuildBound.Spec RebuildBound.P11fgProof RebuildBound.P11dProof in
theorem RebuildBound.P11f : RebuildBound.Spec.P11f_statement := by
  intro K _ _ b C P L lo R lam _hlo hK
  obtain ⟨hmono, hconv, hbound⟩ := RebuildBound.P11c_class C P L lo R
  have hfin : ∀ y, firstArrivalTest C P L lo R y ≠ ∞ := fun y =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top P,
      ENNReal.sum_ne_top.2 fun _ _ => ENNReal.natCast_ne_top _⟩) (hbound y)
  have hU := RebuildBound.P11dProof.unitLaw_prob (law (ddF b lo)) (sum_law _)
  rw [lhs_eqF]
  have h5a := RebuildBound.P5a (firstArrivalTest C P L lo R) hconv hfin
    (List.replicate (Fintype.card K) (unitLaw (law (ddF b lo))))
    (fun μ hμ => (List.eq_of_mem_replicate hμ) ▸ hU) 0
  simp only [zero_add, List.map_replicate] at h5a
  rw [RebuildBound.P5b_split 1 _ (sum_law _)] at h5a
  refine h5a.trans (RebuildBound.P11dProof.poisson_chain _ hmono _ _ lam ?_)
  intro V
  simp only [Pi.smul_apply, nsmul_eq_mul, one_mul]
  exact law_boundF b lo _ lam hK V

open RebuildBound.Spec RebuildBound.P11fgProof RebuildBound.P11dProof in
theorem RebuildBound.P11g : RebuildBound.Spec.P11g_statement := by
  intro K _ _ b C P L lo R lam pos hlo hpos
  obtain ⟨hmono, hconv, hbound⟩ := RebuildBound.P11c_class C P L lo R
  have hfin : ∀ y, firstArrivalTest C P L lo R y ≠ ∞ := fun y =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top P,
      ENNReal.sum_ne_top.2 fun _ _ => ENNReal.natCast_ne_top _⟩) (hbound y)
  set e := Fintype.equivFin K
  set d : Fin (Fintype.card K) → Bits b → Bits b := fun i => dG lo (pos (e.symm i)) with hd
  have hlhs : wordAvg (fun h : K → Bits b =>
      firstArrivalTest C P L lo R (rawArrivals pos h (lo + 1))) =
      ∫⁻ v, firstArrivalTest C P L lo R v
        ∂(convList (List.ofFn fun i => unitLaw (law (d i)))) := by
    simp only [rawArrivals_unit]
    exact wordAvg_bridgeH (fun x => dG lo (pos x)) (firstArrivalTest C P L lo R)
  rw [hlhs]
  haveI := fun (n : ℕ) (d : Fin n → Bits b → Bits b) => prob_ofFn n d
  have h5a := RebuildBound.P5a (firstArrivalTest C P L lo R) hconv hfin
    (List.ofFn fun i => unitLaw (law (d i)))
    (fun μ hμ => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hμ
      exact unitLaw_prob _ (sum_law _)) 0
  simp only [zero_add, List.map_ofFn, Function.comp_def, cp_law] at h5a
  refine h5a.trans (poisson_chainH _ hmono _ _ lam ?_)
  intro V
  rw [Equiv.sum_comp e.symm (fun x => law (dG lo (pos x)) V)]
  exact sum_law_bound lo hlo lam pos hpos V
