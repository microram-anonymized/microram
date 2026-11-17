import RebuildBound.Proofs.SG1p.Terms
import RebuildBound.Spec.SepBound

/-!
# SG1p: the three witness terms with `min(B_sub, D Φ_K)`
-/

open scoped ENNReal NNReal

namespace RebuildBound.SG1pProof

open RebuildBound.Model RebuildBound.Spec RebuildBound.SG1Proof RebuildBound.P11dProof
  RebuildBound.G3Proof

variable {g : SepGeom} (L : SJobLaw g) {lam D : ℝ≥0}

/-- **The stage term with the positive series.** -/
theorem stage_termP (hg : g.Valid) (hL : SInputLaw L lam D) (j : ℕ) (hj : j < g.k)
    (S K' : ℕ) (hSK : S < K') :
    L.prob (fun hist w => S < sRawStageExcess g (L.wOld hist) w (L.inputs hist w) j) ≤
      ENNReal.ofReal (D * Phi K' g.N g.C lam S) := by
  have hN := N_pos g hg
  have hM := M_pos hg
  have hjW : j + 1 ≤ L.W := by have := hL.wide; omega
  have hMpos : (0 : ℝ≥0) < ((((g.d - 1) * g.U : ℕ)) : ℝ≥0) := by exact_mod_cast hM
  haveI : Nonempty (Fin ((g.d - 1) * g.U) × Fin (2 ^ L.W)) :=
    ⟨(⟨0, hM⟩, ⟨0, by positivity⟩)⟩
  refine le_trans (gen_bound L hL.weight_sum L.KA Finset.subset_union_left (M := (g.d - 1) * g.U) hM
    (fun hist x => ⟨g.oldHome (L.wOld hist x.1), oldHome_lt g hg.2.1 _⟩) D ?_
    (fun (o : Fin ((g.d - 1) * g.U)) (a : Fin (2 ^ L.W)) =>
      dN g.N hN (G1Proof.rd g.U j o a))
    1 (law (fun p : Fin ((g.d - 1) * g.U) × Fin (2 ^ L.W) =>
        dN g.N hN (G1Proof.rd g.U j p.1 p.2)))
    (sum_law _) (fun v => by rw [one_mul]) (1 / (((g.d - 1) * g.U : ℕ) : ℝ≥0)) lam
    (fun v => stage_law_le g hg L.W j hj hjW v) ?_ g.C S K' hSK _ ?_) ?_
  · intro o
    have hd := hL.density o
    convert hd using 2
    ext hist
    simp [funext_iff, Fin.ext_iff]
  · rw [mul_one_div, div_le_iff₀ hMpos]
    exact_mod_cast hL.aLoad
  · intro hist h hS
    have hv := hL.shape hist h
    have e1 : sRawStageExcess g (L.wOld hist) (L.wordFn h) (L.inputs hist (L.wordFn h)) j =
        ∑ v : Fin g.N, (stageX L j hist h v - g.C) := by
      unfold sRawStageExcess
      rw [G1Proof.list_sum_range, Finset.sum_range]
      rfl
    rw [e1] at hS
    have h2 : ∑ v : Fin g.N, (stageX L j hist h v - g.C) =
        ∑ v : Fin g.N, ((∑ x : L.KA, unitVec (dN g.N hN (G1Proof.rd g.U j
          (g.oldHome (L.wOld hist x.1)) (h ⟨x.1, Finset.subset_union_left x.2⟩).val))) v - g.C) := by
      refine Finset.sum_congr rfl fun v _ => ?_
      have := count_vec hN (L.inputs hist (L.wordFn h)).aAll hv.aNodup L.KA (hL.aKeys hist)
        (fun x => G1Proof.rd g.U j (g.oldHome (L.wOld hist x)) (L.wordFn h x))
        (fun x _ => rd_lt g hg j hj _ _ (oldHome_lt g hg.2.1 _)) v
      unfold stageX
      rw [show ((L.inputs hist (L.wordFn h)).aAll.countP fun r =>
          sRawDest g (L.wOld hist) (L.wordFn h) j r.key == (v : ℕ)) = _ from this]
      have hs : (∑ x : L.KA, unitVec (dN g.N hN (G1Proof.rd g.U j (g.oldHome (L.wOld hist x.1))
            (L.wordFn h x.1)))) =
          ∑ x : L.KA, unitVec (dN g.N hN (G1Proof.rd g.U j (g.oldHome (L.wOld hist x.1))
            (h ⟨x.1, Finset.subset_union_left x.2⟩).val)) :=
        Finset.sum_congr rfl (fun x _ => by
          rw [wordFn_val L h ⟨x.1, Finset.subset_union_left x.2⟩])
      rw [hs]
    exact lt_of_lt_of_eq hS h2
  · simp only [Fintype.card_fin, ENNReal.coe_one, one_pow, mul_one]
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg D), ENNReal.ofReal_coe_nnreal]

/-- **The radix term with the positive series.** -/
theorem radix_termP (hg : g.Valid) (hL : SInputLaw L lam D) (S K' : ℕ) (hSK : S < K') :
    L.prob (fun hist w => S < sAHomeExcess g w (L.inputs hist w)) ≤
      ENNReal.ofReal (g.curDensity L.W L.KA.card * Phi K' g.N g.C lam S) := by
  refine home_termP L hg hL L.KA Finset.subset_union_left (KA_card_le L hL)
    (fun hist h => (L.inputs hist (L.wordFn h)).aAll)
    (fun hist h => (hL.shape hist h).aNodup) (fun hist h => hL.aKeys hist) S K' hSK _ ?_
  intro hist h hS
  refine lt_of_lt_of_eq hS ?_
  unfold sAHomeExcess sExcess
  rw [G1Proof.list_sum_range, Finset.sum_range]

/-- **The insertion and output term with the positive series.** -/
theorem union_termP (hg : g.Valid) (hL : SInputLaw L lam D) (S K' : ℕ) (hSK : S < K') :
    L.prob (fun hist w => S < sHomeExcess g w (L.inputs hist w)) ≤
      ENNReal.ofReal (g.curDensity L.W (L.KA ∪ L.KB).card * Phi K' g.N g.C lam S) := by
  refine home_termP L hg hL (L.KA ∪ L.KB) subset_rfl (KAB_card_le L hL hg)
    (fun hist h => (L.inputs hist (L.wordFn h)).winners)
    (fun hist h => (winners_keys _ (hL.shape hist h).aNodup (hL.shape hist h).bNodup).1)
    (fun hist h => by
      have ha : ((L.inputs hist (L.wordFn h)).aAll.map Rec.key).toFinset = L.KA := hL.aKeys hist
      have hb : ((L.inputs hist (L.wordFn h)).bAll.map Rec.key).toFinset = L.KB := hL.bKeys hist h
      rw [(winners_keys _ (hL.shape hist h).aNodup (hL.shape hist h).bNodup).2, ha, hb]) S K' hSK _ ?_
  intro hist h hS
  refine lt_of_lt_of_eq hS ?_
  unfold sHomeExcess sExcess
  rw [G1Proof.list_sum_range, Finset.sum_range]

end RebuildBound.SG1pProof
