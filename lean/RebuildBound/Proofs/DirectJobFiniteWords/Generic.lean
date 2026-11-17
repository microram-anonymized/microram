import RebuildBound.Spec.DirectJobFiniteWords
import RebuildBound.Proofs.DirectJobProbability
import RebuildBound.Proofs.SG1p.Terms

/-! Generic finite-word B, union and first-digit bounds. Concrete numerical
certificates are imported only by the selected parent module. -/
open scoped ENNReal NNReal
namespace RebuildBound
open Model Model.DirectJob Spec

private theorem prefix_keys (rs : List Rec) :
    ((DirectPrefix.winners rs).map Rec.key).toFinset = (rs.map Rec.key).toFinset := by
  ext key
  simpa only [List.mem_toFinset] using DirectPrefixKeys rs key

theorem DirectJobBFiniteWords : DirectJobBFiniteWords_statement := by
  intro s L g lam direct cut hw hW hkeys hload hcut
  classical
  let dest : Fin 1 → Fin (2 ^ L.W) → Fin g.U := fun _ a => G3Proof.dHome g.K L.W a
  let q : Fin g.U → ℝ≥0 := fun _ => 1 / (g.U : ℝ≥0)
  have hU : (0 : ℝ≥0) < g.U := by unfold Geometry.U; positivity
  have hq : ∑ v, q v = 1 := by
    simp only [q, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hU.ne'
  have hlaw (v : Fin g.U) :
      P11dProof.law (fun p : Fin 1 × Fin (2 ^ L.W) => dest p.1 p.2) v ≤ 1 * q v := by
    have he : P11dProof.law (fun p : Fin 1 × Fin (2 ^ L.W) => dest p.1 p.2) v =
        P11dProof.law (G3Proof.dHome g.K L.W) v := by
      unfold P11dProof.law
      simp only [Finset.card_filter, Fintype.sum_prod_type, Finset.univ_unique,
        Fin.default_eq_zero, Finset.sum_singleton, Fintype.card_prod, Fintype.card_fin, one_mul]
      rfl
    exact le_of_eq (he.trans (by simpa [q, Geometry.U] using G3Proof.law_dHome hW v))
  have hh := SG1pProof.gen_bound L hw L.KB Finset.subset_union_right
    (M := 1) Nat.one_pos (fun _ _ => 0) 1 (by
      intro o
      have he : (Finset.univ.filter (fun hist : L.Hist => (fun _ : L.KB => (0 : Fin 1)) = o)) =
          Finset.univ := by
        ext hist
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        funext x
        exact Subsingleton.elim _ _
      simp [he, hw])
    dest 1 q hq hlaw (1 / (g.U : ℝ≥0)) lam (fun _ => le_rfl) (by
      rw [mul_one_div, div_le_iff₀ hU]
      exact hload)
    64 g.bCapacity cut hcut
    (fun hist word => g.bCapacity < bExcess g word (direct hist word)) (by
      intro hist h he
      rw [DirectJobBCount] at he
      apply lt_of_lt_of_eq he
      apply Finset.sum_congr rfl
      intro v _
      congr 1
      let rs := DirectPrefix.winners (direct hist (L.wordFn h)).bRecords
      have hk : (rs.map Rec.key).toFinset = L.KB :=
        (prefix_keys _).trans (hkeys hist h)
      have hc := SG1pProof.count_vec (N := g.U) (by unfold Geometry.U; positivity)
        rs (DirectPrefixUnique _) L.KB hk (fun key => L.wordFn h key % g.U)
        (fun _ _ => Nat.mod_lt _ (by unfold Geometry.U; positivity)) v
      change (rs.filter (fun r => L.wordFn h r.key % g.U == v.val)).length = _
      rw [← List.countP_eq_length_filter, hc]
      apply congrArg (fun f : Fin g.U → Nat => f v)
      apply Finset.sum_congr rfl
      intro key _
      congr 1
      apply Fin.ext
      rw [SG1pProof.dN_val _ _ _ (Nat.mod_lt _ (by unfold Geometry.U; positivity))]
      rw [SG1Proof.wordFn_val L h ⟨key.1, Finset.subset_union_right key.2⟩]
      rfl)
  simpa only [ENNReal.coe_one, one_pow, one_mul, Fintype.card_fin] using hh

private theorem matched_winners {s : SepGeom} (L : SJobLaw s) (lam D : ℝ≥0)
    (hL : SInputLaw L lam D) (direct : L.Hist → (Model.LogicalKey → Nat) → DirectJob.Inputs)
    (hm : DirectJobInputMatch L direct) (hist : L.Hist) (hw : L.Key → Fin (2 ^ L.W)) :
    (((direct hist (L.wordFn hw)).winners).map Rec.key).Nodup ∧
    (((direct hist (L.wordFn hw)).winners).map Rec.key).toFinset = L.KA ∪ L.KB := by
  let inp := direct hist (L.wordFn hw)
  let sinp : SInputs := ⟨inp.aMain, inp.aTier, [], [DirectPrefix.winners inp.bRecords]⟩
  have ha : sinp.aAll = (L.inputs hist (L.wordFn hw)).aAll := by
    simp only [sinp, SInputs.aAll, inp, (hm.a hist hw).1, (hm.a hist hw).2]
  have hb : sinp.bAll = DirectPrefix.winners inp.bRecords := by simp [sinp, SInputs.bAll]
  have he : sinp.winners = inp.winners := by
    simp [SInputs.winners, DirectJob.Inputs.winners, hb, sinp, SInputs.aAll, Inputs.aRecords]
  have hk := SG1Proof.winners_keys sinp (by rw [ha]; exact (hL.shape hist hw).aNodup)
    (by rw [hb]; exact DirectPrefixUnique _)
  have hak : ((L.inputs hist (L.wordFn hw)).aAll.map Rec.key).toFinset = L.KA := hL.aKeys hist
  rw [he, ha, hb, prefix_keys, hm.bKeys hist hw, hak] at hk
  exact hk

theorem DirectJobUnionFiniteWords : DirectJobUnionFiniteWords_statement := by
  intro s L g lam D direct cut hs hL hm hC hN hhome hcut
  have hh := SG1pProof.home_termP L hs hL (L.KA ∪ L.KB) (Finset.Subset.refl _)
    (SG1Proof.KAB_card_le L hL hs) (fun hist hw => (direct hist (L.wordFn hw)).winners)
    (fun hist hw => (matched_winners L lam D hL direct hm hist hw).1)
    (fun hist hw => (matched_winners L lam D hL direct hm hist hw).2)
    g.outputCapacity cut hcut
    (fun hist word => g.outputCapacity < (direct hist word).excess g word) (by
      intro hist hw he
      simpa only [Inputs.excess, G1Proof.list_sum_range, Finset.sum_range,
        hN, hC, hhome, sHomeCount, sHome] using he)
  simpa only [hC, hN] using hh

theorem DirectJobDigitOneFiniteWordsFor : DirectJobDigitOneFiniteWordsFor_statement := by
  intro s L g lam direct cut hg hd hw hW hk hload hcut
  apply le_trans (SG1Proof.prob_mono L (fun hist h he => ?_))
    (DirectJobBFiniteWords L g lam direct cut hw hW hk hload hcut)
  obtain ⟨e, he⟩ := he
  have hi := ((DirectJobFirstFailure g (L.wOld hist) (L.wordFn h)
    (direct hist (L.wordFn h)) e).1.mp he).2.1
  have he' : buildB g (L.wordFn h) (direct hist (L.wordFn h)) = .error e := by
    change runJob g (L.wOld hist) (L.wordFn h) (direct hist (L.wordFn h)) = .failed e at he
    simp only [runJob, hg, hi, not_true_eq_false, ite_false, hd, ite_true] at he
    split at he <;> simp_all
  exact (DirectJobBFailure g _ _ hi.2.2.2.2.1).mp ⟨e, he'⟩


end RebuildBound
