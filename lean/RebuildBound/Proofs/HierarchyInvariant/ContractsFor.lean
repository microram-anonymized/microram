import RebuildBound.Proofs.HierarchyInvariant.TopIndFor

/-!
# HierarchyInvariant: the jobs' contractsFor geom at a configuration with `Facts`
-/

namespace RebuildBound.HierarchyInvariantProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.DirectJob RebuildBound.Spec

theorem liveSet_mem {A B : Finset Rec} {x : Rec} (h : x ∈ liveSet A B) : x ∈ A ∨ x ∈ B := by
  simp only [liveSet, Finset.mem_filter, Finset.mem_union] at h
  rcases h.1 with h | h
  · exact Or.inr h
  · exact Or.inl h.1

theorem liveSet_inj {A B : List Rec} (hA : (A.map Rec.key).Nodup) (hB : (B.map Rec.key).Nodup) :
    ∀ x ∈ liveSet A.toFinset B.toFinset, ∀ y ∈ liveSet A.toFinset B.toFinset,
      x.key = y.key → x = y := by
  intro x hx y hy e
  simp only [liveSet, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
    List.mem_toFinset] at hx hy
  rcases hx.1 with hx | ⟨hx, hxn⟩ <;> rcases hy.1 with hy | ⟨hy, hyn⟩
  · exact List.inj_on_of_nodup_map hB hx hy e
  · exact absurd ⟨x, hx, e⟩ hyn
  · exact absurd ⟨y, hy, e.symm⟩ hxn
  · exact List.inj_on_of_nodup_map hA hx hy e

theorem toFinset_map' (l : List Rec) : (l.map Rec.key).toFinset = l.toFinset.image Rec.key := by
  ext; simp

section
variable (geom : HierarchyGeometry)
variable {tr : Trace} {N : Nat}

theorem sepInputsAt_eqFor (words : Words) (ℓ o : Nat) :
    sepInputsAt geom.cfg geom.shapes tr words ℓ o =
      sepInputs (geom.shapes.sep ℓ (geom.cfg.digitAt ℓ o))
        (table geom.cfg geom.shapes tr words ℓ (o - 1))
        (carryOf geom.cfg geom.shapes tr words ℓ o) := rfl

/-- The context of a potential separated job. -/
theorem sep_ctxFor (F : LowFacts geom.cfg geom.rows geom.direct) (hT : TracePremises geom.cfg N tr) (words : Words) {ℓ o : Nat}
    (hj : JobId.ordinary ℓ o ∈ geom.cfg.potentialJobs) (h2 : 2 ≤ ℓ) (hd2 : 2 ≤ geom.cfg.digitAt ℓ o) :
    ∃ g, geom.shapes.sep ℓ (geom.cfg.digitAt ℓ o) = g ∧ g.d = geom.cfg.digitAt ℓ o ∧
      g.U = geom.cfg.carry ℓ ∧ g.Valid ∧ g.C = 64 ∧ 0 < g.bTierPages ∧ val2 g.d = g.e ∧
      LInv geom.cfg N ℓ (o - 1) (jobWord geom.cfg words ℓ (o - 1))
        (table geom.cfg geom.shapes tr words ℓ (o - 1)) ∧
      geom.cfg.digitAt ℓ (o - 1) = geom.cfg.digitAt ℓ o - 1 ∧ geom.cfg.seed ℓ < o - 1 ∧
      CInv geom.cfg N ℓ (jobWord geom.cfg words ℓ o) (carryOf geom.cfg geom.shapes tr words ℓ o) := by
  obtain ⟨h1, hL, hv⟩ := pj_ordinary hj
  obtain ⟨hb2, -, -⟩ := F.fan ℓ h1 hL
  have hdvd : geom.cfg.fanout ℓ ∣ geom.cfg.seed ℓ := ⟨_, F.seed ℓ h1 hL⟩
  have hdb : geom.cfg.digitAt ℓ o ≤ geom.cfg.fanout ℓ := digit_le (by omega) o
  obtain ⟨g, hg, hgd, hgU, hgV, hC, hP, he⟩ := row_ofFor geom F h2 hL hd2 hdb
  have hp := pred_gt hdvd hv hd2
  exact ⟨g, hg, hgd, hgU, hgV, hC, hP, he, (lowFor geom F hT words ℓ h1 hL _ hp).1,
    digit_pred (by omega) hd2, hp, carry_invFor geom F hT words h2 hL.le hv⟩

theorem sepAt_aAllFor (words : Words) (ℓ o : Nat) :
    (sepInputsAt geom.cfg geom.shapes tr words ℓ o).aAll =
      (table geom.cfg geom.shapes tr words ℓ (o - 1)).records := rfl

theorem sepAt_bAllFor (words : Words) (ℓ o : Nat)
    (hP : 0 < (geom.shapes.sep ℓ (geom.cfg.digitAt ℓ o)).bTierPages) :
    (sepInputsAt geom.cfg geom.shapes tr words ℓ o).bAll =
      (carryOf geom.cfg geom.shapes tr words ℓ o).records := by
  rw [sepInputsAt_eqFor geom, sep_bAll_pos _ hP]

theorem finish_belowFor (F : LowFacts geom.cfg geom.rows geom.direct) (G : TopFacts geom) (hT : TracePremises geom.cfg N tr) (hN : N ≤ geom.keyCapacity)
    (words : Words) {o : Nat} (ho : geom.cfg.seed geom.cfg.levels < o) :
    ∀ x ∈ (finishInputsAt geom.cfg geom.shapes tr words o).aAll ++
      (finishInputsAt geom.cfg geom.shapes tr words o).bAll, x.key.toNat < N := by
  intro x hx
  rw [finishInputsAt_eqFor geom, fin_aAll, fin_bAll] at hx
  rcases List.mem_append.1 hx with h | h
  · exact tpReference_P (P := fun x => x.key.toNat < N) _ _ _ _
      (fun y hy => top_belowFor geom F G hT hN words _ y (by rwa [prep_aAll] at hy)) x h
  · exact (carry_invFor geom F hT words F.levels2 le_rfl ho).below x h

theorem contractsFor (F : LowFacts geom.cfg geom.rows geom.direct) (G : TopFacts geom) (hN : N ≤ geom.keyCapacity) (hT : TracePremises geom.cfg N tr)
    (hU : UnshPromise geom.cfg geom.shapes tr) (words : Words) :
    JobContracts geom.cfg geom.shapes tr N words := by
  have hL2 := F.levels2
  have hTop : ∀ o, (JobId.topPrepare o ∈ geom.cfg.potentialJobs ∨ JobId.topFinish o ∈ geom.cfg.potentialJobs) →
      TInvFor geom.top N (jobWord geom.cfg words geom.cfg.levels (o - 1))
        (table geom.cfg geom.shapes tr words geom.cfg.levels (o - 1)) := fun o h => by
    obtain ⟨h1, h2⟩ := pj_top h
    exact top_inv'For geom F G hT hN hU words (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- sepShape
    intro ℓ o hj h2 hd2
    obtain ⟨g, hg, hgd, hgU, -, hC, hP, -, hI, hdg, -, hc⟩ := sep_ctxFor geom F hT words hj h2 hd2
    rw [sepInputsAt_eqFor geom, hg]
    exact sep_shape_pos hgd hgU hC hP hdg hI hc
  · -- sepKeysA
    intro ℓ o hj h2 hd2 words'
    obtain ⟨h1, hL, -⟩ := pj_ordinary hj
    rw [sepAt_aAllFor geom, sepAt_aAllFor geom, toFinset_map', toFinset_map',
      low_recsFor geom F hT words words' ℓ h1 hL]
  · -- sepKeysB
    intro ℓ o hj h2 hd2 words'
    obtain ⟨g, hg, -, -, -, -, hP, -⟩ := sep_ctxFor geom F hT words hj h2 hd2
    obtain ⟨h1, hL, -⟩ := pj_ordinary hj
    rw [sepAt_bAllFor geom words ℓ o (by rw [hg]; exact hP), sepAt_bAllFor geom words' ℓ o (by rw [hg]; exact hP),
      toFinset_map', toFinset_map']
    unfold carryOf
    rw [low_recsFor geom F hT words words' (ℓ - 1) (by omega) (by omega)]
  · -- sepLoadA
    intro ℓ o hj h2 hd2
    obtain ⟨-, -, -, -, -, -, -, -, hI, hdg, -, -⟩ := sep_ctxFor geom F hT words hj h2 hd2
    rw [sepAt_aAllFor geom]
    have := hI.card
    rwa [hdg] at this
  · -- sepLoadB
    intro ℓ o hj h2 hd2
    obtain ⟨g, hg, -, -, -, -, hP, -, -, -, -, hc⟩ := sep_ctxFor geom F hT words hj h2 hd2
    rw [sepAt_bAllFor geom words ℓ o (by rw [hg]; exact hP)]
    exact hc.card
  · -- sepBelow
    intro ℓ o hj h2 hd2 x hx
    obtain ⟨g, hg, -, -, -, -, hP, -, hI, -, -, hc⟩ := sep_ctxFor geom F hT words hj h2 hd2
    rw [sepAt_aAllFor geom, sepAt_bAllFor geom words ℓ o (by rw [hg]; exact hP)] at hx
    rcases List.mem_append.1 hx with h | h
    · exact hI.below x h
    · exact hc.below x h
  · -- prepShape
    intro o hj
    exact prep_shapeFor geom.top geom.prep G.prepC G.prepT (hTop o (Or.inl hj))
  · -- prepKeys
    intro o hj words'
    obtain ⟨h1, h2⟩ := pj_top (Or.inl hj)
    rw [prepInputsAt_eqFor geom, prepInputsAt_eqFor geom, prep_aAll, prep_aAll, toFinset_map',
      toFinset_map', top_recsFor geom F G hT hN hU words words' (o - 1) (by omega)]
  · -- prepLoad
    intro o hj
    rw [prepInputsAt_eqFor geom, prep_aAll]
    refine (keys_card_le _ (top_belowFor geom F G hT hN words _)).trans ?_
    change _ ≤ geom.cfg.load * geom.prep.T
    rw [F.load, G.prepT]
    exact hN.trans G.capacity
  · -- prepBelow
    intro o hj x hx
    rw [prepInputsAt_eqFor geom, prep_aAll] at hx
    exact top_belowFor geom F G hT hN words _ x hx
  · -- finishShape
    intro o hj
    obtain ⟨h1, h2⟩ := pj_top (Or.inr hj)
    exact (top_stepFor geom F G hT hU words h1 h2 (hTop o (Or.inr hj))).1
  · -- finishRecsA
    intro o hj words'
    obtain ⟨h1, h2⟩ := pj_top (Or.inr hj)
    have hw : ∀ ws : Words, (finishInputsAt geom.cfg geom.shapes tr ws o).aAll.toFinset =
        ((table geom.cfg geom.shapes tr ws geom.cfg.levels (o - 1)).records.filter
          fun r => !flagged tr.unsh r).toFinset := by
      intro ws
      have := (top_stepFor geom F G hT hU ws h1 h2
        (top_inv'For geom F G hT hN hU ws (by omega) (by omega))).2.2.2
      rw [List.toFinset_eq_of_perm _ _ this, prepInputsAt_eqFor geom, survivors_eq]
    rw [hw, hw, List.toFinset_filter, List.toFinset_filter,
      top_recsFor geom F G hT hN hU words words' (o - 1) (by omega)]
  · -- finishRecsB
    intro o hj words'
    rw [finishInputsAt_eqFor geom, finishInputsAt_eqFor geom, fin_bAll, fin_bAll]
    unfold carryOf
    exact low_recsFor geom F hT words words' (geom.cfg.levels - 1) (by omega) (by omega) _
  · -- finishLoadA
    intro o hj
    obtain ⟨h1, h2⟩ := pj_top (Or.inr hj)
    have hs := (top_stepFor geom F G hT hU words h1 h2 (hTop o (Or.inr hj))).1
    have hb := finish_belowFor geom F G hT hN words h1
    refine (toFinset_card_le _ hs.aNodup
      (fun x hx => hb x (List.mem_append_left _ hx))).trans ?_
    rw [F.load]
    exact hN.trans G.capacity
  · -- finishLoadW
    intro o hj
    obtain ⟨h1, h2⟩ := pj_top (Or.inr hj)
    have hs := (top_stepFor geom F G hT hU words h1 h2 (hTop o (Or.inr hj))).1
    have hb := finish_belowFor geom F G hT hN words h1
    refine (card_le_of_keys (N := N) _ (liveSet_inj hs.aNodup hs.bNodup) ?_).trans ?_
    · intro x hx
      rcases liveSet_mem hx with h | h
      · exact hb x (List.mem_append_left _ (List.mem_toFinset.1 h))
      · exact hb x (List.mem_append_right _ (List.mem_toFinset.1 h))
    · rw [F.load]
      exact hN.trans G.capacity
  · -- finishBelow
    intro o hj
    exact finish_belowFor geom F G hT hN words (pj_top (Or.inr hj)).1
  · -- initCount
    exact init_lenFor geom G hT hN
  · -- tableBelow
    intro ℓ v
    by_cases h0 : ℓ = 0 ∨ geom.cfg.levels < ℓ
    · rw [table_base (by tauto), base_low (by omega)]
      intro x hx; simp [records_empty] at hx
    · by_cases hL : ℓ = geom.cfg.levels
      · subst hL; exact top_belowFor geom F G hT hN words v
      · exact low_belowFor geom F hT words (by omega) (by omega) v
  · -- keysFlow
    intro ℓ v h1 hL hv
    exact low_flowFor geom F hT words h1 hL hv

end

end RebuildBound.HierarchyInvariantProof
