import RebuildBound.Proofs.HierarchyStructural
import RebuildBound.Proofs.IdealExposure
import RebuildBound.Proofs.AdaptiveTracePrefix
import RebuildBound.Proofs.HierarchyInvariant.ContractsFor
import RebuildBound.Proofs.HierarchyTopLaw.Cone

/-! Top preparation structure and finite-source locality. The temporary key
range bounds one finite trace restriction, independently of storage capacity.
All structural conclusions hold on total reference overflow continuations. -/
namespace RebuildBound.IdealTopPrepProof
open Model Model.Hierarchy Spec HierarchyInvariantProof HierarchyStructuralProof
open HierarchyLocalityProof OnlineCorrectnessProof

section
variable (g : HierarchyGeometry) {tr : Trace} {N : Nat}

/-- The top's record sets within the horizon do not depend on the tape. -/
theorem top_recs_length (F : LowFacts g.cfg g.rows g.direct) (G : TopFacts g) (hT : TracePremises g.cfg N tr) (hInit : tr.init.length ≤ g.init.C / 2 * g.init.T)
    (hU : UnshPromise g.cfg g.shapes tr) (words words' : Words) :
    ∀ v, v ≤ g.cfg.seed g.cfg.levels + g.cfg.ordinals g.cfg.levels →
      (table g.cfg g.shapes tr words g.cfg.levels v).records.toFinset =
        (table g.cfg g.shapes tr words' g.cfg.levels v).records.toFinset := by
  have hI : ∀ ws : Words, ∀ v, v ≤ g.cfg.seed g.cfg.levels →
      (table g.cfg g.shapes tr ws g.cfg.levels v).records.toFinset =
        (if g.cfg.initialized then tr.init else []).toFinset := by
    intro ws v hv
    exact List.toFinset_eq_of_perm _ _ (top_base_outFor_of_initLength g G hT hInit ws hv).2
  have hS : ∀ ws : Words, ∀ v, g.cfg.seed g.cfg.levels < v →
      v ≤ g.cfg.seed g.cfg.levels + g.cfg.ordinals g.cfg.levels →
      (table g.cfg g.shapes tr ws g.cfg.levels v).records.toFinset =
        (winSet ((table g.cfg g.shapes tr ws g.cfg.levels (v - 1)).records.filter
            fun r => !flagged tr.unsh r).toFinset
          (carryOf g.cfg g.shapes tr ws g.cfg.levels v).records.toFinset).filter
          fun r => !r.tomb := by
    intro ws v hv hvh
    have h := top_stepFor g F G hT hU ws hv hvh (top_inv'For_of_initLength g F G hT hInit hU ws (by omega) (by omega))
    rw [List.toFinset_eq_of_perm _ _ h.2.2.1]
    unfold TopInputs.live
    rw [List.toFinset_filter, tWinners_eq, win_toFinset,
      List.toFinset_eq_of_perm _ _ h.2.2.2, prepInputsAt_eqFor g, survivors_eq, finishInputsAt_eqFor g,
      fin_bAll]
  intro v hvh
  induction v with
  | zero => rw [hI words 0 (Nat.zero_le _), hI words' 0 (Nat.zero_le _)]
  | succ v ih =>
    by_cases hv : g.cfg.seed g.cfg.levels < v + 1
    · rw [hS words (v + 1) hv hvh, hS words' (v + 1) hv hvh]
      simp only [Nat.add_sub_cancel]
      rw [List.toFinset_filter, List.toFinset_filter, ih (by omega)]
      have := F.levels2
      rw [show (carryOf g.cfg g.shapes tr words g.cfg.levels (v + 1)).records.toFinset =
          (carryOf g.cfg g.shapes tr words' g.cfg.levels (v + 1)).records.toFinset from
        low_recsFor g F hT words words' (g.cfg.levels - 1) (by omega) (by omega) _]
    · rw [hI words (v + 1) (by omega), hI words' (v + 1) (by omega)]

/-- Every key of a top table lies below `N`, at every top ordinal. -/
theorem top_below_length (F : LowFacts g.cfg g.rows g.direct) (G : TopFacts g) (hT : TracePremises g.cfg N tr) (hInit : tr.init.length ≤ g.init.C / 2 * g.init.T)
    (words : Words) :
    ∀ v, ∀ x ∈ (table g.cfg g.shapes tr words g.cfg.levels v).records, x.key.toNat < N := by
  intro v
  induction v with
  | zero =>
    exact (top_base_outFor_of_initLength g G hT hInit words (Nat.zero_le _)).1.below
  | succ v ih =>
    by_cases hv : g.cfg.seed g.cfg.levels < v + 1
    · rw [top_table_eqFor g F words hv]
      apply topReference_P (P := fun x => x.key.toNat < N)
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · rw [finishInputsAt_eqFor g, fin_aAll] at h
        refine tpReference_P (P := fun x => x.key.toNat < N) _ _ _ _ ?_ x h
        intro y hy
        rw [prep_aAll, Nat.add_sub_cancel] at hy
        exact ih y hy
      · rw [finishInputsAt_eqFor g, fin_bAll] at h
        have hL2 := F.levels2
        exact low_belowFor g F hT words (by omega) (by omega) _ x h
    · exact (top_base_outFor_of_initLength g G hT hInit words (by omega)).1.below

end

/-- Top preparation reads only the previous top's completed trace prefix. -/
theorem prep_prefix (cfg : Config) (sh : Shapes) (tr tr' : Trace) (words : Words)
    (ordinal : Nat) (hi : tr.init = tr'.init) (hu : tr.unsh = tr'.unsh)
    (hunits : ∀ i, cfg.seed 1 + i + 1 ≤ time cfg cfg.levels (ordinal - 1) →
      tr.units i = tr'.units i) :
    prepInputsAt cfg sh tr words ordinal = prepInputsAt cfg sh tr' words ordinal := by
  unfold prepInputsAt
  exact congrArg prepInputs ((TracePrefix cfg sh tr tr' words
    (time cfg cfg.levels (ordinal - 1)) hi hu hunits).1 cfg.levels (ordinal - 1) le_rfl)

/-- Shape of the complete old population, without a capacity-sized key range. -/
theorem prep_shape (geo : HierarchyGeometry) (hgeo : geo.Structural) (tr : Trace)
    (hT : TraceStructural geo.cfg tr)
    (hInit : tr.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hU : UnshPromise geo.cfg geo.shapes tr) (words : Words) (ordinal : Nat)
    (ho : geo.cfg.seed geo.cfg.levels < ordinal)
    (hoh : ordinal ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels) :
    TPShape geo.prep (prepPos geo.cfg geo.shapes words ordinal)
      (prepInputsAt geo.cfg geo.shapes tr words ordinal) := by
  have F := HierarchySemanticsProof.lower hgeo.1
  have G := TopFacts.of_compatible hgeo.2
  obtain ⟨N, hTr⟩ := truncate_premises hT (horizonUnits geo.cfg)
  have hU' := truncate_unsh F tr hU
  have ht := truncate_table F tr words geo.cfg.levels (by have := F.levels2; omega)
    le_rfl (ordinal - 1) (horizonUnits geo.cfg)
    (unitEnd_mono geo.cfg _ (show ordinal - 1 ≤ _ by omega))
  unfold prepInputsAt
  rw [ht]
  exact prep_shapeFor geo.top geo.prep G.prepC G.prepT
    (top_inv'For_of_initLength geo F G hTr hInit hU' words (by omega) (by omega))

/-- A preparation's complete key set is independent of routing words. -/
theorem prep_keys_words (geo : HierarchyGeometry) (hgeo : geo.Structural) (tr : Trace)
    (hT : TraceStructural geo.cfg tr)
    (hInit : tr.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hU : UnshPromise geo.cfg geo.shapes tr) (words words' : Words) (ordinal : Nat)
    (hoh : ordinal ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels) :
    ((prepInputsAt geo.cfg geo.shapes tr words ordinal).aAll.map Rec.key).toFinset =
      ((prepInputsAt geo.cfg geo.shapes tr words' ordinal).aAll.map Rec.key).toFinset := by
  have F := HierarchySemanticsProof.lower hgeo.1
  have G := TopFacts.of_compatible hgeo.2
  obtain ⟨N, hTr⟩ := truncate_premises hT (horizonUnits geo.cfg)
  have hU' := truncate_unsh F tr hU
  have ht := fun ws => truncate_table F tr ws geo.cfg.levels
    (by have := F.levels2; omega) le_rfl (ordinal - 1) (horizonUnits geo.cfg)
    (unitEnd_mono geo.cfg _ (show ordinal - 1 ≤ _ by omega))
  simp only [prepInputsAt, prep_aAll, toFinset_map', ht]
  rw [top_recs_length geo F G hTr hInit hU' words words' (ordinal - 1) (by omega)]

/-- Every record in the finite trace's top or lower tables has a source key. -/
theorem table_below_length (geo : HierarchyGeometry) (hgeo : geo.Structural)
    {N : Nat} {tr : Trace} (hT : TracePremises geo.cfg N tr)
    (hInit : tr.init.length ≤ geo.init.C / 2 * geo.init.T) (words : Words)
    (level ordinal : Nat) (h1 : 1 ≤ level) (hL : level ≤ geo.cfg.levels) :
    ∀ r ∈ (table geo.cfg geo.shapes tr words level ordinal).records, r.key.toNat < N := by
  have F := HierarchySemanticsProof.lower hgeo.1
  by_cases hl : level = geo.cfg.levels
  · subst level
    exact top_below_length geo F (TopFacts.of_compatible hgeo.2) hT hInit words ordinal
  · exact low_belowFor geo F hT words h1 (by omega) ordinal

/-- All direct word reads of a finite trace stay within its source-key bound. -/
theorem jobKeys_below_length (geo : HierarchyGeometry) (hgeo : geo.Structural)
    {N : Nat} {tr : Trace} (hT : TracePremises geo.cfg N tr)
    (hInit : tr.init.length ≤ geo.init.C / 2 * geo.init.T) (words : Words)
    (level ordinal : Nat) (h1 : 1 ≤ level) (hL : level ≤ geo.cfg.levels) :
    ∀ key ∈ jobKeys geo.cfg geo.shapes tr words level ordinal, key.toNat < N := by
  intro key hk
  simp only [jobKeys, List.mem_append, List.mem_map] at hk
  rcases hk with (((⟨r, hr, rfl⟩ | hk) | ⟨r, hr, rfl⟩) | hk) | hk
  · exact table_below_length geo hgeo hT hInit words level (ordinal - 1) h1 hL r hr
  · split_ifs at hk with hl
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
      exact hT.keys _ r hr
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
      exact table_below_length geo hgeo hT hInit words (level - 1)
        (ordinal * geo.cfg.fanout (level - 1)) (by omega) (by omega) r hr
  · exact table_below_length geo hgeo hT hInit words level ordinal h1 hL r hr
  · split_ifs at hk with hl
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
      exact tpReference_P (P := fun r => r.key.toNat < N) geo.prep
        (jobWord geo.cfg words geo.cfg.levels ordinal) tr.unsh
        (prepInputs (table geo.cfg geo.shapes tr words level (ordinal - 1)))
        (fun r hr => table_below_length geo hgeo hT hInit words level
          (ordinal - 1) h1 hL r hr) r hr
    · simp at hk
  · split_ifs at hk
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
      exact hT.initKeys r hr
    · simp at hk

/-- A dependency cone never increases its level. -/
theorem cone_level_le (cfg : Config) :
    ∀ level ordinal, level ≤ cfg.levels → ∀ q ∈ cone cfg level ordinal, q.1 ≤ cfg.levels := by
  intro level
  induction level using Nat.strong_induction_on with
  | _ level ihlevel =>
  intro ordinal
  induction ordinal using Nat.strong_induction_on with
  | _ ordinal ihordinal =>
  intro hL q hq
  rw [cone] at hq
  split_ifs at hq with hb hl h1
  · simpa using List.mem_singleton.mp hq ▸ (show cfg.levels ≤ cfg.levels from le_rfl)
  · simp at hq
  · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | hq
    · exact hL
    · exact ihordinal (ordinal - 1) (by omega) hL q hq
  · simp only [List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · exact hL
    · exact ihordinal (ordinal - 1) (by omega) hL q hq
    · exact ihlevel (level - 1) (by omega) _ (by omega) q hq

/-- The previous top is unchanged when the fresh current family is replaced;
other families need agree only on a finite source-key restriction. -/
theorem previous_congr (geo : HierarchyGeometry) (hgeo : geo.Structural)
    {N : Nat} {tr : Trace} (hT : TracePremises geo.cfg N tr)
    (hInit : tr.init.length ≤ geo.init.C / 2 * geo.init.T) (w w' : Words)
    (ordinal : Nat) (ho : geo.cfg.seed geo.cfg.levels < ordinal)
    (hw : ∀ family, family ≠ (geo.cfg.levels, ordinal) →
      ∀ key, key.toNat < N → w family.1 family.2 key = w' family.1 family.2 key) :
    table geo.cfg geo.shapes tr w geo.cfg.levels (ordinal - 1) =
      table geo.cfg geo.shapes tr w' geo.cfg.levels (ordinal - 1) := by
  have hf := IdealExposureProof.timeFacts (IdealExposureGeometry geo hgeo)
  have h1 : 1 ≤ geo.cfg.levels := by simp [Config.levels]
  apply HierarchyLocalityProof.table_congr
  intro q hq key hk
  have hqt := cone_time geo.cfg hf geo.cfg.levels (ordinal - 1) h1 le_rfl (by omega) q hq
  have hne := family_ne geo.cfg hf geo.cfg.levels ordinal h1 le_rfl ho q hq
  rw [HierarchyTopLawProof.familyOf_top] at hne
  exact hw (familyOf geo.cfg q.1 q.2) hne key
    (jobKeys_below_length geo hgeo hT hInit w q.1 q.2 hqt.1
      (cone_level_le geo.cfg geo.cfg.levels (ordinal - 1) le_rfl q hq) key hk)

end RebuildBound.IdealTopPrepProof
