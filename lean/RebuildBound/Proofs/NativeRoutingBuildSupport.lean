import RebuildBound.Spec.NativeRouting.BuildSupport
import RebuildBound.Proofs.NativeRoutingLocalTable
import RebuildBound.Proofs.NativeMatchExactCounts
import RebuildBound.Proofs.NativeRoutingFamilyExposure

/-! Completed construction support retains old-home reads and counts distinct
keys once per terminal family, even when a table is reconstructed repeatedly.
All bounds use logical reference records, including overflow continuations. -/
namespace RebuildBound.NativeRoutingBuildSupportProof
open Model Model.Hierarchy Model.Online Spec NativeMatchProduction NativeMatchExactCounts
open NativeRoutingActual NativeRoutingLocalTable NativeRoutingBuildSupport
open NativeMatchProductionProof NativeMatchExactCountsProof
open HierarchyInvariantProof OnlineFreshProof NativeRoutingLocalTableProof

lemma mem_completed (cfg : Config) (q : Nat) (c : Nat × Nat) :
    c ∈ completedCoordinates cfg q ↔ 1 ≤ c.1 ∧ c.1 ≤ cfg.levels ∧
      cfg.seed c.1 ≤ c.2 ∧ c.2 ≤ cfg.seed c.1 + q / cfg.carryPositions c.1 := by
  simp only [completedCoordinates, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨level, hl, ordinal, ho, rfl⟩
    exact ⟨hl.1, hl.2, ho.1, ho.2⟩
  · rintro ⟨h1, hL, hs, ho⟩
    exact ⟨c.1, ⟨h1, hL⟩, c.2, ⟨hs, ho⟩, rfl⟩

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

lemma endpoint (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (c : Nat × Nat) (hc : c ∈ completedCoordinates ctx.geo.cfg ctx.accesses) :
    c.2 * ctx.geo.cfg.carryPositions c.1 ≤ pos ctx.geo.cfg ctx.accesses := by
  obtain ⟨h1, hL, hs, ho⟩ := (mem_completed _ _ _).mp hc
  have F := HierarchySemanticsProof.lower (structural ctx hm).1
  have hb := Nat.mul_le_mul_right (ctx.geo.cfg.carryPositions c.1) ho
  rw [Nat.add_mul, seed_cp F c.1 h1 hL] at hb
  exact hb.trans (Nat.add_le_add_left (Nat.div_mul_le_self _ _) _)

lemma completed_of_endpoint (ctx : Context member initialized h)
    (hm : member ∈ ConfigurationFamily.members) (level ordinal : Nat)
    (h1 : 1 ≤ level) (hL : level ≤ ctx.geo.cfg.levels) (hs : ctx.geo.cfg.seed level ≤ ordinal)
    (he : ordinal * ctx.geo.cfg.carryPositions level ≤ pos ctx.geo.cfg ctx.accesses) :
    (level, ordinal) ∈ completedCoordinates ctx.geo.cfg ctx.accesses := by
  have F := HierarchySemanticsProof.lower (structural ctx hm).1
  have hc := cp_pos F h1 hL
  have hseed := seed_cp F level h1 hL
  have hd : (ordinal - ctx.geo.cfg.seed level) * ctx.geo.cfg.carryPositions level ≤ ctx.accesses := by
    rw [Nat.sub_mul, hseed]
    exact Nat.sub_le_of_le_add (by simpa only [pos, Nat.add_comm] using he)
  have hd' := (Nat.le_div_iff_mul_le hc).mpr hd
  exact (mem_completed _ _ _).mpr ⟨h1, hL, hs, by change ordinal ≤ ctx.geo.cfg.seed level + ctx.accesses / ctx.geo.cfg.carryPositions level; omega⟩

lemma family_completed (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (c : Nat × Nat) (hc : c ∈ completedCoordinates ctx.geo.cfg ctx.accesses) :
    familyOf ctx.geo.cfg c.1 c.2 ∈ completedCoordinates ctx.geo.cfg ctx.accesses := by
  obtain ⟨h1, hL, hs, _⟩ := (mem_completed _ _ _).mp hc
  have F := HierarchySemanticsProof.lower (structural ctx hm).1
  obtain ⟨hf1, hfL, hfs, hend⟩ := familyOfAux_inv F ctx.geo.cfg.levels c.1 c.2 h1 hL hs
  apply completed_of_endpoint ctx hm _ _ hf1 hfL hfs
  exact hend.trans_le (endpoint ctx hm c hc)

lemma family_card (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (family : IdealKey.Family) :
    (familyCoordinates ctx.geo.cfg ctx.accesses family).card ≤ ctx.geo.cfg.levels := by
  classical
  have F := HierarchySemanticsProof.lower (structural ctx hm).1
  have hi : Set.InjOn Prod.fst (↑(familyCoordinates ctx.geo.cfg ctx.accesses family) : Set (Nat × Nat)) := by
    intro a ha b hb hab
    obtain ⟨ha, hfa⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hfb⟩ := Finset.mem_filter.mp hb
    obtain ⟨ha1, haL, has, _⟩ := (mem_completed _ _ _).mp ha
    obtain ⟨hb1, hbL, hbs, _⟩ := (mem_completed _ _ _).mp hb
    have ea := familyOf_end F ha1 haL has
    have eb := familyOf_end F hb1 hbL hbs
    rw [hfa] at ea
    rw [hfb, ← hab] at eb
    have ho := Nat.eq_of_mul_eq_mul_right (cp_pos F ha1 haL) (ea.symm.trans eb)
    exact Prod.ext hab ho
  have hs : (familyCoordinates ctx.geo.cfg ctx.accesses family).image Prod.fst ⊆
      Finset.Icc 1 ctx.geo.cfg.levels := by
    intro level hl
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hl
    have hm' := (mem_completed _ _ _).mp (Finset.mem_filter.mp hc).1
    exact Finset.mem_Icc.mpr ⟨hm'.1, hm'.2.1⟩
  have hb := Finset.card_le_card hs
  rw [Finset.card_image_of_injOn hi] at hb
  simpa using hb

lemma completed_horizon (ctx : Context member initialized h) (hv : ctx.Valid)
    (level ordinal : Nat) (ho : ordinal ≤ ctx.geo.cfg.seed level +
      ctx.accesses / ctx.geo.cfg.carryPositions level) :
    ordinal ≤ ctx.geo.cfg.seed level + ctx.geo.cfg.ordinals level := by
  have hd := Nat.div_le_div_right hv.2.1 (c := ctx.geo.cfg.carryPositions level)
  unfold Config.ordinals
  omega

lemma carry_completed (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (level ordinal : Nat) (hc : (level, ordinal) ∈ completedCoordinates ctx.geo.cfg ctx.accesses)
    (hlevel : 1 < level) :
    (level - 1, ordinal * ctx.geo.cfg.fanout (level - 1)) ∈
      completedCoordinates ctx.geo.cfg ctx.accesses := by
  obtain ⟨h1, hL, hs, _⟩ := (mem_completed _ _ _).mp hc
  have F := HierarchySemanticsProof.lower (structural ctx hm).1
  have hseed := F.seed (level - 1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at hseed
  apply completed_of_endpoint ctx hm _ _ (by omega) (by omega)
  · rw [hseed, Nat.mul_comm]
    exact Nat.mul_le_mul_right _ hs
  · have hp := cp_succ F (by omega : 1 ≤ level - 1) (by omega : level - 1 < ctx.geo.cfg.levels)
    rw [Nat.sub_add_cancel (by omega)] at hp
    rw [Nat.mul_assoc, ← hp]
    exact endpoint ctx hm _ hc

lemma coordinate_count (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) (level ordinal : Nat)
    (hc : (level, ordinal) ∈ completedCoordinates ctx.geo.cfg ctx.accesses) :
    (coordinateKeys ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape))
      (IdealHierarchy.words tape) level ordinal).length ≤ coordinateAllowance member := by
  obtain ⟨h1, hL, hs, ho⟩ := (mem_completed _ _ _).mp hc
  have hcurrent := table_count ctx hm hv tape level ordinal h1 hL (completed_horizon ctx hv _ _ ho)
  have hprevious := table_count ctx hm hv tape level (ordinal - 1) h1 hL
    (completed_horizon ctx hv _ _ ((Nat.sub_le ordinal 1).trans ho))
  have hinp : (if level = 1 then
      (DirectMasks.records ((OnlineBatch.traceOf ctx.unit (ctx.run tape)).units
        (ordinal - ctx.geo.cfg.seed 1 - 1))).map Rec.key
      else (carryOf ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape))
        (IdealHierarchy.words tape) level ordinal).records.map Rec.key).length ≤
      maxRecords member + 64 * member.r0 := by
    split_ifs with hl
    · obtain ⟨requests, hcontract, _⟩ := contracts ctx hm hv tape
      obtain ⟨N, _, hT⟩ := ApiStructuralProof.run_premises ctx.geo.cfg ctx.unit (ctx.run tape)
        (alignment member hm initialized h) (by change 0 < 64; decide) hcontract.1.initNodup
      have hu := hT.load (ordinal - ctx.geo.cfg.seed 1 - 1)
      have hunit : ctx.geo.cfg.load * ctx.geo.cfg.carry1 = 64 * member.r0 :=
        by
          simpa only [Context.geo, Config.carryPositions, Config.carry, Nat.sub_self, List.take_zero,
            List.foldr_nil, Nat.mul_one] using (alignment member hm initialized h).symm
      rw [hunit] at hu
      simpa only [List.length_map] using hu.trans (Nat.le_add_left _ _)
    · have hcarry := carry_completed ctx hm level ordinal hc (by omega)
      obtain ⟨hc1, hcL, _, hco⟩ := (mem_completed _ _ _).mp hcarry
      have hb := table_count ctx hm hv tape (level - 1)
        (ordinal * ctx.geo.cfg.fanout (level - 1)) hc1 hcL (completed_horizon ctx hv _ _ hco)
      exact (by simpa only [List.length_map, carryOf] using hb.trans (Nat.le_add_right _ _))
  have hinit : (OnlineBatch.traceOf ctx.unit (ctx.run tape)).init.length ≤
      (member.geometry false).keyCapacity := hv.1.2.1
  unfold coordinateKeys coordinateAllowance
  split_ifs <;> simp_all only [List.length_append, List.length_map, List.length_nil, ite_true, ite_false] <;> omega

lemma keys_bound (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) (family : IdealKey.Family) :
    (buildKeys ctx tape family).card ≤ buildAllowance member := by
  classical
  apply le_trans (Finset.card_biUnion_le_card_mul _ _ (coordinateAllowance member) ?_)
  · exact Nat.mul_le_mul_right _ (family_card ctx hm family)
  · intro c hc
    exact (List.toFinset_card_le _).trans
      (coordinate_count ctx hm hv tape c.1 c.2 (Finset.mem_filter.mp hc).1)

lemma ordinal_bound (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (level : Nat) (_h1 : 1 ≤ level) (_hL : level ≤ ctx.geo.cfg.levels) :
    buildOrdinals ctx.geo.cfg ctx.accesses level ⊆ Finset.Icc (ctx.geo.cfg.seed level)
      (ctx.geo.cfg.seed level + ctx.accesses / ctx.geo.cfg.carryPositions level) ∧
    (buildOrdinals ctx.geo.cfg ctx.accesses level).card ≤
      1 + ctx.accesses / ctx.geo.cfg.carryPositions level := by
  classical
  have hs : buildOrdinals ctx.geo.cfg ctx.accesses level ⊆ Finset.Icc (ctx.geo.cfg.seed level)
      (ctx.geo.cfg.seed level + ctx.accesses / ctx.geo.cfg.carryPositions level) := by
    intro ordinal ho
    obtain ⟨family, hf, ho⟩ := (Finset.mem_filterMap _).mp ho
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hf
    split_ifs at ho with hl
    · have he := Option.some.inj ho
      have hb := (mem_completed _ _ _).mp (family_completed ctx hm c hc)
      rw [hl, he] at hb
      exact Finset.mem_Icc.mpr hb.2.2
  refine ⟨hs, ?_⟩
  have hc := Finset.card_le_card hs
  simpa only [Nat.card_Icc, Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_comm 1] using hc

lemma key_mem (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (level ordinal : Nat) (hc : (level, ordinal) ∈ completedCoordinates ctx.geo.cfg ctx.accesses)
    (key : LogicalKey) (hk : key ∈ coordinateKeys ctx.geo.cfg ctx.geo.shapes
      (OnlineBatch.traceOf ctx.unit (ctx.run tape)) (IdealHierarchy.words tape) level ordinal) :
    key ∈ buildKeys ctx tape (familyOf ctx.geo.cfg level ordinal) := by
  classical
  exact Finset.mem_biUnion.mpr ⟨(level, ordinal), Finset.mem_filter.mpr ⟨hc, rfl⟩,
    List.mem_toFinset.mpr hk⟩

lemma own_key (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)
    (level ordinal : Nat) (record : Rec) (hr : record ∈ (table cfg sh tr words level ordinal).records) :
    record.key ∈ coordinateKeys cfg sh tr words level ordinal :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨record, hr, rfl⟩))

lemma input_key (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)
    (level ordinal : Nat) (ha : cfg.seed level < ordinal) (key : LogicalKey)
    (hk : key ∈ (table cfg sh tr words level (ordinal - 1)).records.map Rec.key ++
      (if level = 1 then (DirectMasks.records (tr.units (ordinal - cfg.seed 1 - 1))).map Rec.key
        else (carryOf cfg sh tr words level ordinal).records.map Rec.key)) :
    key ∈ coordinateKeys cfg sh tr words level ordinal := by
  apply List.mem_append_left
  apply List.mem_append_left
  simpa only [ite_eq_left ha] using hk

lemma reads_bind {Q α β : Type} (tape : Q → Word64) (tree : ReadTree Q α)
    (next : α → ReadTree Q β) :
    ReadTree.reads tape (bind tree next) = ReadTree.reads tape tree ++
      ReadTree.reads tape (next (ReadTree.evaluate tape tree)) := by
  induction tree with
  | done result => rfl
  | read query resume ih =>
    simpa only [NativeRoutingLocalTable.bind, ReadTree.reads, ReadTree.evaluate, List.cons_append] using
      congrArg (List.cons (query, tape query)) (ih (tape query))

lemma base_reads (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (tape : IdealKey.Tape) (level : Nat) (read : IdealKey.Coord × Word64)
    (hr : read ∈ ReadTree.reads tape
      (baseProgram ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape)) level)) :
    ∃ family key, read.1 = Sum.inl (family, key) ∧ key ∈ buildKeys ctx tape family := by
  have hq := List.mem_map_of_mem (f := Prod.fst) hr
  rw [baseProgram, NativeRoutingLocalTableProof.gather_reads] at hq
  by_cases hb : level = ctx.geo.cfg.levels ∧ ctx.geo.cfg.initialized = true
  · simp only [ite_eq_left hb, recordQueries, List.mem_map] at hq
    obtain ⟨record, hr, he⟩ := hq
    refine ⟨familyOf ctx.geo.cfg ctx.geo.cfg.levels (ctx.geo.cfg.seed ctx.geo.cfg.levels),
      record.key, he.symm, ?_⟩
    have F := HierarchySemanticsProof.lower (structural ctx hm).1
    apply key_mem ctx tape ctx.geo.cfg.levels (ctx.geo.cfg.seed ctx.geo.cfg.levels)
    · exact (mem_completed _ _ _).mpr ⟨by have := F.levels2; omega, le_rfl, le_rfl,
        Nat.le_add_right _ _⟩
    · apply List.mem_append_right
      simp only [hb.2, and_self, ite_true]
      exact List.mem_map.mpr ⟨record, hr, rfl⟩
  · simp only [ite_eq_right hb, List.not_mem_nil] at hq

lemma step_queries_covered (ctx : Context member initialized h) (_hm : member ∈ ConfigurationFamily.members)
    (tape : IdealKey.Tape) (level ordinal : Nat)
    (hc : (level, ordinal) ∈ completedCoordinates ctx.geo.cfg ctx.accesses)
    (ha : ctx.geo.cfg.seed level < ordinal) (query : IdealKey.Coord)
    (hq : query ∈ stepQueries ctx.geo.cfg (OnlineBatch.traceOf ctx.unit (ctx.run tape)) level ordinal
      (table ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape))
        (IdealHierarchy.words tape) level (ordinal - 1))
      (if level = 1 then DirectJob.emptyOutput else
        carryOf ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape))
          (IdealHierarchy.words tape) level ordinal)) :
    ∃ family key, query = Sum.inl (family, key) ∧ key ∈ buildKeys ctx tape family := by
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨record, hr, rfl⟩ := List.mem_map.mp hq
    refine ⟨familyOf ctx.geo.cfg level ordinal, record.key, rfl, ?_⟩
    apply key_mem ctx tape level ordinal hc
    apply input_key _ _ _ _ _ _ ha
    by_cases hl : level = 1
    · simp only [ite_eq_left hl, DirectJob.emptyOutput, Output.records, List.flatMap_nil,
        Bucket.recs, List.filterMap_nil, List.append_nil, List.mem_append] at hr
      simp only [ite_eq_left hl, List.mem_append, List.mem_map]
      rcases hr with hr | hr
      · exact Or.inl ⟨record, List.mem_append.mpr hr, rfl⟩
      · exact Or.inr ⟨record, hr, rfl⟩
    · simp only [ite_eq_right hl, List.append_nil, List.mem_append] at hr
      simp only [ite_eq_right hl, List.mem_append, List.mem_map]
      rcases hr with hr | hr
      · exact Or.inl ⟨record, hr, rfl⟩
      · exact Or.inr ⟨record, hr, rfl⟩
  · by_cases hl : level = 1 ∧ level ≠ ctx.geo.cfg.levels
    · simp only [ite_eq_left hl, recordQueries, List.mem_map] at hq
      obtain ⟨record, hr, rfl⟩ := hq
      refine ⟨familyOf ctx.geo.cfg 1 (ordinal - 1), record.key, rfl, ?_⟩
      obtain ⟨h1, hL, hs, ho⟩ := (mem_completed _ _ _).mp hc
      have hp : (1, ordinal - 1) ∈ completedCoordinates ctx.geo.cfg ctx.accesses := by
        apply (mem_completed _ _ _).mpr
        simp only [hl.1] at hL ha ho ⊢
        exact ⟨le_rfl, hL, by omega, (Nat.sub_le ordinal 1).trans ho⟩
      apply key_mem ctx tape 1 (ordinal - 1) hp
      apply own_key
      apply List.mem_append_left
      simpa only [hl.1] using hr
    · simp only [ite_eq_right hl, List.not_mem_nil] at hq

lemma table_reads (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (tape : IdealKey.Tape) :
    ∀ level ordinal, 1 ≤ level → level ≤ ctx.geo.cfg.levels →
      ordinal ≤ ctx.geo.cfg.seed level + ctx.accesses / ctx.geo.cfg.carryPositions level →
      ∀ read ∈ ReadTree.reads tape
        (tableProgram ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape))
          level ordinal),
        ∃ family key, read.1 = Sum.inl (family, key) ∧ key ∈ buildKeys ctx tape family := by
  intro level
  induction level using Nat.strong_induction_on with
  | _ level ihLevel =>
    intro ordinal
    induction ordinal using Nat.strong_induction_on with
    | _ ordinal ihOrdinal =>
      intro h1 hL ho read hr
      rw [tableProgram] at hr
      by_cases hb : level = 0 ∨ ctx.geo.cfg.levels < level ∨ ordinal ≤ ctx.geo.cfg.seed level
      · simp only [ite_eq_left hb] at hr
        exact base_reads ctx hm tape level read hr
      · simp only [ite_eq_right hb, reads_bind, List.mem_append] at hr
        rcases hr with hr | hr
        · exact ihOrdinal (ordinal - 1) (by omega) h1 hL ((Nat.sub_le ordinal 1).trans ho) read hr
        · rw [table_evaluate] at hr
          rcases hr with hr | hr
          · by_cases hl : level = 1
            · simp only [ite_eq_left hl, ReadTree.reads, List.not_mem_nil] at hr
            · have hc := carry_completed ctx hm level ordinal
                ((mem_completed _ _ _).mpr ⟨h1, hL, by change ctx.geo.cfg.seed level ≤ ordinal; omega, ho⟩) (by omega)
              obtain ⟨hc1, hcL, _, hco⟩ := (mem_completed _ _ _).mp hc
              simp only [ite_eq_right hl] at hr
              exact ihLevel (level - 1) (by omega) _ hc1 hcL hco read hr
          · have he : ReadTree.evaluate tape
                (if level = 1 then ReadTree.done DirectJob.emptyOutput else
                  tableProgram ctx.geo.cfg ctx.geo.shapes
                    (OnlineBatch.traceOf ctx.unit (ctx.run tape)) (level - 1)
                    (ordinal * ctx.geo.cfg.fanout (level - 1))) =
                (if level = 1 then DirectJob.emptyOutput else
                  carryOf ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape))
                    (IdealHierarchy.words tape) level ordinal) := by
                split_ifs <;> first | rfl | exact table_evaluate _ _ _ _ _ _
            rw [he] at hr
            have hq := List.mem_map_of_mem (f := Prod.fst) hr
            rw [NativeRoutingLocalTableStepReads] at hq
            exact step_queries_covered ctx hm tape level ordinal
              ((mem_completed _ _ _).mpr ⟨h1, hL, by change ctx.geo.cfg.seed level ≤ ordinal; omega, ho⟩) (by omega) read.1 hq

end RebuildBound.NativeRoutingBuildSupportProof

namespace RebuildBound
open NativeRoutingBuildSupportProof

theorem NativeRoutingBuildFamilyCoordinates : Spec.NativeRoutingBuildFamilyCoordinates_statement := by
  intro member initialized h
  exact family_card

theorem NativeRoutingBuildKeysBound : Spec.NativeRoutingBuildKeysBound_statement := by
  intro member initialized h
  exact keys_bound

theorem NativeRoutingBuildOrdinalsBound : Spec.NativeRoutingBuildOrdinalsBound_statement := by
  intro member initialized h
  exact ordinal_bound

theorem NativeRoutingBuildReadsCovered : Spec.NativeRoutingBuildReadsCovered_statement := by
  intro member initialized h ctx hm _ tape
  exact table_reads ctx hm tape

end RebuildBound
