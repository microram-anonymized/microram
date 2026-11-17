import RebuildBound.Spec.NativeRouting.LocalNative
import RebuildBound.Proofs.NativeRoutingLocalDiagnostics
import RebuildBound.Proofs.NativeMatchHierarchy

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

namespace RebuildBound.NativeRoutingLocalNativeProof
open Model Model.DirectJob Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchHierarchy Spec.NativeRoutingLocalDiagnostics Spec.NativeMatchJobTrace
open NativeMatchHierarchyLayoutProof NativeMatchHierarchyLocalReplay NativeMatchPhysicalInputs
open HierarchyInvariantProof HierarchyCoveringProof


/-- Restrict diagnostics to the predecessor actually reconstructed. -/
lemma previous_subset (cfg : Config) (level ordinal : Nat)
    (hb : ¬(level = 0 ∨ cfg.levels < level ∨ ordinal ≤ cfg.seed level)) :
    invokedJobs cfg level (ordinal-1) ⊆ invokedJobs cfg level ordinal := by
  intro job hj
  rw [invokedJobs, ite_eq_right hb]
  exact List.mem_append_left _ (List.mem_append_left _ hj)

/-- Restrict diagnostics to the carry actually reconstructed. -/
lemma carry_subset (cfg : Config) (level ordinal : Nat)
    (hb : ¬(level = 0 ∨ cfg.levels < level ∨ ordinal ≤ cfg.seed level))
    (h1 : level ≠ 1) :
    invokedJobs cfg (level-1) (ordinal * cfg.fanout (level-1)) ⊆ invokedJobs cfg level ordinal := by
  intro job hj
  rw [invokedJobs, ite_eq_right hb, ite_eq_right h1]
  exact List.mem_append_left _ (List.mem_append_right _ hj)

lemma ordinary_mem (cfg : Config) (level ordinal : Nat)
    (h1 : 1 ≤ level) (hL : level < cfg.levels) (ho : cfg.seed level < ordinal) :
    JobId.ordinary level ordinal ∈ invokedJobs cfg level ordinal := by
  rw [invokedJobs, ite_eq_right (by omega), ite_eq_right (by omega : level ≠ cfg.levels)]
  exact List.mem_append_right _ (by simp)

lemma prep_mem (cfg : Config) (ordinal : Nat) (hL : 0 < cfg.levels)
    (ho : cfg.seed cfg.levels < ordinal) :
    JobId.topPrepare ordinal ∈ invokedJobs cfg cfg.levels ordinal := by
  rw [invokedJobs, ite_eq_right (by omega), ite_eq_left rfl]
  exact List.mem_append_right _ (by simp)

lemma finish_mem (cfg : Config) (ordinal : Nat) (hL : 0 < cfg.levels)
    (ho : cfg.seed cfg.levels < ordinal) :
    JobId.topFinish ordinal ∈ invokedJobs cfg cfg.levels ordinal := by
  rw [invokedJobs, ite_eq_right (by omega), ite_eq_left rfl]
  exact List.mem_append_right _ (by simp)

lemma carry_length_local (geo : HierarchyGeometry)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (tr : Trace) (words : Words) (level ordinal : Nat)
    (h2 : 2 ≤ level) (hL : level ≤ geo.cfg.levels) (ho : geo.cfg.seed level < ordinal)
    (hf : jobFails geo.cfg geo.shapes tr words
      (.ordinary (level-1) (ordinal * geo.cfg.fanout (level-1))) = false) :
    (carryOf geo.cfg geo.shapes tr words level ordinal).tier.length ≤
      incomingCapacity geo.cfg geo.shapes level := by
  have hb := F.fanout_ge (level-1) (by omega) (by omega)
  have hseed := F.seed_succ (level-1) (by omega) (by omega)
  rw [show level-1+1=level by omega] at hseed
  have hlt : geo.cfg.seed (level-1) < ordinal*geo.cfg.fanout (level-1) := by
    rw [hseed]
    exact Nat.mul_lt_mul_of_pos_right ho (by omega)
  have hdig : Config.digitOf (geo.cfg.fanout (level-1)) (ordinal*geo.cfg.fanout (level-1)) =
      geo.cfg.fanout (level-1) := HierarchyCoveringProof.digit_mul (by omega) (by omega)
  unfold carryOf incomingCapacity
  by_cases he : level=2
  · subst level
    simp only [ite_true]
    have h := NativeMatchPhysicalProducers.one_table F tr words hlt hf
    rw [hdig] at h
    exact h
  · simp only [he,ite_false]
    have h := NativeMatchPhysicalProducers.sep_table tr words NativeMatchTierLength.sep_published
      (ℓ:=level-1) (by omega) (by omega) hlt (by rw [hdig]; omega) hf
    rw [hdig] at h
    exact h

lemma carry_safe (geo : HierarchyGeometry)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (tr : Trace) (words : Words) (level ordinal : Nat)
    (h2 : 2 ≤ level) (hL : level ≤ geo.cfg.levels) (ho : geo.cfg.seed level < ordinal)
    (hno : ∀ j ∈ invokedJobs geo.cfg level ordinal, jobFails geo.cfg geo.shapes tr words j = false) :
    jobFails geo.cfg geo.shapes tr words
      (.ordinary (level-1) (ordinal * geo.cfg.fanout (level-1))) = false := by
  apply hno
  apply carry_subset geo.cfg level ordinal (by omega) (by omega)
  apply ordinary_mem geo.cfg _ _ (by omega) (by omega)
  have hseed := F.seed_succ (level-1) (by omega) (by omega)
  rw [show level-1+1=level by omega] at hseed
  rw [hseed]
  exact Nat.mul_lt_mul_of_pos_right ho (by have := F.fanout_ge (level-1) (by omega) (by omega); omega)

lemma direct_length_local (geo : HierarchyGeometry)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (tr : Trace) (words : Words) (ordinal : Nat) (hL : 1 < geo.cfg.levels)
    (ho : geo.cfg.seed 1 < ordinal) (hd2 : 2 ≤ geo.cfg.digitAt 1 ordinal)
    (hlink : (geo.direct (geo.cfg.digitAt 1 ordinal-1)).outputCapacity ≤
      (geo.direct (geo.cfg.digitAt 1 ordinal)).aTierCapacity)
    (hno : ∀ j ∈ invokedJobs geo.cfg 1 ordinal, jobFails geo.cfg geo.shapes tr words j = false) :
    (table geo.cfg geo.shapes tr words 1 (ordinal-1)).tier.length ≤
      (geo.direct (geo.cfg.digitAt 1 ordinal)).aTierCapacity := by
  have hfan := F.fanout_ge 1 hL (by omega)
  have hpred : geo.cfg.seed 1 < ordinal-1 :=
    HierarchyInvariantProof.pred_gt (Nat.dvd_of_mod_eq_zero F.seed_dvd) ho hd2
  have hdprev : Config.digitOf (geo.cfg.fanout 1) (ordinal-1) = geo.cfg.digitAt 1 ordinal-1 :=
    HierarchyInvariantProof.digit_pred (by omega) hd2
  have hf := hno _ (previous_subset geo.cfg 1 ordinal (by omega)
    (ordinary_mem geo.cfg 1 (ordinal-1) (by omega) hL hpred))
  have hprev := NativeMatchPhysicalProducers.one_table F tr words hpred hf
  rw [hdprev] at hprev
  exact hprev.trans hlink

lemma separated_length_local {cfg : Config} {rows : List (SepGeom × Nat)}
    {top : TopGeom} {prep init : TPGeom} {direct : Nat → Geometry}
    (F : FactsFor cfg rows top prep init direct) (tr : Trace) (words : Words) (hS : NativeMatchPhysicalProducers.SepLengthStatement) {ℓ v : Nat}
    (hj : JobId.ordinary ℓ v ∈ cfg.potentialJobs)
    (h2 : 2 ≤ ℓ) (hd : cfg.digitAt ℓ v ≠ 1)
    (hno : ∀ j ∈ invokedJobs cfg ℓ v,
      jobFails cfg (hierarchyShapesWith cfg rows top prep init direct) tr words j = false) :
    (table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words ℓ (v-1)).tier.length ≤
      ((hierarchyShapesWith cfg rows top prep init direct).sep ℓ (cfg.digitAt ℓ v)).aTierPages *
      ((hierarchyShapesWith cfg rows top prep init direct).sep ℓ (cfg.digitAt ℓ v)).C := by
  obtain ⟨h1, hL, h3, h4⟩ := mem_ordinary.1 hj
  simp only [Config.digitAt] at hd ⊢
  have hb := F.fanout_ge ℓ hL (by omega)
  have hd2 : 2 ≤ Config.digitOf (cfg.fanout ℓ) v := by have := HierarchyCoveringProof.digit_pos (cfg.fanout ℓ) v; omega
  have hdle : Config.digitOf (cfg.fanout ℓ) v ≤ cfg.fanout ℓ := HierarchyCoveringProof.digit_le (by omega)
  have hℓL : ℓ ≠ cfg.levels := by omega
  have hℓ1 : ℓ ≠ 1 := by omega
  show ((table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words ℓ (v - 1)).tier).length ≤ _
  by_cases hv : v - 1 ≤ cfg.seed ℓ
  · rw [HierarchyCoveringProof.table_base (Or.inr (Or.inr hv))]
    unfold base
    simp [hℓL, emptyOutput]
  have hdp : Config.digitOf (cfg.fanout ℓ) (v - 1) = Config.digitOf (cfg.fanout ℓ) v - 1 := HierarchyCoveringProof.digit_pred (by omega) hd2
  by_cases hd3 : 3 ≤ Config.digitOf (cfg.fanout ℓ) v
  · have hp : JobId.ordinary ℓ (v - 1) ∈ cfg.potentialJobs := mem_ordinary.2 ⟨h1, hL, by omega, by omega⟩
    have hf := hno _ (previous_subset cfg ℓ v (by omega)
      (ordinary_mem cfg ℓ (v-1) h1 hL (by omega)))
    have := NativeMatchPhysicalProducers.sep_table tr words hS h2 hL (by omega) (by rw [hdp]; omega) hf
    rw [hdp] at this
    exact le_trans this (F.rowA ℓ hL h2 _ (by omega) hd3)
  · have hdeq : Config.digitOf (cfg.fanout ℓ) v = 2 := by omega
    have hd1 : Config.digitOf (cfg.fanout ℓ) (v - 1) = 1 := by rw [hdp]; omega
    have ht : table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words ℓ (v - 1) =
        table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (ℓ - 1) ((v - 1) * cfg.fanout (ℓ - 1)) := by
      rw [HierarchyCoveringProof.table_step (by omega)]
      unfold step
      simp only [hℓL, hℓ1, hd1, ite_false, ite_true]
    rw [ht, hdeq]
    have hb' := F.fanout_ge (ℓ - 1) (by omega) (by omega)
    have hseed := F.seed_succ (ℓ - 1) (by omega) (by omega)
    rw [show ℓ - 1 + 1 = ℓ by omega] at hseed
    have hlt : cfg.seed (ℓ - 1) < (v - 1) * cfg.fanout (ℓ - 1) := by
      rw [hseed]; exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    have hdig : Config.digitOf (cfg.fanout (ℓ - 1)) ((v - 1) * cfg.fanout (ℓ - 1)) =
        cfg.fanout (ℓ - 1) := HierarchyCoveringProof.digit_mul (by omega) (by omega)
    have hf := hno _ (previous_subset cfg ℓ v (by omega)
      (carry_subset cfg ℓ (v-1) (by omega) (by omega)
        (ordinary_mem cfg (ℓ-1) ((v-1)*cfg.fanout (ℓ-1)) (by omega) (by omega) hlt)))
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      have := NativeMatchPhysicalProducers.one_table F tr words hlt hf
      rw [hdig] at this
      exact le_trans this (F.rowOne hL)
    · have := NativeMatchPhysicalProducers.sep_table tr words hS (ℓ := ℓ - 1) (by omega) (by omega) hlt (by rw [hdig]; omega) hf
      rw [hdig] at this
      exact le_trans this (F.rowCarry ℓ hL (by omega))

theorem separated_local (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (classes : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (geo : HierarchyGeometry) (hgeo : geo.Structural)
    {N : Nat} (tr : Trace) (hT : TracePremises geo.cfg N tr) (words : Words)
    (level ordinal : Nat) (hj : JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs)
    (h2 : 2 ≤ level)
    (hd2 : 2 ≤ geo.cfg.digitAt level ordinal)
    (hf : jobFails geo.cfg geo.shapes tr words (.ordinary level ordinal) = false)
    (ha : (table geo.cfg geo.shapes tr words level (ordinal-1)).tier.length ≤
      (geo.shapes.sep level (geo.cfg.digitAt level ordinal)).aTierPages *
        (geo.shapes.sep level (geo.cfg.digitAt level ordinal)).C)
    (hb : (carryOf geo.cfg geo.shapes tr words level ordinal).tier.length ≤
      incomingCapacity geo.cfg geo.shapes level)
    (hlink : incomingCapacity geo.cfg geo.shapes level ≤
      (geo.shapes.sep level (geo.cfg.digitAt level ordinal)).bTierPages *
      (geo.shapes.sep level (geo.cfg.digitAt level ordinal)).C)
    (hoff : ∀ e ∈ NativeMatchHierarchy.jobEvents geo.cfg geo.shapes tr words (.ordinary level ordinal),
      ¬e.bad stored) :
    let g := geo.shapes.sep level (geo.cfg.digitAt level ordinal)
    NativeMatchHierarchy.OutputEq
      (separatedNative stored engineRule g (jobWord geo.cfg words level ordinal)
        (sepInputsAt geo.cfg geo.shapes tr words level ordinal) (engineOps g)
        (bucketPages g.aTierPages (table geo.cfg geo.shapes tr words level (ordinal-1)).tier))
      (sReferenceWith engineRule g (jobWord geo.cfg words level ordinal)
        (sepInputsAt geo.cfg geo.shapes tr words level ordinal) (engineOps g)).output := by
  have LF := HierarchySemanticsProof.lower hgeo.1
  obtain ⟨h1,hL,ho,hov⟩ := mem_ordinary.1 hj
  obtain ⟨g,hg,hgd,hgU,hvalid,hC,hP,he,hprev,hdg,hpred,hcarry⟩ :=
    sep_ctxFor geo LF hT words hj h2 hd2
  have hs : SInputShape g (jobWord geo.cfg words level (ordinal-1))
      (jobWord geo.cfg words level ordinal) (sepInputsAt geo.cfg geo.shapes tr words level ordinal) := by
    rw [sepInputsAt_eqFor geo,hg]
    exact sep_shape_pos hgd hgU hC hP hdg hprev hcarry
  rw [hg,hC] at ha
  have hb := hb.trans hlink
  rw [hg,hC] at hb
  have hraw : pageRecords (bucketPages g.aTierPages
      (table geo.cfg geo.shapes tr words level (ordinal-1)).tier) =
      (sepInputsAt geo.cfg geo.shapes tr words level ordinal).aTier := by
    rw [NativeMatchDenseTraceProof.bucketPages_records,List.take_of_length_le (by simpa only [Nat.mul_comm] using ha)]
    rfl
  have hpages : ∀ page ∈ (sepInputsAt geo.cfg geo.shapes tr words level ordinal).bTier,
      page.length ≤ 64 := by
    change ∀ page ∈ pagesOf _ _ _, page.length ≤ 64
    rw [hg,hC]
    exact pagesOf_fits _ _ _ (by simpa only [Nat.mul_comm] using hb)
  have hn : sFirstFailure (geo.shapes.sep level (geo.cfg.digitAt level ordinal))
      (sReferenceWith engineRule (geo.shapes.sep level (geo.cfg.digitAt level ordinal))
        (jobWord geo.cfg words level ordinal) (sepInputsAt geo.cfg geo.shapes tr words level ordinal)
        (engineOps (geo.shapes.sep level (geo.cfg.digitAt level ordinal)))).trace = none := by
    simp only [jobFails, show level ≠ 1 by omega, show geo.cfg.digitAt level ordinal ≠ 1 by omega,
      ite_false, Bool.not_eq_false'] at hf
    obtain ⟨out, hok⟩ := toBool_ok hf
    unfold sepResult sJob sJobWith at hok
    dsimp only at hok
    split at hok
    · cases hok
    · assumption
  rw [hg] at hn ⊢
  have hoff' : ∀ e ∈ separatedEvents engineRule g (jobWord geo.cfg words level ordinal)
      (sepInputsAt geo.cfg geo.shapes tr words level ordinal) (engineOps g)
      (bucketPages g.aTierPages (table geo.cfg geo.shapes tr words level (ordinal-1)).tier), ¬e.bad stored := by
    simpa only [NativeMatchHierarchy.jobEvents,show level ≠ 1 by omega,
      show geo.cfg.digitAt level ordinal ≠ 1 by omega,ite_false,hg] using hoff
  have hr := (RebuildBound.NativeMatchSeparatedFullJob bridge retained classes stored engineRule g _ _ _ _ _
    D1Lemmas.engine_valid hvalid hC hs (SEngProof.engine_valid g hvalid) hn hraw hpages).1 hoff'
  dsimp only
  rw [hr]
  exact ⟨rfl,padding _ _⟩

set_option maxHeartbeats 1000000 in
theorem top_local (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (classes : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (tr : Trace) (hT : TraceStructural geo.cfg tr)
    (hLen : tr.init.length ≤ geo.init.C/2*geo.init.T) (hUnsh : UnshPromise geo.cfg geo.shapes tr)
    (words : Words) (ordinal : Nat) (hj : JobId.topFinish ordinal ∈ geo.cfg.potentialJobs)
    (hdfs : geo.top.dfs = true)
    (hf : jobFails geo.cfg geo.shapes tr words (.topFinish ordinal) = false)
    (hr : (prepOutput geo.cfg geo.shapes tr words ordinal
      (table geo.cfg geo.shapes tr words geo.cfg.levels (ordinal-1))).tier.length ≤ geo.top.SR)
    (hb : (carryOf geo.cfg geo.shapes tr words geo.cfg.levels ordinal).tier.length ≤ geo.top.SB)
    (hoff : ∀ e ∈ NativeMatchHierarchy.jobEvents geo.cfg geo.shapes tr words (.topFinish ordinal),
      ¬e.bad stored) :
    let prepared := prepOutput geo.cfg geo.shapes tr words ordinal
      (table geo.cfg geo.shapes tr words geo.cfg.levels (ordinal-1))
    let carry := carryOf geo.cfg geo.shapes tr words geo.cfg.levels ordinal
    NativeMatchHierarchy.OutputEq
      (NativeMatchTopJobTrace.native stored geo.top tr.unsh
        (jobWord geo.cfg words geo.cfg.levels ordinal) (finishInputs prepared carry)
        (bucketPages geo.top.rPages prepared.tier) (bucketPages geo.top.bPages carry.tier))
      (topReference geo.top tr.unsh (jobWord geo.cfg words geo.cfg.levels ordinal)
        (finishInputs prepared carry)).output := by
  let prepared := prepOutput geo.cfg geo.shapes tr words ordinal
    (table geo.cfg geo.shapes tr words geo.cfg.levels (ordinal-1))
  let carry := carryOf geo.cfg geo.shapes tr words geo.cfg.levels ordinal
  have G := TopFacts.of_compatible hgeo.2
  obtain ⟨ho,hov⟩ := mem_finish.1 hj
  have hs := (HierarchyStructuralStep geo hgeo tr hT hLen hUnsh words ordinal ho hov).1
  have hlayoutR : pageRecords (bucketPages geo.top.rPages prepared.tier) = (finishInputs prepared carry).carry := by
    rw [NativeMatchDenseTraceProof.bucketPages_records,List.take_of_length_le ?_]
    · rfl
    · simpa only [TopGeom.SR,G.topC,Nat.mul_comm] using hr
  have hlayoutB : pageRecords (bucketPages geo.top.bPages carry.tier) = (finishInputs prepared carry).bTier := by
    rw [NativeMatchDenseTraceProof.bucketPages_records,List.take_of_length_le ?_]
    · rfl
    · simpa only [TopGeom.SB,G.topC,Nat.mul_comm] using hb
  have hn : firstFailure geo.shapes.top.toGeom geo.shapes.top.caps
      (topReference geo.shapes.top tr.unsh (jobWord geo.cfg words geo.cfg.levels ordinal)
        (finishInputsAt geo.cfg geo.shapes tr words ordinal)).trace = none := by
    simp only [jobFails, Bool.not_eq_false'] at hf
    obtain ⟨out, hok⟩ := toBool_ok hf
    unfold finishResult topJob at hok
    dsimp only at hok
    split at hok
    · cases hok
    · assumption
  have he := (RebuildBound.NativeMatchTopFullJob bridge retained classes stored geo.top tr.unsh
    (jobWord geo.cfg words geo.cfg.levels ordinal) (finishInputs prepared carry) _ _
    G.topValid G.topC hs hdfs hn hlayoutR hlayoutB).1 hoff
  dsimp only
  rw [he]
  exact ⟨rfl,padding _ _⟩


theorem direct_local (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (classes : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (tr : Trace) (words : Words) (ordinal : Nat)
    (hj : JobId.ordinary 1 ordinal ∈ geo.cfg.potentialJobs)
    (hwidth : ∀ bucket ∈ tr.units (ordinal-geo.cfg.seed 1-1), bucket.length ≤ 64)
    (hcap : 2 ≤ geo.cfg.digitAt 1 ordinal → (geo.direct (geo.cfg.digitAt 1 ordinal)).bCapacity ≤ 64)
    (hf : jobFails geo.cfg geo.shapes tr words (.ordinary 1 ordinal) = false)
    (hprevLen : 2 ≤ geo.cfg.digitAt 1 ordinal →
      (table geo.cfg geo.shapes tr words 1 (ordinal-1)).tier.length ≤
        (geo.direct (geo.cfg.digitAt 1 ordinal)).aTierCapacity)
    (hoff : ∀ e ∈ jobEvents geo.cfg geo.shapes tr words (.ordinary 1 ordinal), ¬e.bad stored) :
    let d := geo.cfg.digitAt 1 ordinal
    let prev := if d=1 then emptyOutput else table geo.cfg geo.shapes tr words 1 (ordinal-1)
    let units := tr.units (ordinal-geo.cfg.seed 1-1)
    ∃ nativeOut, directNative stored (geo.direct d) (jobWord geo.cfg words 1 ordinal)
        (adopt prev units) prev = some nativeOut ∧
      OutputEq nativeOut (levelOneStep (geo.direct d) (jobWord geo.cfg words 1 (ordinal-1))
        (jobWord geo.cfg words 1 ordinal) prev units) := by
  let d := geo.cfg.digitAt 1 ordinal
  let prev := if d=1 then emptyOutput else table geo.cfg geo.shapes tr words 1 (ordinal-1)
  let units := tr.units (ordinal-geo.cfg.seed 1-1)
  have LF := HierarchySemanticsProof.lower hgeo.1
  obtain ⟨h1,hL,ho,hov⟩ := mem_ordinary.1 hj
  have hfan := F.fanout_ge 1 hL (by omega)
  have hdpos : 1 ≤ d := HierarchyCoveringProof.digit_pos _ _
  have hdle : d ≤ geo.cfg.fanout 1 := HierarchyCoveringProof.digit_le (by omega)
  have hD := (LF.direct d (by omega) hdpos).2.2
  have hpublished : ∃ out, levelOneResult geo.cfg geo.shapes tr words ordinal = .published out := by
    cases he : levelOneResult geo.cfg geo.shapes tr words ordinal with
    | rejected reason => simp [jobFails, he] at hf
    | failed event => simp [jobFails, he] at hf
    | published out => exact ⟨out, rfl⟩
  obtain ⟨out, hpub⟩ := hpublished
  change runJob (geo.direct d) (jobWord geo.cfg words 1 (ordinal-1))
    (jobWord geo.cfg words 1 ordinal) (adopt prev units) = .published out at hpub
  have hprev : 2 ≤ (geo.direct d).digit → prev.tier.length ≤ (geo.direct d).aTierCapacity := by
    intro hd2
    rw [hD] at hd2
    have hdne : d ≠ 1 := by omega
    dsimp only [prev]
    rw [ite_eq_right hdne]
    exact hprevLen hd2
  have hoff' : ∀ e ∈ directEvents (geo.direct d) (jobWord geo.cfg words 1 ordinal) (adopt prev units) prev,
      ¬e.bad stored := hoff
  obtain ⟨nativeOut,hn,he⟩ := NativeMatchHierarchyDirectReplay.published bridge retained classes stored
    (geo.direct d) (jobWord geo.cfg words 1 (ordinal-1)) (jobWord geo.cfg words 1 ordinal)
    prev units out hpub hwidth (by simpa only [hD] using hcap) hprev hoff'
  refine ⟨nativeOut,hn,?_⟩
  change OutputEq nativeOut (levelOneStep (geo.direct d) (jobWord geo.cfg words 1 (ordinal-1))
    (jobWord geo.cfg words 1 ordinal) prev units)
  unfold levelOneStep
  rw [hpub]
  exact he


lemma table_replay_local (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes)
    (tr : Trace) (words : Words) (H : Nat)
    (hcarry : ∀ level ordinal, 2 ≤ level → level ≤ cfg.levels →
      time cfg (level-1) (ordinal*cfg.fanout (level-1)) = time cfg level ordinal)
    (hstep : ∀ level ordinal, 1 ≤ level → level ≤ cfg.levels → cfg.seed level < ordinal →
      time cfg level ordinal ≤ H →
      (∀ j ∈ invokedJobs cfg level ordinal,
        jobFails cfg sh tr words j = false ∧ ∀ e ∈ jobEvents cfg sh tr words j, ¬e.bad stored) →
      let prev := Hierarchy.table cfg sh tr words level (ordinal-1)
      let carry := if level = 1 then emptyOutput else
        Hierarchy.table cfg sh tr words (level-1) (ordinal*cfg.fanout (level-1))
      ∃ out, nativeStep stored cfg sh tr words level ordinal prev carry = some out ∧
        OutputEq out (Hierarchy.step cfg sh tr words level ordinal prev carry))
    (level ordinal : Nat) (hH : time cfg level ordinal ≤ H)
    (hsafe : ∀ j ∈ invokedJobs cfg level ordinal,
      jobFails cfg sh tr words j = false ∧ ∀ e ∈ jobEvents cfg sh tr words j, ¬e.bad stored) :
    ∃ out, nativeTable stored cfg sh tr words level ordinal = some out ∧
      OutputEq out (Hierarchy.table cfg sh tr words level ordinal) := by
  induction level using Nat.strong_induction_on generalizing ordinal with
  | h level ihl =>
    induction ordinal using Nat.strong_induction_on with
    | h ordinal ihv =>
      by_cases hb : level = 0 ∨ cfg.levels < level ∨ ordinal ≤ cfg.seed level
      · refine ⟨base cfg sh tr words level,?_,?_⟩
        · rw [nativeTable,ite_eq_left hb]
        · rw [Hierarchy.table,ite_eq_left hb]
          exact output_refl _
      · have hl1 : 1 ≤ level := by omega
        have hlL : level ≤ cfg.levels := by omega
        have hpred : time cfg level (ordinal-1) ≤ H :=
          (Nat.mul_le_mul_right _ (Nat.sub_le _ _)).trans hH
        obtain ⟨prev,hprev,hprevEq⟩ := ihv (ordinal-1) (by omega) hpred
          (fun j hj => hsafe j (previous_subset cfg level ordinal hb hj))
        obtain ⟨exactOut,hexact,heq⟩ := hstep level ordinal hl1 hlL (by omega) hH hsafe
        by_cases hl : level = 1
        · have hc := step_congr stored cfg sh tr words level ordinal hprevEq
            (output_refl emptyOutput) exactOut (by simpa only [hl,ite_true] using hexact)
          obtain ⟨out,hout,heout⟩ := hc
          refine ⟨out,?_,?_⟩
          · rw [nativeTable,ite_eq_right hb,hprev]
            simp only [hl,ite_true,Option.bind_eq_bind',Option.bind_some]
            simpa only [hl] using hout
          · rw [Hierarchy.table,ite_eq_right hb]
            exact output_trans heout (by simpa only [hl,ite_true] using heq)
        · have hcH : time cfg (level-1) (ordinal*cfg.fanout (level-1)) ≤ H := by
            rw [hcarry level ordinal (by omega) hlL]
            exact hH
          obtain ⟨carry,hcarryOut,hcarryEq⟩ := ihl (level-1) (by omega)
            (ordinal*cfg.fanout (level-1)) hcH
            (fun j hj => hsafe j (carry_subset cfg level ordinal hb hl hj))
          obtain ⟨out,hout,heout⟩ := step_congr stored cfg sh tr words level ordinal hprevEq hcarryEq
            exactOut (by simpa only [hl,ite_false] using hexact)
          refine ⟨out,?_,?_⟩
          · rw [nativeTable,ite_eq_right hb,hprev]
            simp only [hl,ite_false,hcarryOut]
            exact hout
          · rw [Hierarchy.table,ite_eq_right hb]
            exact output_trans heout (by simpa only [hl,ite_false] using heq)


lemma table_agreement_local (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (classes : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    {N : Nat} (tr : Trace) (hT : TracePremises geo.cfg N tr)
    (hLen : tr.init.length ≤ geo.init.C/2*geo.init.T) (hUnsh : UnshPromise geo.cfg geo.shapes tr)
    (hwidth : ∀ i, ∀ bucket ∈ tr.units i, bucket.length ≤ 64)
    (htop : ∀ ordinal, time geo.cfg geo.cfg.levels ordinal ≤ geo.cfg.seed 1+geo.cfg.ordinals 1 →
      ordinal ≤ geo.cfg.seed geo.cfg.levels+geo.cfg.ordinals geo.cfg.levels)
    (hdfs : geo.top.dfs = true)
    (hdirect : ∀ d, 2 ≤ d → d ≤ geo.cfg.fanout 1 →
      (geo.direct d).bCapacity ≤ 64 ∧ (geo.direct (d-1)).outputCapacity ≤ (geo.direct d).aTierCapacity)
    (hsep : ∀ level, 2 ≤ level → level < geo.cfg.levels → ∀ d, 2 ≤ d → d ≤ geo.cfg.fanout level →
      incomingCapacity geo.cfg geo.shapes level ≤
        (geo.shapes.sep level d).bTierPages*(geo.shapes.sep level d).C)
    (words : Words) (level ordinal : Nat)
    (hH : time geo.cfg level ordinal ≤ geo.cfg.seed 1+geo.cfg.ordinals 1)
    (hsafe : ∀ j ∈ invokedJobs geo.cfg level ordinal,
      jobFails geo.cfg geo.shapes tr words j = false ∧
        ∀ e ∈ jobEvents geo.cfg geo.shapes tr words j, ¬e.bad stored) :
    ∃ out, nativeTable stored geo.cfg geo.shapes tr words level ordinal = some out ∧
      OutputEq out (table geo.cfg geo.shapes tr words level ordinal) := by
  apply table_replay_local stored geo.cfg geo.shapes tr words (geo.cfg.seed 1+geo.cfg.ordinals 1) ?_ ?_ level ordinal hH hsafe
  · intro l v h2 hL
    have hp := F.per_succ (l-1) (by omega) (by omega)
    rw [show l-1+1=l by omega] at hp
    rw [time_eq,time_eq,hp,Nat.mul_assoc,Nat.mul_comm (geo.cfg.fanout (l-1))]
  · intro l v h1 hL ho hW hsafe
    have hno : ∀ j ∈ invokedJobs geo.cfg l v, jobFails geo.cfg geo.shapes tr words j = false :=
      fun j hj => (hsafe j hj).1
    dsimp only
    by_cases htopL : l = geo.cfg.levels
    · subst l
      have hj : JobId.topFinish v ∈ geo.cfg.potentialJobs := mem_finish.mpr ⟨ho,htop v hW⟩
      have hf := hsafe _ (finish_mem geo.cfg v (by omega) ho)
      have hprep := (NativeMatchPhysicalProducers.prep_out tr words NativeMatchTierLength.tp_published
        (hno _ (prep_mem geo.cfg v (by omega) ho))).trans F.prepTop
      have hcarry := carry_length_local geo F tr words geo.cfg.levels v F.levels_ge le_rfl ho
        (carry_safe geo F tr words geo.cfg.levels v F.levels_ge le_rfl ho hno)
      have hlink : incomingCapacity geo.cfg geo.shapes geo.cfg.levels ≤ geo.top.SB := by
        simpa only [incomingCapacity, HierarchyGeometry.shapes, hierarchyShapesWith] using F.topB
      have he := top_local bridge retained classes stored geo hgeo tr
        ⟨hT.nodup,hT.load,hT.initNodup⟩ hLen hUnsh words v hj hdfs hf.1 hprep
        (hcarry.trans hlink) hf.2
      have hn1 : geo.cfg.levels ≠ 1 := by have := F.levels_ge; omega
      simp only [nativeStep,ite_true]
      refine ⟨_,rfl,?_⟩
      simpa only [Hierarchy.step,ite_true,hn1,ite_false,HierarchyGeometry.shapes,hierarchyShapesWith,carryOf] using he
    · have hj : JobId.ordinary l v ∈ geo.cfg.potentialJobs :=
        NativeMatchPhysicalProducers.ord_potential F h1 (by omega) ho hW
      have hfan := F.fanout_ge l (by omega) h1
      have hdpos : 1 ≤ geo.cfg.digitAt l v := HierarchyCoveringProof.digit_pos _ _
      have hdle : geo.cfg.digitAt l v ≤ geo.cfg.fanout l := HierarchyCoveringProof.digit_le (by omega)
      by_cases hl1 : l=1
      · subst l
        have hf := hsafe _ (ordinary_mem geo.cfg 1 v h1 (by omega) ho)
        obtain ⟨out,hn,he⟩ := direct_local bridge retained classes stored geo hgeo F tr words v hj
          (hwidth _) (fun hd => (hdirect _ hd hdle).1) hf.1
          (fun hd => direct_length_local geo F tr words v (by omega) ho hd
            (hdirect _ hd hdle).2 hno) hf.2
        refine ⟨out,?_,?_⟩
        · simpa only [nativeStep,htopL,ite_false,ite_true,Config.digitAt,HierarchyGeometry.shapes,hierarchyShapesWith] using hn
        · simpa only [Hierarchy.step,htopL,ite_false,ite_true,Config.digitAt,HierarchyGeometry.shapes,hierarchyShapesWith] using he
      · by_cases hd1 : geo.cfg.digitAt l v=1
        · refine ⟨carryOf geo.cfg geo.shapes tr words l v,?_,?_⟩
          · simp only [nativeStep,htopL,hl1,hd1,ite_false,ite_true,Config.digitAt] at *
            rfl
          · simp only [Hierarchy.step,htopL,hl1,ite_false]
            change OutputEq _ (if geo.cfg.digitAt l v=1 then _ else _)
            rw [ite_eq_left hd1]
            exact output_refl _
        · have hd2 : 2 ≤ geo.cfg.digitAt l v := by omega
          have hf := hsafe _ (ordinary_mem geo.cfg l v h1 (by omega) ho)
          have ha := separated_length_local F tr words NativeMatchTierLength.sep_published hj
            (by omega) hd1 hno
          have hb := carry_length_local geo F tr words l v (by omega) hL ho
            (carry_safe geo F tr words l v (by omega) hL ho hno)
          have he := separated_local bridge retained classes stored geo hgeo tr hT words l v hj
            (by omega) hd2 hf.1 ha hb (hsep l (by omega) (by omega) _ hd2 hdle) hf.2
          have hd1' : Config.digitOf (geo.cfg.fanout l) v ≠ 1 := hd1
          simp only [nativeStep,htopL,hl1,hd1',ite_false]
          refine ⟨_,rfl,?_⟩
          simpa only [Hierarchy.step,htopL,hl1,hd1',ite_false,Config.digitAt,sReference,sepInputsAt,carryOf] using he

open ConfigurationFamily Model.Online NativeMatchHierarchyFamilyReplay

lemma family_replay (m : Member) (initialized : Bool) (hm : m ∈ members)
    (h : Nat) (run : OnlineBatch.BatchRun)
    (hready : RunReady m initialized h run) (stored : LogicalKey → Stored) (tape : IdealKey.Tape) :
    let geo := (m.geometry initialized).chunk h
    let tr := OnlineBatch.traceOf ⟨64,m.r0⟩ run
    ∀ level ordinal, time geo.cfg level ordinal ≤ geo.cfg.seed 1+geo.cfg.ordinals 1 →
      (∀ d ∈ (Spec.NativeRoutingActual.ReadTree.evaluate tape
        (tableProgram geo.cfg geo.shapes tr level ordinal)).diagnostics,
          d.failed = false ∧ ∀ e ∈ d.events, ¬e.bad stored) →
      ∃ out, nativeTable stored geo.cfg geo.shapes tr (IdealHierarchy.words tape) level ordinal = some out ∧
        OutputEq out (table geo.cfg geo.shapes tr (IdealHierarchy.words tape) level ordinal) := by
  let geo := (m.geometry initialized).chunk h
  let g : OnlineGeom := ⟨64,m.r0⟩
  let tr := OnlineBatch.traceOf g run
  dsimp only
  intro level ordinal hH hsafe
  have hgeo := ConfigurationFamilyProbabilityProof.structural initialized m hm h
  have F := HierarchyCoveringFromProof.factsFor_chunk
    (ConfigurationFamilyProbabilityProof.coveringFacts initialized m hm)
    (ConfigurationFamilyProbabilityProof.chunkFacts initialized m hm) HierarchyHorizonFree h
  have hlinks : Links m initialized := by
    have H := links m hm
    cases initialized
    · exact H.2
    · exact H.1
  have hshapes : geo.shapes = (m.geometry initialized).shapes := shapes_chunk _ _
  have halign : g.unitEntries*g.unitsPerPrefix = geo.cfg.carryPositions 1 := by
    dsimp only [geo,g,HierarchyGeometry.chunk,chunkConfig,Member.geometry,Member.config,Config.carryPositions,Config.carry]
    simp only [Nat.sub_self,List.take_zero,List.foldr_nil,Nat.mul_one]
    omega
  obtain ⟨N,_,hT⟩ := ApiStructuralProof.run_premises geo.cfg g run halign (by change 0 < 64; decide) hready.1
  have hsafe' : ∀ j ∈ invokedJobs geo.cfg level ordinal,
      jobFails geo.cfg geo.shapes tr (IdealHierarchy.words tape) j = false ∧
        ∀ e ∈ jobEvents geo.cfg geo.shapes tr (IdealHierarchy.words tape) j, ¬e.bad stored := by
    rw [NativeRoutingLocalDiagnosticsEvaluate geo.cfg geo.shapes tr tape F.levels_ge hT.nodup level ordinal] at hsafe
    intro j hj
    exact hsafe _ (List.mem_map.mpr ⟨j, hj, rfl⟩)
  apply table_agreement_local RebuildBound.NativeMatchLanesBridge
    RebuildBound.NativeMatchRetained RebuildBound.NativeMatchClassBridge stored geo hgeo F tr hT
    hready.2.1 hready.2.2 (NativeMatchRequesterLayout.trace_width64 g run rfl) ?_ hlinks.1 ?_ ?_
    (IdealHierarchy.words tape) level ordinal hH hsafe'
  · exact NativeMatchHierarchyReplayProof.top_horizon
      (ConfigurationFamilyProbabilityProof.chunkFacts initialized m hm) h
  · intro d hd2 hdb
    have H := hlinks.2.1 (d-2) (List.mem_range.mpr (by change _ < geo.cfg.fanout 1-1; omega))
    simpa only [geo,HierarchyGeometry.chunk,Member.geometry,show d-2+2=d by omega,show d-2+1=d-1 by omega] using H
  · intro l h2 hL d hd2 hdb
    have H := hlinks.2.2 (l,d) (separated_class_mem (m.config initialized) l d h2 hL hd2 hdb)
    dsimp only at H
    rw [hshapes]
    exact H

end RebuildBound.NativeRoutingLocalNativeProof

namespace RebuildBound
open Spec Model Model.Hierarchy NativeMatchHierarchy NativeRoutingActual

theorem NativeRoutingLocalNativeTable : NativeRoutingLocalNativeTable_statement :=
  NativeRoutingLocalNativeProof.family_replay

theorem NativeRoutingLocalNativeDivergence : NativeRoutingLocalNativeDivergence_statement := by
  classical
  intro member initialized hm h run hready stored tape level ordinal
  dsimp only
  intro hH hbad
  by_contra hsafe
  apply hbad
  apply NativeRoutingLocalNativeTable member initialized hm h run hready stored tape level ordinal hH
  intro d hd
  constructor
  · apply Bool.eq_false_iff.mpr
    exact fun hf => hsafe ⟨d, hd, Or.inl hf⟩
  · intro e he hbad
    exact hsafe ⟨d, hd, Or.inr ⟨e, he, hbad⟩⟩

end RebuildBound
