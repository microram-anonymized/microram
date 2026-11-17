import RebuildBound.Spec.NativeMatch.Hierarchy
import RebuildBound.Proofs.ConfigurationFamilyProbability.Facts
import RebuildBound.Proofs.HierarchyCoveringFrom
import RebuildBound.Proofs.NativeMatchJobs
import RebuildBound.Proofs.DirectMaskIndex
import RebuildBound.Proofs.DirectJobPublication
import RebuildBound.Proofs.TierFit
import RebuildBound.Proofs.HierarchyCovering
import RebuildBound.Proofs.ApiStructural
import RebuildBound.Proofs.HierarchyStructural
import RebuildBound.Proofs.HierarchyInvariant.ContractsFor
import RebuildBound.Proofs.NativeMatchHierarchy.PhysicalInputs
import RebuildBound.Proofs.NativeMatchHierarchy.Direct
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace RebuildBound.NativeMatchHierarchyLayoutProof
open Model Model.Hierarchy Spec Spec.NativeMatchTrace Spec.NativeMatchHierarchy

theorem lane_refl (a : Bucket) : LaneEq a a := fun _ => rfl

theorem lane_symm {a b : Bucket} (h : LaneEq a b) : LaneEq b a := fun i => (h i).symm

theorem lane_trans {a b c : Bucket} (hab : LaneEq a b) (hbc : LaneEq b c) : LaneEq a c :=
  fun i => (hab i).trans (hbc i)

theorem padding (a : Bucket) (n : Nat) : LaneEq (a ++ List.replicate n none) a := by
  intro i
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append,List.getElem?_replicate]
  split
  · rfl
  · rename_i hi
    have he : a[i]? = none := List.getElem?_eq_none (by omega)
    rw [he]
    split <;> rfl

theorem getD_ext {a b : Bucket} (hlen : a.length = b.length) (h : LaneEq a b) : a = b := by
  apply List.ext_getElem hlen
  intro i ha hb
  simpa only [List.getD_eq_getElem _ _ ha,List.getD_eq_getElem _ _ hb] using h i

theorem pad_equal {a b : Bucket} (h : LaneEq a b) :
    a ++ List.replicate (max a.length b.length-a.length) none =
    b ++ List.replicate (max a.length b.length-b.length) none := by
  apply getD_ext (by simp)
  exact lane_trans (padding a _) (lane_trans h (lane_symm (padding b _)))

theorem recs_equal {a b : Bucket} (h : LaneEq a b) : a.recs = b.recs := by
  have hh := congrArg Bucket.recs (pad_equal h)
  simpa [Bucket.recs] using hh

theorem drop {a b : Bucket} (h : LaneEq a b) (n : Nat) : LaneEq (a.drop n) (b.drop n) := by
  intro i
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_drop,Nat.add_comm] using h (n+i)

theorem take {a b : Bucket} (h : LaneEq a b) (n : Nat) : LaneEq (a.take n) (b.take n) := by
  intro i
  simp only [List.getD_eq_getElem?_getD,List.getElem?_take]
  split
  · exact h i
  · rfl

theorem ofBucket_equal {a b : Bucket} (h : LaneEq a b) : Page.ofBucket a = Page.ofBucket b := by
  unfold LaneEq at h
  unfold Page.ofBucket
  simp_rw [h]

theorem bucketPages_equal {a b : Bucket} (h : LaneEq a b) (n : Nat) :
    bucketPages n a = bucketPages n b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [bucketPages,ofBucket_equal h,ih (drop h 64)]

theorem pagesOf_equal {a b : Bucket} (h : LaneEq a b) (C n : Nat) :
    pagesOf C n a = pagesOf C n b := by
  unfold pagesOf
  apply List.map_congr_left
  intro p _
  split
  · exact recs_equal (drop h _)
  · exact recs_equal (take (drop h _) _)

theorem sepInputs_equal (g : SepGeom) {prev prev' carry carry' : Output}
    (hp : OutputEq prev prev') (hc : OutputEq carry carry') :
    sepInputs g prev carry = sepInputs g prev' carry' := by
  simp only [sepInputs,hp.1,hc.1,recs_equal hp.2,pagesOf_equal hc.2]

theorem prepInputs_equal {prev prev' : Output} (hp : OutputEq prev prev') :
    prepInputs prev = prepInputs prev' := by
  simp only [prepInputs,hp.1,recs_equal hp.2]

theorem finishInputs_equal {prev prev' carry carry' : Output}
    (hp : OutputEq prev prev') (hc : OutputEq carry carry') :
    finishInputs prev carry = finishInputs prev' carry' := by
  simp only [finishInputs,hp.1,hc.1,recs_equal hp.2,recs_equal hc.2]

end RebuildBound.NativeMatchHierarchyLayoutProof


namespace RebuildBound.NativeMatchHierarchyLayoutProof
open Model Model.Hierarchy Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchHierarchy

theorem output_refl (a : Output) : OutputEq a a := ⟨rfl,lane_refl _⟩
theorem output_trans {a b c : Output} (hab : OutputEq a b) (hbc : OutputEq b c) : OutputEq a c :=
  ⟨hab.1.trans hbc.1,lane_trans hab.2 hbc.2⟩

theorem adopt_equal {a b : Output} (h : OutputEq a b) (units : List Bucket) :
    adopt a units = adopt b units := by
  simp only [adopt,h.1,recs_equal h.2]

theorem prepOutput_equal (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)
    (ordinal : Nat) {a b : Output} (h : OutputEq a b) :
    prepOutput cfg sh tr words ordinal a = prepOutput cfg sh tr words ordinal b := by
  simp only [prepOutput,prepInputs_equal h]

theorem directRaw_equal (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    {a b : Output} (h : OutputEq a b) : directRaw g word inp a = directRaw g word inp b := by
  simp only [directRaw,bucketPages_equal h.2]

theorem directNative_equal (stored : LogicalKey → Stored) (g : Geometry) (word : LogicalKey → Nat)
    (units : List Bucket) {a b : Output} (h : OutputEq a b) :
    directNative stored g word (adopt a units) a = directNative stored g word (adopt b units) b := by
  simp only [directNative,adopt_equal h,directRaw_equal _ _ _ h]

/-- Inputs related only by unused trailing lanes run the same computational
job. An adoption preserves the relation instead of forcing list equality. -/
theorem step_congr (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes)
    (tr : Trace) (words : Words) (level ordinal : Nat) {prev prev' carry carry' : Output}
    (hp : OutputEq prev prev') (hc : OutputEq carry carry') :
    ∀ out', nativeStep stored cfg sh tr words level ordinal prev' carry' = some out' →
      ∃ out, nativeStep stored cfg sh tr words level ordinal prev carry = some out ∧ OutputEq out out' := by
  intro out' hout
  unfold nativeStep at hout ⊢
  dsimp only at hout ⊢
  split_ifs at hout ⊢ with ht hl hd hd
  · have he := prepOutput_equal cfg sh tr words ordinal hp
    rw [he,finishInputs_equal (output_refl _) hc,bucketPages_equal hc.2]
    exact ⟨out',hout,output_refl _⟩
  · exact ⟨out',hout,output_refl _⟩
  · rw [directNative_equal stored _ _ _ hp]
    exact ⟨out',hout,output_refl _⟩
  · cases hout
    exact ⟨carry,rfl,hc⟩
  · rw [sepInputs_equal _ hp hc,bucketPages_equal hp.2]
    exact ⟨out',hout,output_refl _⟩

end RebuildBound.NativeMatchHierarchyLayoutProof


namespace RebuildBound.NativeMatchHierarchyReplayProof
open Model Model.Hierarchy Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchHierarchy
open NativeMatchHierarchyLayoutProof

/-- A proof-only induction combinator. Its local step premise is discharged
below by the proved job implementations at the reference pre-states; it is
not a whole-execution agreement or stored-key-independence hypothesis. -/
theorem table_replay (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes)
    (tr : Trace) (words : Words) (H : Nat)
    (hcarry : ∀ level ordinal, 2 ≤ level → level ≤ cfg.levels →
      time cfg (level-1) (ordinal*cfg.fanout (level-1)) = time cfg level ordinal)
    (hstep : ∀ level ordinal, 1 ≤ level → level ≤ cfg.levels → cfg.seed level < ordinal →
      time cfg level ordinal ≤ H →
      let prev := Hierarchy.table cfg sh tr words level (ordinal-1)
      let carry := if level = 1 then emptyOutput else
        Hierarchy.table cfg sh tr words (level-1) (ordinal*cfg.fanout (level-1))
      ∃ out, nativeStep stored cfg sh tr words level ordinal prev carry = some out ∧
        OutputEq out (Hierarchy.step cfg sh tr words level ordinal prev carry))
    (level ordinal : Nat) (hH : time cfg level ordinal ≤ H) :
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
        obtain ⟨exactOut,hexact,heq⟩ := hstep level ordinal hl1 hlL (by omega) hH
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
          obtain ⟨out,hout,heout⟩ := step_congr stored cfg sh tr words level ordinal hprevEq hcarryEq
            exactOut (by simpa only [hl,ite_false] using hexact)
          refine ⟨out,?_,?_⟩
          · rw [nativeTable,ite_eq_right hb,hprev]
            simp only [hl,ite_false,hcarryOut]
            exact hout
          · rw [Hierarchy.table,ite_eq_right hb]
            exact output_trans heout (by simpa only [hl,ite_false] using heq)

end RebuildBound.NativeMatchHierarchyReplayProof


namespace RebuildBound.NativeMatchHierarchyLocalReplay
open Model Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open HierarchyInvariantProof HierarchyCoveringProof NativeMatchPhysicalInputs NativeMatchHierarchyLayoutProof

theorem pagesOf_fits (C n : Nat) (tier : Bucket) (hfit : tier.length ≤ C*n) :
    ∀ page ∈ pagesOf C n tier, page.length ≤ C := by
  intro page hp
  simp only [pagesOf] at hp
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hp
  split_ifs with he
  · have h := List.length_filterMap_le id (tier.drop (C*p))
    simp only [List.length_drop] at h
    have heq : C*n = C*p+C := by rw [← he]; ring
    change ((tier.drop (C*p)).filterMap id).length ≤ C
    omega
  · exact (List.length_filterMap_le _ _).trans (List.length_take_le _ _)

theorem sep_no_failure (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)
    (level ordinal : Nat) (hj : JobId.ordinary level ordinal ∈ cfg.potentialJobs)
    (hW : WithinHorizon cfg (.ordinary level ordinal)) (h2 : 2 ≤ level)
    (hd : cfg.digitAt level ordinal ≠ 1) (hno : ¬Fails cfg sh tr words) :
    sFirstFailure (sh.sep level (cfg.digitAt level ordinal))
      (sReferenceWith engineRule (sh.sep level (cfg.digitAt level ordinal))
        (jobWord cfg words level ordinal) (sepInputsAt cfg sh tr words level ordinal)
        (engineOps (sh.sep level (cfg.digitAt level ordinal)))).trace = none := by
  have hf : jobFails cfg sh tr words (.ordinary level ordinal) = false := by
    apply Bool.eq_false_iff.mpr
    exact fun h => hno ⟨_,hj,hW,h⟩
  have hl : level ≠ 1 := by omega
  simp only [jobFails,hl,hd,ite_false,Bool.not_eq_false'] at hf
  obtain ⟨out,hok⟩ := toBool_ok hf
  unfold sepResult sJob sJobWith at hok
  dsimp only at hok
  split at hok
  · cases hok
  · assumption

theorem top_no_failure (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)
    (ordinal : Nat) (hj : JobId.topFinish ordinal ∈ cfg.potentialJobs)
    (hW : WithinHorizon cfg (.topFinish ordinal)) (hno : ¬Fails cfg sh tr words) :
    firstFailure sh.top.toGeom sh.top.caps
      (topReference sh.top tr.unsh (jobWord cfg words cfg.levels ordinal)
        (finishInputsAt cfg sh tr words ordinal)).trace = none := by
  have hf : jobFails cfg sh tr words (.topFinish ordinal) = false := by
    apply Bool.eq_false_iff.mpr
    exact fun h => hno ⟨_,hj,hW,h⟩
  simp only [jobFails,Bool.not_eq_false'] at hf
  obtain ⟨out,hok⟩ := toBool_ok hf
  unfold finishResult topJob at hok
  dsimp only at hok
  split at hok
  · cases hok
  · assumption

set_option maxHeartbeats 1000000 in
theorem separated (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (classes : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    {N : Nat} (tr : Trace) (hT : TracePremises geo.cfg N tr) (words : Words)
    (level ordinal : Nat) (hj : JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs)
    (hW : WithinHorizon geo.cfg (.ordinary level ordinal)) (h2 : 2 ≤ level)
    (hd2 : 2 ≤ geo.cfg.digitAt level ordinal) (hno : ¬Fails geo.cfg geo.shapes tr words)
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
  have ha := separated_a_length geo F tr words hno level ordinal hj hW h2 (by omega)
  rw [hg,hC] at ha
  have hb := (carry_length geo F tr words hno level ordinal h2 hL.le ho hW).trans hlink
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
  have hn := sep_no_failure geo.cfg geo.shapes tr words level ordinal hj hW h2 (by omega) hno
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
theorem top (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (classes : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (tr : Trace) (hT : TraceStructural geo.cfg tr)
    (hLen : tr.init.length ≤ geo.init.C/2*geo.init.T) (hUnsh : UnshPromise geo.cfg geo.shapes tr)
    (words : Words) (ordinal : Nat) (hj : JobId.topFinish ordinal ∈ geo.cfg.potentialJobs)
    (hW : WithinHorizon geo.cfg (.topFinish ordinal)) (hdfs : geo.top.dfs = true)
    (hno : ¬Fails geo.cfg geo.shapes tr words)
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
  obtain ⟨hr,hb⟩ := finish_lengths geo F tr words hno ordinal hj hW
  have hlayoutR : pageRecords (bucketPages geo.top.rPages prepared.tier) = (finishInputs prepared carry).carry := by
    rw [NativeMatchDenseTraceProof.bucketPages_records,List.take_of_length_le ?_]
    · rfl
    · simpa only [TopGeom.SR,G.topC,Nat.mul_comm] using hr
  have hlayoutB : pageRecords (bucketPages geo.top.bPages carry.tier) = (finishInputs prepared carry).bTier := by
    rw [NativeMatchDenseTraceProof.bucketPages_records,List.take_of_length_le ?_]
    · rfl
    · simpa only [TopGeom.SB,G.topC,Nat.mul_comm] using hb
  have hn := top_no_failure geo.cfg geo.shapes tr words ordinal hj hW hno
  have he := (RebuildBound.NativeMatchTopFullJob bridge retained classes stored geo.top tr.unsh
    (jobWord geo.cfg words geo.cfg.levels ordinal) (finishInputs prepared carry) _ _
    G.topValid G.topC hs hdfs hn hlayoutR hlayoutB).1 hoff
  dsimp only
  rw [he]
  exact ⟨rfl,padding _ _⟩

end RebuildBound.NativeMatchHierarchyLocalReplay


namespace RebuildBound.NativeMatchHierarchyDirectReplay
open Model Model.DirectJob Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchHierarchy NativeMatchHierarchyLayoutProof

theorem pageAllocation_bound (n : Nat) : n ≤ 64*pageAllocation n := by
  unfold pageAllocation
  omega

set_option maxHeartbeats 1000000 in
/-- A published direct job supplies the actual phase successes. The only
physical input premise here is its original previous-tier allocation; the
hierarchy adapter derives that from its successful producer. -/
theorem published (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (classes : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (g : Geometry) (oldWord word : LogicalKey → Nat)
    (prev : Output) (units : List Bucket) (out : Output)
    (hpub : runJob g oldWord word (adopt prev units) = .published out)
    (hwidth : ∀ bucket ∈ units, bucket.length ≤ 64)
    (hcap : 2 ≤ g.digit → g.bCapacity ≤ 64)
    (hprev : 2 ≤ g.digit → prev.tier.length ≤ g.aTierCapacity)
    (hoff : ∀ e ∈ directEvents g word (adopt prev units) prev, ¬e.bad stored) :
    ∃ nativeOut, directNative stored g word (adopt prev units) prev = some nativeOut ∧
      OutputEq nativeOut out := by
  have hp : ∀ e ∈ NativeMatchPrefixProducer.events units, ¬e.bad stored :=
    fun e he => hoff e (List.mem_append_left _ he)
  obtain ⟨hg,hi,_⟩ := DirectJobPublication g oldWord word (adopt prev units) out hpub
  have hproducer := NativeMatchPrefixProducerProof.producer_agreement bridge stored g word (adopt prev units)
    hwidth hi.2.2.2.2.1 hp
  by_cases hd : g.digit = 1
  · obtain ⟨_,_,b,hb,hout⟩ := NativeMatchDirectSuccess.first g oldWord word (adopt prev units) out hd hpub
    refine ⟨out,?_,output_refl _⟩
    simp only [directNative,hproducer,hb,hd,ite_true,← hout]
  · have hd2 : 2 ≤ g.digit := by have := hg.1; omega
    obtain ⟨_,_,ha,b,hb,hdis,hfin,hout⟩ := NativeMatchDirectSuccess.later g oldWord word (adopt prev units) out hd2 hpub
    have hs : pageRecords (directSources b) = b.tier := by
      have hfit := (DirectJobBSuccess g word (adopt prev units) b hi.2.2.2.2.1 hb).2.2.2.2.1
      simpa only [directSources,pageRecords,List.flatMap_cons,List.flatMap_nil,List.append_nil]
        using NativeMatchPageProof.ofRecords_recs b.tier (hfit.trans (hcap hd2))
    have htier : pageRecords (bucketPages (pageAllocation g.aTierCapacity) prev.tier) =
        (adopt prev units).aTier := by
      rw [NativeMatchDenseTraceProof.bucketPages_records,List.take_of_length_le ?_]
      · rfl
      · exact (hprev hd2).trans (pageAllocation_bound _)
    have hr : pageRecords (directRaw g word (adopt prev units) prev) =
        aResidual (analyticalA g word (adopt prev units).aMain).state (adopt prev units).aTier :=
      NativeMatchDirectInitialProof.allocatedRaw_projection g word (adopt prev units) _ hd ha _ _ _
        (pageAllocation_bound _) (fun _ => pageAllocation_bound _) htier
    have hoff' : ∀ e ∈ NativeMatchDirectPlanTrace.events g word (adopt prev units) b
        (directSources b) (directRaw g word (adopt prev units) prev)
        (pageAllocation g.insertionCapacity) (pageAllocation g.outputCapacity), ¬e.bad stored := by
      intro e he
      apply hoff e
      unfold directEvents
      rw [hb]
      simp only [hd,ite_false]
      exact List.mem_append_right _ he
    have he := NativeMatchDirectPlanProof.full_agreement bridge retained classes stored g oldWord word
      (adopt prev units) b (directSources b) (directRaw g word (adopt prev units) prev)
      (pageAllocation g.insertionCapacity) (pageAllocation g.outputCapacity)
      hg hd2 hi hb (hcap hd2) hs hr hdis hfin (pageAllocation_bound _) (pageAllocation_bound _) hoff'
    refine ⟨NativeMatchDirectPlanTrace.native stored g word (adopt prev units) b (directSources b)
      (directRaw g word (adopt prev units) prev) (pageAllocation g.insertionCapacity)
      (pageAllocation g.outputCapacity),?_,?_⟩
    · simp only [directNative,hproducer,hb,hd,ite_false]
    · rw [he,hout]
      exact ⟨rfl,lane_trans (padding _ _) (lane_symm (padding _ _))⟩

end RebuildBound.NativeMatchHierarchyDirectReplay


namespace RebuildBound.NativeMatchHierarchyLocalReplay
open Model Model.DirectJob Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchHierarchy NativeMatchHierarchyLayoutProof
open HierarchyInvariantProof HierarchyCoveringProof NativeMatchPhysicalInputs

theorem direct_published (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (ordinal : Nat)
    (hj : JobId.ordinary 1 ordinal ∈ cfg.potentialJobs)
    (hW : WithinHorizon cfg (.ordinary 1 ordinal)) (hno : ¬Fails cfg sh tr words) :
    ∃ out, levelOneResult cfg sh tr words ordinal = .published out := by
  have hf : jobFails cfg sh tr words (.ordinary 1 ordinal) = false := by
    apply Bool.eq_false_iff.mpr
    exact fun h => hno ⟨_,hj,hW,h⟩
  cases he : levelOneResult cfg sh tr words ordinal with
  | rejected reason => simp [jobFails,he] at hf
  | failed event => simp [jobFails,he] at hf
  | published out => exact ⟨out,rfl⟩

set_option maxHeartbeats 1000000 in
theorem direct (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (classes : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (tr : Trace) (words : Words) (ordinal : Nat)
    (hj : JobId.ordinary 1 ordinal ∈ geo.cfg.potentialJobs)
    (hW : WithinHorizon geo.cfg (.ordinary 1 ordinal))
    (hwidth : ∀ bucket ∈ tr.units (ordinal-geo.cfg.seed 1-1), bucket.length ≤ 64)
    (hcap : 2 ≤ geo.cfg.digitAt 1 ordinal → (geo.direct (geo.cfg.digitAt 1 ordinal)).bCapacity ≤ 64)
    (hlink : 2 ≤ geo.cfg.digitAt 1 ordinal →
      (geo.direct (geo.cfg.digitAt 1 ordinal-1)).outputCapacity ≤
        (geo.direct (geo.cfg.digitAt 1 ordinal)).aTierCapacity)
    (hno : ¬Fails geo.cfg geo.shapes tr words)
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
  obtain ⟨out,hpub⟩ := direct_published geo.cfg geo.shapes tr words ordinal hj hW hno
  change runJob (geo.direct d) (jobWord geo.cfg words 1 (ordinal-1))
    (jobWord geo.cfg words 1 ordinal) (adopt prev units) = .published out at hpub
  have hprev : 2 ≤ (geo.direct d).digit → prev.tier.length ≤ (geo.direct d).aTierCapacity := by
    intro hd2
    rw [hD] at hd2
    have hdne : d ≠ 1 := by omega
    dsimp only [prev]
    rw [ite_eq_right hdne]
    exact direct_previous_length geo F tr words ordinal hj hW hd2 (hlink hd2) hno
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

end RebuildBound.NativeMatchHierarchyLocalReplay


namespace RebuildBound.NativeMatchHierarchyReplayProof
open Model Model.DirectJob Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchHierarchy NativeMatchHierarchyLayoutProof
open HierarchyInvariantProof HierarchyCoveringProof NativeMatchPhysicalInputs

set_option maxHeartbeats 2000000 in
/-- Every matching transition is the corresponding proved job, applied to
its actual reference pre-state. The extra hypotheses are public geometry
arithmetic and the requester's physical unit shape. -/
theorem table_agreement (bridge : NativeMatchLanesBridge_statement)
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
    (words : Words) (hno : ¬Fails geo.cfg geo.shapes tr words)
    (hoff : ∀ j ∈ geo.cfg.potentialJobs, WithinHorizon geo.cfg j →
      ∀ e ∈ jobEvents geo.cfg geo.shapes tr words j, ¬e.bad stored)
    (level ordinal : Nat) (hH : time geo.cfg level ordinal ≤ geo.cfg.seed 1+geo.cfg.ordinals 1) :
    ∃ out, nativeTable stored geo.cfg geo.shapes tr words level ordinal = some out ∧
      OutputEq out (table geo.cfg geo.shapes tr words level ordinal) := by
  apply table_replay stored geo.cfg geo.shapes tr words (geo.cfg.seed 1+geo.cfg.ordinals 1) ?_ ?_ level ordinal hH
  · intro l v h2 hL
    have hp := F.per_succ (l-1) (by omega) (by omega)
    rw [show l-1+1=l by omega] at hp
    rw [time_eq,time_eq,hp,Nat.mul_assoc,Nat.mul_comm (geo.cfg.fanout (l-1))]
  · intro l v h1 hL ho hW
    dsimp only
    by_cases htopL : l = geo.cfg.levels
    · subst l
      have hj : JobId.topFinish v ∈ geo.cfg.potentialJobs := mem_finish.mpr ⟨ho,htop v hW⟩
      have he := NativeMatchHierarchyLocalReplay.top bridge retained classes stored geo hgeo F tr
        ⟨hT.nodup,hT.load,hT.initNodup⟩ hLen hUnsh words v hj hW hdfs hno (hoff _ hj hW)
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
        obtain ⟨out,hn,he⟩ := NativeMatchHierarchyLocalReplay.direct bridge retained classes stored geo hgeo F tr words v hj hW
          (hwidth _) (fun hd => (hdirect _ hd hdle).1) (fun hd => (hdirect _ hd hdle).2) hno (hoff _ hj hW)
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
          have he := NativeMatchHierarchyLocalReplay.separated bridge retained classes stored geo hgeo F tr hT words l v hj hW
            (by omega) hd2 hno (hsep l (by omega) (by omega) _ hd2 hdle) (hoff _ hj hW)
          have hd1' : Config.digitOf (geo.cfg.fanout l) v ≠ 1 := hd1
          simp only [nativeStep,htopL,hl1,hd1',ite_false]
          refine ⟨_,rfl,?_⟩
          simpa only [Hierarchy.step,htopL,hl1,hd1',ite_false,Config.digitAt,sReference,sepInputsAt,carryOf] using he

end RebuildBound.NativeMatchHierarchyReplayProof


namespace RebuildBound.NativeMatchRequesterLayout
open Model Model.Online Model.OnlineBatch Spec

/-- The actual requester freezes full physical units. This is independent of
stored-key values and is stronger than the reference trace's population cap. -/
theorem trace_units (g : OnlineGeom) (run : BatchRun) (hE : 0 < g.unitEntries) (i : Nat) :
    ((traceOf g run).units i).length ≤ g.unitsPerPrefix ∧
      ∀ bucket ∈ (traceOf g run).units i, bucket.length = g.unitEntries := by
  have hs := (RequesterShape g.unitEntries ⟨[],[]⟩ ((run.ops.take run.ops.length).map Op.requester)
    hE (by simp) (by simpa using hE)).1
  refine ⟨List.length_take_le _ _,?_⟩
  intro bucket hb
  exact hs bucket (List.mem_of_mem_drop (List.mem_of_mem_take hb))

theorem trace_width64 (g : OnlineGeom) (run : BatchRun) (hE : g.unitEntries = 64) :
    ∀ i, ∀ bucket ∈ (traceOf g run).units i, bucket.length ≤ 64 := by
  intro i bucket hb
  exact ((trace_units g run (by omega) i).2 bucket hb).trans_le hE.le

end RebuildBound.NativeMatchRequesterLayout


namespace RebuildBound.NativeMatchHierarchyReplayProof
open Model Model.Hierarchy Spec HierarchyCoveringProof HierarchyChunkArith

/-- The top's ordinal range follows from the same exact carry-period
arithmetic as the lower levels, including a partial final prefix. -/
theorem top_horizon {cfg : Config} (F : ChunkFacts cfg) (h ordinal : Nat)
    (hW : time (chunkConfig cfg h) cfg.levels ordinal ≤
      (chunkConfig cfg h).seed 1 + (chunkConfig cfg h).ordinals 1) :
    ordinal ≤ (chunkConfig cfg h).seed cfg.levels + (chunkConfig cfg h).ordinals cfg.levels := by
  have h1 : 1 ≤ cfg.levels := by have := F.levels_ge; omega
  have ht : ordinal * per cfg cfg.levels ≤
      (cfg.seed cfg.levels+h*(cfg.ordinals cfg.levels-1))*per cfg cfg.levels+1 := by
    change ordinal*per cfg cfg.levels ≤ cfg.seed 1+(chunkConfig cfg h).ordinals 1 at hW
    rw [ordinals_chunk F h 1 (by omega) (by omega),bound_eq F h cfg.levels h1 le_rfl] at hW
    exact hW
  have hb := aux_le_succ (F.per_pos cfg.levels (by omega) h1) ht
  change ordinal ≤ cfg.seed cfg.levels + (chunkConfig cfg h).ordinals cfg.levels
  rw [ordinals_chunk F h cfg.levels h1 le_rfl]
  simpa only [Nat.add_assoc] using hb

end RebuildBound.NativeMatchHierarchyReplayProof


namespace RebuildBound.NativeMatchHierarchyFamilyReplay
open Model Model.Hierarchy Model.Online Spec ConfigurationFamily Spec.NativeMatch Spec.NativeMatch.Lanes
open Spec.NativeMatchHierarchy NativeMatchPhysicalInputs HierarchyCoveringProof

def Links (m : Member) (initialized : Bool) : Prop :=
  (m.geometry initialized).top.dfs = true ∧
  (∀ j ∈ List.range ((m.config initialized).fanout 1-1),
    (m.direct (j+2)).bCapacity ≤ 64 ∧
      (m.direct (j+1)).outputCapacity ≤ (m.direct (j+2)).aTierCapacity) ∧
  (∀ p ∈ (m.config initialized).separatedClasses,
    incomingCapacity (m.config initialized) (m.geometry initialized).shapes p.1 ≤
      ((m.geometry initialized).shapes.sep p.1 p.2).bTierPages *
        ((m.geometry initialized).shapes.sep p.1 p.2).C)

instance (m : Member) (b : Bool) : Decidable (Links m b) :=
  inferInstanceAs (Decidable (_ ∧ (∀ j ∈ _, _) ∧ (∀ p ∈ _, _)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem links : ∀ m ∈ members, Links m true ∧ Links m false := by decide +kernel

theorem shapes_chunk (geo : HierarchyGeometry) (h : Nat) : (geo.chunk h).shapes = geo.shapes := by
  unfold HierarchyGeometry.shapes HierarchyGeometry.chunk hierarchyShapesWith chunkConfig
  rw [(HierarchyHorizonFree geo.cfg (h*2^32) geo.rows).2.1]

theorem separated_class_mem (cfg : Config) (level digit : Nat)
    (h2 : 2 ≤ level) (hL : level < cfg.levels) (hd2 : 2 ≤ digit) (hdb : digit ≤ cfg.fanout level) :
    (level,digit) ∈ cfg.separatedClasses := by
  apply List.mem_filterMap.mpr
  refine ⟨(.ordinary level digit,cfg.ordinaryCount level digit),?_,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨level,?_,?_⟩
    · exact List.mem_map.mpr ⟨level-1,List.mem_range.mpr (by omega),by omega⟩
    · exact List.mem_map.mpr ⟨digit-1,List.mem_range.mpr (by omega),by simp [show digit-1+1=digit by omega]⟩
  · simp [h2,hd2]

set_option maxHeartbeats 2000000 in
theorem replay (m : Member) (initialized : Bool) (hm : m ∈ members)
    (h : Nat) (run : OnlineBatch.BatchRun)
    (hready : RunReady m initialized h run) (stored : LogicalKey → Stored) (words : Words) :
    let geo := (m.geometry initialized).chunk h
    let tr := OnlineBatch.traceOf ⟨64,m.r0⟩ run
    ¬Fails geo.cfg geo.shapes tr words → OffEvents stored geo.cfg geo.shapes tr words →
    ∀ level ordinal, time geo.cfg level ordinal ≤ geo.cfg.seed 1+geo.cfg.ordinals 1 →
      ∃ out, nativeTable stored geo.cfg geo.shapes tr words level ordinal = some out ∧
        OutputEq out (table geo.cfg geo.shapes tr words level ordinal) := by
  let geo := (m.geometry initialized).chunk h
  let g : OnlineGeom := ⟨64,m.r0⟩
  let tr := OnlineBatch.traceOf g run
  dsimp only
  intro hno hoff level ordinal hH
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
  apply NativeMatchHierarchyReplayProof.table_agreement RebuildBound.NativeMatchLanesBridge
    RebuildBound.NativeMatchRetained RebuildBound.NativeMatchClassBridge stored geo hgeo F tr hT
    hready.2.1 hready.2.2 (NativeMatchRequesterLayout.trace_width64 g run rfl) ?_ hlinks.1 ?_ ?_
    words hno hoff level ordinal hH
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

end RebuildBound.NativeMatchHierarchyFamilyReplay

namespace RebuildBound.NativeMatchHierarchyTracePrefix
open Model Model.DirectJob Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchHierarchy
open HierarchyInvariantProof OnlineCorrectnessProof

/-- The matching continuation reads exactly the same finite requester-unit
prefix as the existing reference recursion, even on a bad stored-key map. -/
theorem table_trace_congr {geo : HierarchyGeometry}
    (F : LowFacts geo.cfg geo.rows geo.direct) (stored : LogicalKey → Stored)
    (tr tr' : Trace) (hi : tr.init = tr'.init) (hu : tr.unsh = tr'.unsh) (words : Words) :
    ∀ level, 1 ≤ level → level ≤ geo.cfg.levels → ∀ ordinal,
      (∀ i < unitEnd geo.cfg level ordinal, tr.units i = tr'.units i) →
      nativeTable stored geo.cfg geo.shapes tr words level ordinal =
        nativeTable stored geo.cfg geo.shapes tr' words level ordinal := by
  intro level
  induction level using Nat.strong_induction_on with
  | h level ihl =>
    intro h1 hL ordinal
    induction ordinal using Nat.strong_induction_on with
    | h ordinal ihv =>
      intro hag
      by_cases hb : level=0 ∨ geo.cfg.levels<level ∨ ordinal≤geo.cfg.seed level
      · rw [nativeTable,ite_eq_left hb,nativeTable,ite_eq_left hb]
        simp only [base,initOutput,hi]
      · have hp := ihv (ordinal-1) (by omega) (fun i h =>
          hag i (lt_of_lt_of_le h (unitEnd_mono geo.cfg level (Nat.sub_le _ _))))
        have hc : (if level=1 then some emptyOutput else
            nativeTable stored geo.cfg geo.shapes tr words (level-1) (ordinal*geo.cfg.fanout (level-1))) =
          (if level=1 then some emptyOutput else
            nativeTable stored geo.cfg geo.shapes tr' words (level-1) (ordinal*geo.cfg.fanout (level-1))) := by
          split_ifs with he
          · rfl
          · apply ihl (level-1) (by omega) (by omega) (by omega)
            intro i hidx
            have hend := unitEnd_carry F (ℓ:=level-1) (by omega) (by omega) ordinal
            rw [Nat.sub_add_cancel (by omega)] at hend
            exact hag i (by rwa [hend] at hidx)
        have hs : ∀ prev carry,
            nativeStep stored geo.cfg geo.shapes tr words level ordinal prev carry =
              nativeStep stored geo.cfg geo.shapes tr' words level ordinal prev carry := by
          intro prev carry
          simp only [nativeStep,prepOutput,hu]
          by_cases ht : level=geo.cfg.levels
          · simp only [ht,ite_true]
          · simp only [ht,ite_false]
            by_cases hl : level=1
            · subst level
              have hidx : ordinal-geo.cfg.seed 1-1 < unitEnd geo.cfg 1 ordinal := by
                rw [unitEnd_one]
                omega
              rw [hag _ hidx]
            · simp only [hl,ite_false]
        conv_lhs => rw [nativeTable,ite_eq_right hb]
        conv_rhs => rw [nativeTable,ite_eq_right hb]
        rw [hp]
        simp_rw [hs]
        by_cases he : level=1
        · simp only [he,ite_true]
        · simp only [he,ite_false] at hc ⊢
          rw [hc]

end RebuildBound.NativeMatchHierarchyTracePrefix
