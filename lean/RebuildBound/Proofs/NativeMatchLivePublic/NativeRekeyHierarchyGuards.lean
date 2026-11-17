import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyHierarchyBase
import RebuildBound.Proofs.NativeMatchHierarchy.Replay

namespace RebuildBound.NativeRekeyHierarchyGuards
open Model Model.Hierarchy Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeRekeyRouting NativeRekeyHierarchyBase Spec.NativeMatchHierarchy
open NativeMatchHierarchyLayoutProof NativeMatchPhysicalInputs HierarchyCoveringProof HierarchyInvariantProof

set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma bucketPages_sublist (n : Nat) (b : Bucket) :
    (pageRecords (bucketPages n b)).Sublist b.recs := by
  rw [NativeMatchDenseTraceProof.bucketPages_records]
  exact (List.take_sublist (64*n) b).filterMap id

lemma layout_of_mapped_laneEq (f : LogicalKey → LogicalKey) (n : Nat)
    (b canonical : Bucket) (h : LaneEq (bucket f b) canonical)
    (hc : canonical.length ≤ 64*n) :
    pageRecords (bucketPages n b) = b.recs := by
  have htarget : pageRecords (bucketPages n (bucket f b)) = (bucket f b).recs := by
    rw [bucketPages_equal h,bucketPages_layout n canonical hc,recs_equal h]
  have hm := NativeRekeyLocal.rel_pageRecords (NativeRekeyDrain.bucket_pages_rel f n b)
  have he : (pageRecords (bucketPages n b)).length = b.recs.length := by
    rw [←List.length_map (f := NativeRekeyLocal.rec f),←hm]
    change (pageRecords (bucketPages n (bucket f b))).length = b.recs.length
    rw [htarget,bucket_recs,records,List.length_map]
  exact (bucketPages_sublist n b).eq_of_length he

lemma top_native_layout_shape {f : LogicalKey → LogicalKey} {tr tr' : Hierarchy.Trace}
    (ht : TraceRel f tr tr') {words words' : Words} (hw : WordsRel f words words')
    (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (cfg : Config) (sh : Shapes) (v : Nat) (prev carry : Output)
    (hr : pageRecords (bucketPages sh.top.rPages (prepOutput cfg sh tr words v prev).tier) =
      Bucket.recs (prepOutput cfg sh tr words v prev).tier)
    (hb : pageRecords (bucketPages sh.top.bPages carry.tier) = Bucket.recs carry.tier)
    (hshape : TopShape sh.top tr'.unsh (jobWord cfg words' cfg.levels v)
      (finishInputs (prepOutput cfg sh tr' words' v (output f prev)) (output f carry))) :
    nativeStep s' cfg sh tr' words' cfg.levels v (output f prev) (output f carry) =
      (nativeStep s cfg sh tr words cfg.levels v prev carry).map (output f) := by
  let prepared := prepOutput cfg sh tr words v prev
  have hp := prepOutput_map ht hw cfg sh v prev
  have hc := NativeRekeyDrain.bucket_pages_rel f sh.top.rPages prepared.tier
  have hbc := NativeRekeyDrain.bucket_pages_rel f sh.top.bPages carry.tier
  rw [hp,finishInputs_map] at hshape
  have hn := NativeRekeyTop.native_map_shape hc hbc s s' hs sh.top
    tr.unsh tr'.unsh ht.unsh (jobWord cfg words cfg.levels v)
    (jobWord cfg words' cfg.levels v) (jobWord_rel hw cfg _ _) (finishInputs prepared carry)
    hr hb hshape
  simp only [nativeStep,ite_true,hp,finishInputs_map,Option.map_some]
  exact congrArg some hn

lemma top_certified {f : LogicalKey → LogicalKey} {tr tr' : Hierarchy.Trace}
    (ht : TraceRel f tr tr') {words words' : Words} (hw : WordsRel f words words')
    (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (hT : TraceStructural geo.cfg tr')
    (hLen : tr'.init.length ≤ geo.init.C/2*geo.init.T)
    (hUnsh : UnshPromise geo.cfg geo.shapes tr')
    (hno : ¬Fails geo.cfg geo.shapes tr' words')
    (v : Nat) (hj : JobId.topFinish v ∈ geo.cfg.potentialJobs)
    (hW : WithinHorizon geo.cfg (.topFinish v)) (prev carry : Output)
    (hp : OutputEq (output f prev) (Hierarchy.table geo.cfg geo.shapes tr' words' geo.cfg.levels (v-1)))
    (hc : OutputEq (output f carry) (carryOf geo.cfg geo.shapes tr' words' geo.cfg.levels v)) :
    nativeStep s' geo.cfg geo.shapes tr' words' geo.cfg.levels v (output f prev) (output f carry) =
      (nativeStep s geo.cfg geo.shapes tr words geo.cfg.levels v prev carry).map (output f) := by
  let canonicalPrev := Hierarchy.table geo.cfg geo.shapes tr' words' geo.cfg.levels (v-1)
  let canonicalPrep := prepOutput geo.cfg geo.shapes tr' words' v canonicalPrev
  let canonicalCarry := carryOf geo.cfg geo.shapes tr' words' geo.cfg.levels v
  let prepared := prepOutput geo.cfg geo.shapes tr words v prev
  have hprep : output f prepared = canonicalPrep :=
    (prepOutput_map ht hw geo.cfg geo.shapes v prev).symm.trans
      (prepOutput_equal geo.cfg geo.shapes tr' words' v hp)
  have G := TopFacts.of_compatible hgeo.2
  obtain ⟨hv,hv'⟩ := mem_finish.1 hj
  have hshape := (HierarchyStructuralStep geo hgeo tr' hT hLen hUnsh words' v hv hv').1
  obtain ⟨hr,hb⟩ := finish_lengths geo F tr' words' hno v hj hW
  have hr' : canonicalPrep.tier.length ≤ 64*geo.top.rPages := by
    simpa only [TopGeom.SR,G.topC,Nat.mul_comm] using hr
  have hb' : canonicalCarry.tier.length ≤ 64*geo.top.bPages := by
    simpa only [TopGeom.SB,G.topC,Nat.mul_comm] using hb
  have hpr : LaneEq (bucket f prepared.tier) canonicalPrep.tier := by
    have he := congrArg Output.tier hprep
    rw [show bucket f prepared.tier = canonicalPrep.tier from he]
    exact lane_refl _
  have hsourceR := layout_of_mapped_laneEq f geo.top.rPages prepared.tier canonicalPrep.tier hpr hr'
  have hsourceB := layout_of_mapped_laneEq f geo.top.bPages carry.tier canonicalCarry.tier hc.2 hb'
  apply top_native_layout_shape ht hw s s' hs geo.cfg geo.shapes v prev carry hsourceR hsourceB
  rw [prepOutput_equal geo.cfg geo.shapes tr' words' v hp,
    finishInputs_equal (output_refl canonicalPrep) hc]
  exact hshape

end RebuildBound.NativeRekeyHierarchyGuards
