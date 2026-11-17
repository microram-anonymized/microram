import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyDirect
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyDirectGood
import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyHierarchyGuards

namespace RebuildBound.NativeRekeyDirectCertified
open Model Model.Hierarchy Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeRekeyRouting NativeRekeyHierarchyBase Spec.NativeMatchHierarchy
open NativeMatchHierarchyLayoutProof NativeMatchPhysicalInputs HierarchyCoveringProof HierarchyInvariantProof

set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma layout_of_laneEq (n : Nat) (a b : Bucket) (h : LaneEq a b) (hb : b.length ≤ 64*n) :
    pageRecords (bucketPages n a) = a.recs := by
  rw [bucketPages_equal h,bucketPages_layout n b hb,recs_equal h]

lemma direct_published_map (f : LogicalKey → LogicalKey) (bridge : NativeMatchLanesBridge_statement)
    (s s' : LogicalKey → Stored) (hs : ∀ k, s' (f k) = s k)
    (g : Geometry) (oldWord' w w' : LogicalKey → Nat) (hw : ∀ k, w' (f k) = w k)
    (prev canonical : Output) (units : List Bucket) (out : Output)
    (hp : OutputEq (output f prev) canonical)
    (hpub : runJob g oldWord' w' (adopt canonical (buckets f units)) = .published out)
    (hwidth : ∀ b ∈ buckets f units, b.length ≤ 64)
    (hprev : 2 ≤ g.digit → canonical.tier.length ≤ g.aTierCapacity)
    (hoff : ∀ e ∈ NativeMatchPrefixProducer.events (buckets f units), ¬ e.bad s') :
    directNative s' g w' (adopt (output f prev) (buckets f units)) (output f prev) =
      (directNative s g w (adopt prev units) prev).map (output f) := by
  have hinputs : adopt (output f prev) (buckets f units) = adopt canonical (buckets f units) :=
    adopt_equal hp _
  obtain ⟨hg,hi,_⟩ := DirectJobPublication g oldWord' w' (adopt canonical (buckets f units)) out hpub
  rw [←hinputs] at hi
  have hproducer := NativeMatchPrefixProducerProof.producer_agreement bridge s' g w'
    (adopt (output f prev) (buckets f units)) hwidth hi.2.2.2.2.1 hoff
  have hmap := NativeRekeyDirect.directNative_map f s s' hs g ⟨w,w',hw⟩ (adopt prev units) prev
  rw [←adopt_map] at hmap
  apply hmap
  intro hd b hnb
  have hd2 : 2 ≤ g.digit := by have := hg.1; omega
  have hb : buildB g w' (adopt (output f prev) (buckets f units)) = .ok b := by
    rw [←hproducer]
    exact hnb
  have hpage : pageRecords (bucketPages (pageAllocation g.aTierCapacity) (output f prev).tier) =
      (adopt (output f prev) (buckets f units)).aTier := by
    exact layout_of_laneEq _ _ _ hp.2 ((hprev hd2).trans
      (NativeMatchHierarchyDirectReplay.pageAllocation_bound _))
  exact NativeRekeyDirectGood.initial_good_allocated s' g oldWord' w'
    (adopt (output f prev) (buckets f units)) b (directSources b) _ _ _ hg hd2 hi hb hpage

lemma direct_certified {f : LogicalKey → LogicalKey} {tr tr' : Hierarchy.Trace}
    (ht : TraceRel f tr tr') {words words' : Words} (hw : WordsRel f words words')
    (bridge : NativeMatchLanesBridge_statement) (s s' : LogicalKey → Stored)
    (hs : ∀ k, s' (f k) = s k)
    (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (v : Nat) (hj : JobId.ordinary 1 v ∈ geo.cfg.potentialJobs)
    (hW : WithinHorizon geo.cfg (.ordinary 1 v))
    (hwidth : ∀ bucket ∈ tr'.units (v-geo.cfg.seed 1-1), bucket.length ≤ 64)
    (hlink : 2 ≤ geo.cfg.digitAt 1 v →
      (geo.direct (geo.cfg.digitAt 1 v-1)).outputCapacity ≤
        (geo.direct (geo.cfg.digitAt 1 v)).aTierCapacity)
    (hno : ¬Fails geo.cfg geo.shapes tr' words')
    (hoff : ∀ e ∈ jobEvents geo.cfg geo.shapes tr' words' (.ordinary 1 v), ¬ e.bad s')
    (prev carry : Output)
    (hp : OutputEq (output f prev) (Hierarchy.table geo.cfg geo.shapes tr' words' 1 (v-1))) :
    nativeStep s' geo.cfg geo.shapes tr' words' 1 v (output f prev) (output f carry) =
      (nativeStep s geo.cfg geo.shapes tr words 1 v prev carry).map (output f) := by
  let d := geo.cfg.digitAt 1 v
  let canonical := if d=1 then emptyOutput else Hierarchy.table geo.cfg geo.shapes tr' words' 1 (v-1)
  let previous := if d=1 then emptyOutput else prev
  let units := tr.units (v-geo.cfg.seed 1-1)
  have hrel : OutputEq (output f previous) canonical := by
    unfold previous canonical
    split
    · exact output_refl _
    · exact hp
  have LF := HierarchySemanticsProof.lower hgeo.1
  obtain ⟨h1,hL,ho,hov⟩ := mem_ordinary.1 hj
  have hfan := F.fanout_ge 1 hL (by omega)
  have hdpos : 1 ≤ d := HierarchyCoveringProof.digit_pos _ _
  have hdle : d ≤ geo.cfg.fanout 1 := HierarchyCoveringProof.digit_le (by omega)
  have hD := (LF.direct d (by omega) hdpos).2.2
  obtain ⟨out,hpub⟩ := NativeMatchHierarchyLocalReplay.direct_published geo.cfg geo.shapes tr' words' v hj hW hno
  change runJob (geo.direct d) (jobWord geo.cfg words' 1 (v-1))
    (jobWord geo.cfg words' 1 v) (adopt canonical (tr'.units (v-geo.cfg.seed 1-1))) = .published out at hpub
  have hprev : 2 ≤ (geo.direct d).digit → canonical.tier.length ≤ (geo.direct d).aTierCapacity := by
    intro hd2
    rw [hD] at hd2
    have hdne : d ≠ 1 := by omega
    dsimp only [canonical]
    rw [ite_eq_right hdne]
    exact direct_previous_length geo F tr' words' v hj hW hd2 (hlink hd2) hno
  have hoffprefix : ∀ e ∈ NativeMatchPrefixProducer.events (tr'.units (v-geo.cfg.seed 1-1)), ¬ e.bad s' := by
    intro e he
    apply hoff e
    exact List.mem_append_left _ he
  rw [ht.units] at hpub hwidth hoffprefix
  have hm := direct_published_map f bridge s s' hs (geo.direct d) (jobWord geo.cfg words' 1 (v-1))
    (jobWord geo.cfg words 1 v) (jobWord geo.cfg words' 1 v) (jobWord_rel hw geo.cfg 1 v)
    previous canonical units out hrel hpub hwidth hprev hoffprefix
  have hl : (1 : Nat) ≠ geo.cfg.levels := by omega
  simp only [nativeStep,hl,ite_false,ite_true,ht.units]
  change directNative s' (geo.direct d) (jobWord geo.cfg words' 1 v)
    (adopt (if d=1 then emptyOutput else output f prev) (buckets f units))
    (if d=1 then emptyOutput else output f prev) = _
  have he : (if d=1 then emptyOutput else output f prev) = output f previous := by
    unfold previous
    split <;> rfl
  rw [he]
  exact hm

end RebuildBound.NativeRekeyDirectCertified
