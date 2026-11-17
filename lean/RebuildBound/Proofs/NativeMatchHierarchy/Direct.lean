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
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace RebuildBound.NativeMatchDirectDfsProof
open Model Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace Spec.NativeMatchDirectJobTrace NativeMatchDirectInitialProof
open NativeMatchFinishInvariantProof NativeMatchFinishInitialProof

theorem leaf_fits (g : Geometry) (word : LogicalKey → Nat) (pool : List Rec)
    (i r p : Nat) (hp : g.ranges = .dfs i r p)
    (hno : DirectJob.firstFailure (distributeA g word pool).trace = none)
    (leaf : List Rec) (hl : leaf ∈ (distributeA g word pool).leaves) : leaf.length ≤ 64 := by
  simp only [distributeA,hp] at hl
  obtain ⟨R,hR,rfl⟩ := List.mem_map.mp hl
  let nodes := (List.range (r+1)).flatMap fun depth =>
    (List.range (2^depth)).map fun pre => (depth,pre)
  have hn : (r,R) ∈ nodes := List.mem_flatMap.mpr ⟨r,by simp,List.mem_map.mpr ⟨R,hR,rfl⟩⟩
  have hz : (r,R) ∈ nodes.zipIdx.map Prod.fst := by simpa using hn
  obtain ⟨node,hnode,heq⟩ := List.mem_map.mp hz
  have he : (⟨⟨.distributeA,.dfs node.1.1 node.1.2,node.2⟩,
      (pool.filter fun x => g.home (word x.key) / 2^i / 2^(r-node.1.1) == node.1.2).length,
      min p (64*2^(r-node.1.1))⟩ : CheckEvent) ∈ (distributeA g word pool).trace := by
    simp only [distributeA,hp]
    exact List.mem_map_of_mem hnode
  have hc := NativeMatchDirectDrainProof.noFailure_entry _ hno _ he
  change (pool.filter fun x => g.home (word x.key) / 2^i / 2^(r-node.1.1) == node.1.2).length ≤
    min p (64*2^(r-node.1.1)) at hc
  simp only [heq,Nat.sub_self,pow_zero,Nat.div_one,Nat.mul_one] at hc
  exact hc.trans (min_le_right _ _)

theorem initial_projection (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier) :
    (dfsInitialGhost g word inp b sources raw).state =
      finishInitial b (analyticalA g word inp.aMain).state.main
        (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves := by
  simp only [dfsInitialGhost,pool_records _ _ _ sources raw hs hr]

theorem initial_ready (g : Geometry) (oldWord word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page)
    (hg : g.Valid) (hd : 2 ≤ g.digit) (hi : inp.Valid g oldWord)
    (hb : buildB g word inp = .ok b) (hcap : g.bCapacity ≤ 64)
    (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier)
    (i r p : Nat) (hp : g.ranges = .dfs i r p)
    (hno : DirectJob.firstFailure (distributeA g word
      (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).trace = none) :
    Ready g.finishTopology (dfsInitialGhost g word inp b sources raw) := by
  let route := (analyticalA g word inp.aMain).state
  let pool := aOperational route inp.aTier b.tier
  let leaves := (distributeA g word pool).leaves
  have hshape := DirectJobBridgeShape g oldWord word inp b hg hd hi hb
  have hgeom := (DirectJobFinishTopology g hg hd).1
  have hinv := S12.srt_inv D1Lemmas.engine_valid hgeom hshape
    (SEngProof.engine_valid g.finishTopology hgeom).1
  change S12.SRInv g.finishTopology inp.aMain
    (sRouteWith engineRule g.finishTopology word inp.aMain (engineOps g.finishTopology)) at hinv
  rw [← DirectJobFinishCorrectnessLemmas.route g word inp.aMain (by omega)] at hinv
  have hn : (pool.map Rec.key).Nodup := by
    have he : pool = sPool route inp.aTier [b.tier] := by
      simp only [pool,aOperational,aResidual,sPool,List.flatten_cons,List.flatten_nil,List.append_nil]
    rw [he]
    exact NativeMatchSeparatedReadyProof.pool_nodup g.finishTopology (separatedInputs inp b) route hinv hshape.aNodup
  have hfit : ∀ leaf ∈ leaves, leaf.length ≤ 64 := leaf_fits g word pool i r p hp hno
  have hlayout := onePageLeaves_layout leaves hfit
  have hunique : (leaves.flatten.map Rec.key).Nodup := by
    dsimp only [leaves]
    rw [← DirectJobFinishDistribution g word pool hg hd]
    exact S4b.sLeaves_nodup g.finishTopology word hn
  have ht := (DirectJobBSuccess g word inp b hi.2.2.2.2.1 hb).2.2.2.2.1
  change Ready g.finishTopology ⟨finishInitial b route.main
    (distributeA g word (pageRecords (poolExact sources raw))).leaves,
    onePageLeaves (distributeA g word (pageRecords (poolExact sources raw))).leaves⟩
  rw [pool_records _ _ _ sources raw hs hr]
  refine ⟨hinv.len,fun bucket hm => (hinv.lanes bucket hm).trans
    (DirectJobFinishLemmas.topology_C g),?_,?_,hlayout⟩
  · intro pg
    change (([b.tier] : List (List Rec)).getD pg []).length ≤ 64
    cases pg with
    | zero => exact ht.trans hcap
    | succ pg => simp
  · intro R
    exact hunique.sublist ((D4b.getD_sublist_flatten leaves R).map Rec.key)

end RebuildBound.NativeMatchDirectDfsProof


namespace RebuildBound.NativeMatchDirectDfsProof
open Model Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace Spec.NativeMatchDirectJobTrace

theorem finish_projection (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier) :
    (finishExact g.finishTopology word b.bLanes (dfsInitialGhost g word inp b sources raw)).state =
      (analyticalInsert g word b (analyticalA g word inp.aMain).state.main
        (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves).state := by
  unfold finishExact
  rw [NativeMatchFinishOrchestrationProof.finish_prefix_projection,
    initial_projection g word inp b sources raw hs hr]
  simp only [analyticalInsert,DirectJobFinishLemmas.insert_state,DirectJobFinishLemmas.topology_U]

theorem initial_agreement (bridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (g : Geometry) (word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page)
    (hoff : ∀ e ∈ poolTrace sources raw, ¬e.bad stored) :
    dfsInitialNative stored g word inp b sources raw = dfsInitialGhost g word inp b sources raw := by
  rw [dfsInitialNative,NativeMatchPoolProof.pool_agreement bridge stored sources raw hoff]
  rfl

end RebuildBound.NativeMatchDirectDfsProof


namespace RebuildBound.NativeMatchDirectPlanProof
open Model Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace Spec.NativeMatchDirectJobTrace Spec.NativeMatchDirectPlanTrace
open NativeMatchFinishInvariantProof

theorem initial_agreement (bridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (g : Geometry) (word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page)
    (hoff : ∀ e ∈ poolTrace sources raw, ¬e.bad stored) :
    NativeMatchDirectPlanTrace.initialNative stored g word inp b sources raw =
      NativeMatchDirectPlanTrace.initialGhost g word inp b sources raw := by
  cases hp : g.ranges with
  | direct =>
    simp only [NativeMatchDirectPlanTrace.initialNative,NativeMatchDirectPlanTrace.initialGhost,hp]
    simp only [NativeMatchDirectJobTrace.initialNative,NativeMatchDirectJobTrace.initialGhost,
      NativeMatchPoolProof.pool_agreement bridge stored sources raw hoff]
  | dfs i r p => simpa only [NativeMatchDirectPlanTrace.initialNative,NativeMatchDirectPlanTrace.initialGhost,hp] using NativeMatchDirectDfsProof.initial_agreement bridge stored g word inp b sources raw hoff

theorem initial_projection (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier) :
    (NativeMatchDirectPlanTrace.initialGhost g word inp b sources raw).state =
      finishInitial b (analyticalA g word inp.aMain).state.main
        (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves := by
  cases hp : g.ranges with
  | direct => simpa only [NativeMatchDirectPlanTrace.initialGhost,hp] using NativeMatchDirectInitialProof.initial_projection g word inp b sources raw hp hs hr
  | dfs i r p => simpa only [NativeMatchDirectPlanTrace.initialGhost,hp] using NativeMatchDirectDfsProof.initial_projection g word inp b sources raw hs hr

theorem initial_ready (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (hg : g.Valid) (hd : 2 ≤ g.digit)
    (hi : inp.Valid g oldWord) (hb : buildB g word inp = .ok b) (hcap : g.bCapacity ≤ 64)
    (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier)
    (hno : DirectJob.firstFailure (distributeA g word
      (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).trace = none) :
    Ready g.finishTopology (NativeMatchDirectPlanTrace.initialGhost g word inp b sources raw) := by
  cases hp : g.ranges with
  | direct => simpa only [NativeMatchDirectPlanTrace.initialGhost,hp] using NativeMatchDirectInitialProof.initial_ready g oldWord word inp b sources raw hg hd hi hb hcap hs hr
  | dfs i r p => simpa only [NativeMatchDirectPlanTrace.initialGhost,hp] using NativeMatchDirectDfsProof.initial_ready g oldWord word inp b sources raw hg hd hi hb hcap hs hr i r p hp hno

theorem finish_projection (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier) :
    (finishExact g.finishTopology word b.bLanes
      (NativeMatchDirectPlanTrace.initialGhost g word inp b sources raw)).state = finishState g word inp b := by
  unfold finishExact
  rw [NativeMatchFinishOrchestrationProof.finish_prefix_projection,initial_projection g word inp b sources raw hs hr]
  simp only [finishState,analyticalFinish,analyticalInsert,DirectJobFinishLemmas.insert_state,
    DirectJobFinishLemmas.topology_U]

theorem full_agreement (bridge : NativeMatchLanesBridge_statement)
    (retained : NativeMatchRetained_statement) (classes : NativeMatchClassBridge_statement)
    (stored : LogicalKey → Stored) (g : Geometry) (oldWord word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page) (shedPages tierPages : Nat)
    (hg : g.Valid) (hd : 2 ≤ g.digit) (hi : inp.Valid g oldWord) (hb : buildB g word inp = .ok b)
    (hcap : g.bCapacity ≤ 64) (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier)
    (hdistribute : DirectJob.firstFailure (distributeA g word
      (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).trace = none)
    (hno : DirectJob.firstFailure (analyticalFinish g word b (analyticalA g word inp.aMain).state.main
      (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves).trace = none)
    (hinsCap : g.insertionCapacity ≤ 64*shedPages) (houtCap : g.outputCapacity ≤ 64*tierPages)
    (hoff : ∀ e ∈ NativeMatchDirectPlanTrace.events g word inp b sources raw shedPages tierPages, ¬e.bad stored) :
    NativeMatchDirectPlanTrace.native stored g word inp b sources raw shedPages tierPages =
      ⟨(finishState g word inp b).main,(sDrain (finishState g word inp b)).1 ++
        List.replicate (64*tierPages - (sDrain (finishState g word inp b)).1.length) none⟩ := by
  have hinit := initial_agreement bridge stored g word inp b sources raw
    (fun e he => hoff e (List.mem_append_left _ (List.mem_append_left _ he)))
  have hready := initial_ready g oldWord word inp b sources raw hg hd hi hb hcap hs hr hdistribute
  have hshape := DirectJobBridgeShape g oldWord word inp b hg hd hi hb
  have hbmain : ∀ i < g.finishTopology.U, (b.bLanes.getD i []).length = 64 := by
    intro i hi
    exact (hshape.bLanes _ (D6.getD_mem (by rw [hshape.bLen]; exact hi))).trans
      (DirectJobFinishLemmas.topology_C g)
  have hf := NativeMatchFinishReplayProof.finish_agreement bridge retained stored g.finishTopology word b.bLanes _
    hready hbmain (fun e he => hoff e (List.mem_append_left _ (List.mem_append_right _ he)))
  obtain ⟨hins,hfirst,houtput⟩ := NativeMatchDirectDrainProof.finish_fits g word b
    (analyticalA g word inp.aMain).state.main
    (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves hno
  have hdr := NativeMatchDrainReplayProof.drain_agreement classes stored shedPages tierPages
    (finishState g word inp b) (hins.trans hinsCap) (hfirst.trans houtCap) (houtput.trans houtCap)
    (NativeMatchDirectDrainProof.actual_disjoint g oldWord word inp b hg hd hi hb)
    (fun e he => hoff e (List.mem_append_right _ he))
  simp only [NativeMatchDirectPlanTrace.native,hinit,hf,finish_projection g word inp b sources raw hs hr,hdr]

end RebuildBound.NativeMatchDirectPlanProof


namespace RebuildBound.NativeMatchPrefixProducerProof
open Model Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchPrefixProducer NativeMatchDenseTraceProof NativeMatchPrefixProof

theorem singleton_run (compare : DirectMasks.Comparison) (state units : List Bucket) :
    DirectMaskBuckets.run compare (state.map (fun b => [b])) (units.map (fun b => [b])) =
      (DirectMasks.run compare state units).map (fun b => [b]) := by
  induction units generalizing state with
  | nil => rfl
  | cons fresh units ih =>
    simp only [List.map_cons,DirectMaskBuckets.run,DirectMasks.run,List.foldl_cons] at *
    have hs : DirectMaskBuckets.step compare (state.map (fun b => [b])) [fresh] =
        (DirectMasks.step compare state fresh).map (fun b => [b]) := by
      simp only [DirectMaskBuckets.step,DirectMaskBuckets.pair,DirectMasks.step,List.map_map,
        List.map_append,List.map_cons,List.map_nil,Function.comp_def,List.foldl_cons,List.foldl_nil]
    rw [hs]
    exact ih _

theorem singleton_flatten {α : Type} (xs : List α) : (xs.map (fun x => [x])).flatten = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.map_cons,List.flatten_cons,List.singleton_append] using congrArg (List.cons x) ih

theorem index_run (compare : DirectMasks.Comparison) (units : List Bucket) :
    DirectMaskIndex.runRange compare 1 units 0 (DirectMaskIndex.pairs 1 units.length) =
      DirectMasks.run compare [] units := by
  have h := DirectMaskIndexComplete compare 1 (units.map (fun b => [b])) (by simp)
  rw [DirectMaskSweepComplete] at h
  have hs := singleton_run compare [] units
  simp only [List.map_nil] at hs
  rw [hs] at h
  simpa only [singleton_flatten,List.length_map] using h

theorem decode_pages (units : List Bucket) : DirectMask64.buckets (data units) (masks units) =
    (pages units).map Page.bucket := by
  apply List.ext_getElem (by simp [DirectMask64.buckets,masks])
  intro i hi hj
  have hlen : i < (pages units).length := by simpa [masks,DirectMask64.buckets] using hi
  simp only [DirectMask64.buckets,List.getElem_mapIdx,masks,List.getElem_map,data,
    List.getD_eq_getElem _ _ hlen,Page.bucket]

theorem decode_units (units : List Bucket) (hwidth : ∀ bucket ∈ units, bucket.length = 64) :
    DirectMask64.buckets (data units) (masks units) = units := by
  rw [decode_pages]
  simp only [pages,List.map_map]
  calc
    _ = units.map id := by
      apply List.map_congr_left
      intro bucket hb
      exact NativeMatchPoolProof.ofBucket_decode bucket (hwidth bucket hb)
    _ = units := List.map_id units

theorem masked_agreement (bridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (units : List Bucket)
    (hwidth : ∀ bucket ∈ units, bucket.length = 64)
    (hoff : ∀ e ∈ events units, ¬e.bad stored) :
    masked stored units = DirectMasks.run exactCompare [] units := by
  change masked stored units = DirectMasks.run (fun a b => a == b) [] units
  have h := range_agreement bridge stored (data units) 1 (masks units) 0
    (DirectMaskIndex.pairs 1 units.length) (by simpa only [events,Nat.sub_zero,← List.range_eq_range'] using hoff)
  simpa only [masked,← List.range_eq_range',Nat.sub_zero,decode_units units hwidth,index_run] using h

def padUnit (bucket : Bucket) : Bucket := bucket ++ List.replicate (64-bucket.length) none

theorem pad_recs (bucket : Bucket) : (padUnit bucket).recs = bucket.recs := by
  simp [padUnit,Bucket.recs]

theorem pair_pad (compare : DirectMasks.Comparison) (fresh older : Bucket) :
    DirectMasks.pair compare (padUnit fresh) (padUnit older) =
      padUnit (DirectMasks.pair compare fresh older) := by
  simp [DirectMasks.pair,padUnit,Bucket.recs]

theorem run_pad (compare : DirectMasks.Comparison) (state units : List Bucket) :
    DirectMasks.run compare (state.map padUnit) (units.map padUnit) =
      (DirectMasks.run compare state units).map padUnit := by
  induction units generalizing state with
  | nil => rfl
  | cons fresh units ih =>
    simp only [List.map_cons,DirectMasks.run,List.foldl_cons] at *
    have hs : DirectMasks.step compare (state.map padUnit) (padUnit fresh) =
        (DirectMasks.step compare state fresh).map padUnit := by
      simp only [DirectMasks.step,List.map_map,List.map_append,List.map_cons,List.map_nil,Function.comp_def,pair_pad]
    rw [hs]
    exact ih _

theorem records_pad (units : List Bucket) : DirectMasks.records (units.map padUnit) = DirectMasks.records units := by
  simp only [DirectMasks.records,List.flatMap_map,pad_recs]

theorem chunks_pad (units : List Bucket) : DirectMaskedRecords.chunks (units.map padUnit) =
    DirectMaskedRecords.chunks units := by
  simp only [DirectMaskedRecords.chunks,List.map_map,Function.comp_def,pad_recs]

theorem decode_padded (units : List Bucket) (hfit : ∀ bucket ∈ units, bucket.length ≤ 64) :
    DirectMask64.buckets (data units) (masks units) = units.map padUnit := by
  rw [decode_pages]
  simp only [pages,List.map_map]
  apply List.map_congr_left
  intro bucket hb
  change (Page.ofBucket bucket).bucket = padUnit bucket
  rw [NativeMatchDenseTraceProof.pageOfBucket_lanes,NativeMatchDenseTraceProof.indexed_lanes,
    List.take_of_length_le (hfit bucket hb)]
  rfl

theorem masked_padded_agreement (bridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (units : List Bucket)
    (hfit : ∀ bucket ∈ units, bucket.length ≤ 64)
    (hoff : ∀ e ∈ events units, ¬e.bad stored) :
    masked stored units = (DirectMasks.run Model.DirectJob.exactCompare [] units).map padUnit := by
  change masked stored units = (DirectMasks.run (fun a b => a == b) [] units).map padUnit
  have h := range_agreement bridge stored (data units) 1 (masks units) 0
    (DirectMaskIndex.pairs 1 units.length) (by simpa only [events,Nat.sub_zero,← List.range_eq_range'] using hoff)
  have hp := run_pad (fun a b => a == b) [] units
  simp only [List.map_nil] at hp
  have hi := index_run (fun a b => a == b) (units.map padUnit)
  simp only [List.length_map] at hi
  simpa only [masked,← List.range_eq_range',Nat.sub_zero,decode_padded units hfit,hi,hp] using h

theorem producer_agreement (bridge : NativeMatchLanesBridge_statement)
    (stored : LogicalKey → Stored) (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (hwidth : ∀ bucket ∈ inp.units, bucket.length ≤ 64)
    (hunique : ∀ bucket ∈ inp.units, (bucket.recs.map Rec.key).Nodup)
    (hoff : ∀ e ∈ events inp.units, ¬e.bad stored) :
    nativeBuildB stored g word inp = buildB g word inp := by
  have hm := masked_padded_agreement bridge stored inp.units hwidth hoff
  have hw := DirectMasksWinners exactCompare inp.units (fun _ _ => rfl) hunique
  simp only [nativeBuildB,hm,records_pad,chunks_pad,hw,buildB,bRemaining,bHomes,bChunks,
    DirectRecords.restore,DirectJob.Inputs.bRecords]
  rfl

end RebuildBound.NativeMatchPrefixProducerProof


