import RebuildBound.Spec.NativeMatch.HierarchyCounts
import RebuildBound.Proofs.NativeMatchHierarchy
import RebuildBound.Proofs.NativeMatchCounts
import RebuildBound.Proofs.NativeMatchOrdinals
import RebuildBound.Proofs.ApiLegal
import RebuildBound.Proofs.ConfigurationFamilyProbability.Facts
import RebuildBound.Proofs.AdaptiveCompose.Rows
set_option maxRecDepth 4000

namespace RebuildBound.Spec.NativeMatchJobAllocation
open Model Model.DirectJob

def directCharge (g : Geometry) (rawPages sourcePages shedPages tierPages recA recB : Nat) : Nat :=
  min (sourcePages * min recA (64*rawPages)) (rawPages * min recB (64*sourcePages)) +
  (min recA (64*g.outputHomes) + (min recA (64*rawPages) + min recB (64*sourcePages))) +
  (tierPages * min (64*shedPages) recB + shedPages * min (64*tierPages) recA)

end RebuildBound.Spec.NativeMatchJobAllocation

namespace RebuildBound.NativeMatchDirectCount
open Model Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace Spec.NativeMatchDirectJobTrace Spec.NativeMatchJobAllocation
open NativeMatchPopulationCount NativeMatchPoolCount NativeMatchLeftoverCount
open NativeMatchFinishWeight NativeMatchFinishInvariantProof NativeMatchDirectInitialProof

theorem winners_length (records : List Rec) : (DirectPrefix.winners records).length ≤ records.length := by
  induction records with
  | nil => simp [DirectPrefix.winners]
  | cons record records ih =>
    simp only [DirectPrefix.winners]
    split <;> simp only [List.length_cons] <;> omega

theorem b_population (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (hu : ∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup)
    (hb : buildB g word inp = .ok b) :
    (separatedInputs inp b).bAll.length ≤ inp.bRecords.length := by
  rw [DirectJobBridgeLemmas.bAll b inp (DirectJobBridgeLemmas.bMain_bounds g word inp b hu hb).2.1,
    (DirectJobBSuccess g word inp b hu hb).1.length_eq]
  exact winners_length _

theorem raw_population (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (raw : List Page) (hg : g.Valid) (hd : 2 ≤ g.digit) (hi : inp.Valid g oldWord)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier) :
    (pageRecords raw).length ≤ inp.aRecords.length := by
  have hp := ((NativeMatchDirectRouteProof.route_invariant g oldWord word inp hg hd hi).perm.append_right inp.aTier).length_eq
  rw [hr]
  simp only [aResidual,List.length_append,Inputs.aRecords] at hp ⊢
  omega

theorem pool_population (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (hg : g.Valid) (hd : 2 ≤ g.digit)
    (hi : inp.Valid g oldWord) (hb : buildB g word inp = .ok b)
    (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier)
    (recA recB : Nat) (hA : inp.aRecords.length ≤ recA) (hB : inp.bRecords.length ≤ recB) :
    (pageRecords raw).length ≤ min recA (64*raw.length) ∧
    b.tier.length ≤ min recB (64*sources.length) ∧
    (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier).length ≤
      min recA (64*raw.length) := by
  have ha := le_min ((raw_population g oldWord word inp raw hg hd hi hr).trans hA) (pages_count_le raw)
  have hbp := (b_population g word inp b hi.2.2.2.2.1 hb).trans hB
  have hb' : b.tier.length ≤ recB := by
    rw [DirectJobBridgeLemmas.bAll b inp (DirectJobBridgeLemmas.bMain_bounds g word inp b hi.2.2.2.2.1 hb).2.1] at hbp
    simp only [List.length_append] at hbp
    omega
  refine ⟨ha,le_min hb' (by rw [← hs]; exact pages_count_le sources),?_⟩
  have hfilter : (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier).length ≤
      (aResidual (analyticalA g word inp.aMain).state inp.aTier).length := List.length_filter_le _ _
  rw [← hr] at hfilter
  exact hfilter.trans ha

theorem pool_allocated (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (hg : g.Valid) (hd : 2 ≤ g.digit)
    (hi : inp.Valid g oldWord) (hb : buildB g word inp = .ok b)
    (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier)
    (recA recB : Nat) (hA : inp.aRecords.length ≤ recA) (hB : inp.bRecords.length ≤ recB) :
    weight 4 ((poolTrace sources raw).map Event.comparison) ≤
      64^4 * min (sources.length*min recA (64*raw.length)) (raw.length*min recB (64*sources.length)) := by
  obtain ⟨ha,hb',_⟩ := pool_population g oldWord word inp b sources raw hg hd hi hb hs hr recA recB hA hB
  have hm := pool_min sources raw
  rw [hs] at hm
  exact (pool_weight sources raw).trans (Nat.mul_le_mul_left _
    (hm.trans (min_le_min (Nat.mul_le_mul_left _ ha) (Nat.mul_le_mul_left _ hb'))))

/-- Generic grouped writer bound, instantiated below by actual direct or DFS
initialization. The state is the existing exact distributed reference. -/
theorem finish_allocated (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (hg : g.Valid) (hd : 2 ≤ g.digit)
    (hi : inp.Valid g oldWord) (hb : buildB g word inp = .ok b)
    (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier)
    (groups : List (List Page))
    (hlayout : groups.map pageRecords = (distributeA g word
      (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves)
    (hready : Ready g.finishTopology ⟨finishInitial b (analyticalA g word inp.aMain).state.main
      (groups.map pageRecords),groups⟩)
    (recA recB : Nat) (hA : inp.aRecords.length ≤ recA) (hB : inp.bRecords.length ≤ recB) :
    weight 4 ((finishEvents g.finishTopology word b.bLanes
      ⟨finishInitial b (analyticalA g word inp.aMain).state.main (groups.map pageRecords),groups⟩).map Event.comparison) ≤
      64^4 * (min recA (64*g.outputHomes) + (min recA (64*raw.length) + min recB (64*sources.length))) := by
  let route := (analyticalA g word inp.aMain).state
  let pool := aOperational route inp.aTier b.tier
  have hshape := DirectJobBridgeShape g oldWord word inp b hg hd hi hb
  have hg' := (DirectJobFinishTopology g hg hd).1
  have hinv := S12.srt_inv D1Lemmas.engine_valid hg' hshape
    (SEngProof.engine_valid g.finishTopology hg').1
  change S12.SRInv g.finishTopology inp.aMain
    (sRouteWith engineRule g.finishTopology word inp.aMain (engineOps g.finishTopology)) at hinv
  rw [← DirectJobFinishCorrectnessLemmas.route g word inp.aMain (by omega)] at hinv
  have hl : groups.map pageRecords = sLeaves g.finishTopology word pool :=
    hlayout.trans (DirectJobFinishDistribution g word pool hg hd).symm
  have hw := finish_population_weight hg' word (separatedInputs inp b) route.main groups hready
    (by rw [hl]; simp [sLeaves]) (by
      rw [hl]
      intro R x hx
      by_cases hR : R < g.finishTopology.ranges
      · have he : (sLeaves g.finishTopology word pool).getD R [] =
            pool.filter (fun x => sRange g.finishTopology word x == R) := by
          simp [sLeaves,List.getD_eq_getElem?_getD,hR]
        rw [he,List.mem_filter] at hx
        simpa using hx.2
      · simp [sLeaves,List.getD_eq_getElem?_getD,hR] at hx) hshape.bHome
  have hmain := (main_and_pool_populations g.finishTopology (separatedInputs inp b) route hinv).1.trans hA
  have hcap := main_capacity g.finishTopology (separatedInputs inp b) route hinv
  rw [(DirectJobFinishTopology g hg hd).2.2.1,DirectJobFinishLemmas.topology_C] at hcap
  have hm : (route.main.flatMap Bucket.recs).length ≤ min recA (64*g.outputHomes) :=
    le_min hmain (by simpa only [Nat.mul_comm] using hcap)
  obtain ⟨_,hbt,hpool⟩ := pool_population g oldWord word inp b sources raw hg hd hi hb hs hr recA recB hA hB
  have hleaves : (groups.map pageRecords).flatten.length ≤ min recA (64*raw.length) := by
    rw [hl]
    exact (leaves_count g.finishTopology word pool).trans hpool
  apply hw.trans
  apply Nat.mul_le_mul_left
  simpa only [separatedInputs,List.flatten_cons,List.flatten_nil,List.append_nil] using
    Nat.add_le_add hm (Nat.add_le_add hleaves hbt)

theorem drain_allocated (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (hg : g.Valid) (hd : 2 ≤ g.digit) (hi : inp.Valid g oldWord)
    (hb : buildB g word inp = .ok b) (shedPages tierPages recA recB : Nat)
    (hA : inp.aRecords.length ≤ recA) (hB : inp.bRecords.length ≤ recB) :
    weight 4 ((NativeMatchJobTrace.drainEvents shedPages tierPages (finishState g word inp b)).map Event.comparison) ≤
      64^4 * (tierPages*min (64*shedPages) recB + shedPages*min (64*tierPages) recA) := by
  have hshape := DirectJobBridgeShape g oldWord word inp b hg hd hi hb
  have hg' := (DirectJobFinishTopology g hg hd).1
  have hsched := SEngProof.engine_valid g.finishTopology hg'
  have hA' : (separatedInputs inp b).aAll.length ≤ recA := hA
  have hB' := (b_population g word inp b hi.2.2.2.2.1 hb).trans hB
  have ha := NativeMatchFinalDrainCount.final_leaf_population engineRule g.finishTopology oldWord word
    (separatedInputs inp b) (engineOps g.finishTopology) D1Lemmas.engine_valid hg' hshape hsched.1 recA hA'
  have hb' := NativeMatchFinalDrainCount.final_ins_population engineRule g.finishTopology oldWord word
    (separatedInputs inp b) (engineOps g.finishTopology) D1Lemmas.engine_valid hg' hshape hsched recB hB'
  have he := (DirectJobFinishCorrectnessLemmas.output g word inp b hg hd).1
  change finishState g word inp b = _ at he
  rw [← he] at ha hb'
  exact NativeMatchDrainCount.drain_population_weight shedPages tierPages _ recA recB ha hb'

end RebuildBound.NativeMatchDirectCount

namespace RebuildBound.NativeMatchDirectCount
open Model Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace Spec.NativeMatchDirectJobTrace Spec.NativeMatchJobAllocation
open NativeMatchDirectInitialProof NativeMatchFinishInvariantProof

theorem direct_allocated (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (hg : g.Valid) (hd : 2 ≤ g.digit)
    (hi : inp.Valid g oldWord) (hb : buildB g word inp = .ok b)
    (hp : g.ranges = .direct) (hcap : g.bCapacity ≤ 64)
    (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier)
    (shedPages tierPages recA recB : Nat)
    (hA : inp.aRecords.length ≤ recA) (hB : inp.bRecords.length ≤ recB) :
    weight 4 ((fullEvents g word inp b sources raw shedPages tierPages).map Event.comparison) ≤
      64^4 * directCharge g raw.length sources.length shedPages tierPages recA recB := by
  let groups := [poolExact sources raw]
  have hlayout : groups.map pageRecords = (distributeA g word
      (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves := by
    simp only [groups,List.map_cons,List.map_nil,distributeA,hp,
      pool_records _ _ _ sources raw hs hr]
  have hready : Ready g.finishTopology ⟨finishInitial b (analyticalA g word inp.aMain).state.main
      (groups.map pageRecords),groups⟩ :=
    initial_ready g oldWord word inp b sources raw hg hd hi hb hcap hs hr
  have hp' := pool_allocated g oldWord word inp b sources raw hg hd hi hb hs hr recA recB hA hB
  have hf := finish_allocated g oldWord word inp b sources raw hg hd hi hb hs hr groups hlayout hready recA recB hA hB
  have hd' := drain_allocated g oldWord word inp b hg hd hi hb shedPages tierPages recA recB hA hB
  simpa only [fullEvents,events,initialGhost,groups,List.map_cons,List.map_nil,
    directCharge,List.map_append,weight,List.sum_append,Nat.mul_add] using
      Nat.add_le_add (Nat.add_le_add hp' hf) hd'

end RebuildBound.NativeMatchDirectCount
namespace RebuildBound.NativeMatchDirectCount
open Model Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open Spec.NativeMatchJobTrace Spec.NativeMatchDirectJobTrace Spec.NativeMatchJobAllocation
open NativeMatchFinishInvariantProof

theorem plan_allocated (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (hg : g.Valid) (hd : 2 ≤ g.digit)
    (hi : inp.Valid g oldWord) (hb : buildB g word inp = .ok b) (hcap : g.bCapacity ≤ 64)
    (hs : pageRecords sources = b.tier)
    (hr : pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier)
    (hdistribute : DirectJob.firstFailure (distributeA g word
      (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).trace = none)
    (shedPages tierPages recA recB : Nat)
    (hA : inp.aRecords.length ≤ recA) (hB : inp.bRecords.length ≤ recB) :
    weight 4 ((NativeMatchDirectPlanTrace.events g word inp b sources raw shedPages tierPages).map Event.comparison) ≤
      64^4 * directCharge g raw.length sources.length shedPages tierPages recA recB := by
  let ghost := NativeMatchDirectPlanTrace.initialGhost g word inp b sources raw
  have hready := NativeMatchDirectPlanProof.initial_ready g oldWord word inp b sources raw hg hd hi hb hcap hs hr hdistribute
  have hstate := NativeMatchDirectPlanProof.initial_projection g word inp b sources raw hs hr
  have hlayout : ghost.groups.map pageRecords = (distributeA g word
      (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves :=
    hready.layout.trans (congrArg SFin.leaves hstate)
  have he : ghost = ⟨finishInitial b (analyticalA g word inp.aMain).state.main
      (ghost.groups.map pageRecords),ghost.groups⟩ := by
    have h : ghost.state = finishInitial b (analyticalA g word inp.aMain).state.main
        (ghost.groups.map pageRecords) := by rw [hlayout]; exact hstate
    exact congrArg (fun state => (⟨state,ghost.groups⟩ : FinishGhost)) h
  have hrdy : Ready g.finishTopology ⟨finishInitial b (analyticalA g word inp.aMain).state.main
      (ghost.groups.map pageRecords),ghost.groups⟩ := by rw [← he]; exact hready
  have hf := finish_allocated g oldWord word inp b sources raw hg hd hi hb hs hr ghost.groups hlayout hrdy recA recB hA hB
  rw [← he] at hf
  have hp := pool_allocated g oldWord word inp b sources raw hg hd hi hb hs hr recA recB hA hB
  have hd' := drain_allocated g oldWord word inp b hg hd hi hb shedPages tierPages recA recB hA hB
  simpa only [NativeMatchDirectPlanTrace.events,directCharge,List.map_append,weight,List.sum_append,Nat.mul_add] using
    Nat.add_le_add (Nat.add_le_add hp hf) hd'

end RebuildBound.NativeMatchDirectCount
namespace RebuildBound.Spec.NativeMatchJobAllocation
open Model Model.DirectJob NativeMatchHierarchy

def directAllocatedCharge (g : Geometry) (recA recB : Nat) : Nat :=
  directCharge g (g.aTopology.k*pageAllocation g.routeCapacity +
    (if 1 < g.aTopology.r then pageAllocation g.radixCapacity else 0) + pageAllocation g.aTierCapacity)
    1 (pageAllocation g.insertionCapacity) (pageAllocation g.outputCapacity) recA recB

end RebuildBound.Spec.NativeMatchJobAllocation

namespace RebuildBound.NativeMatchDirectEventsCount
open Model Model.DirectJob Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatchTrace
open Spec.NativeMatchHierarchy Spec.NativeMatchJobAllocation

theorem pageAllocation_covers (slots : Nat) : slots ≤ 64*pageAllocation slots := by
  unfold pageAllocation
  omega

theorem prefix_weight (units : List Bucket) (count : Nat) (hcount : units.length ≤ count) :
    weight 4 ((NativeMatchPrefixProducer.events units).map Event.comparison) ≤
      64^4*(64*(count*(count-1)/2)) := by
  have hw := NativeMatchPrefixProof.trace_weight (NativeMatchPrefixProducer.data units) 1
    (NativeMatchPrefixProducer.masks units) (List.range (DirectMaskIndex.pairs 1 units.length))
  have hm := NativeMatchPrefixProof.prefixSMin_le (NativeMatchPrefixProducer.data units) 1
    (NativeMatchPrefixProducer.masks units) (List.range (DirectMaskIndex.pairs 1 units.length))
  simp only [List.length_range,DirectMaskIndex.pairs,Nat.one_mul] at hm
  have ht : units.length*(units.length-1)/2 ≤ count*(count-1)/2 :=
    Nat.div_le_div_right (Nat.mul_le_mul hcount (Nat.sub_le_sub_right hcount 1))
  apply hw.trans
  apply Nat.mul_le_mul_left
  simpa only [DirectMaskIndex.pairs,Nat.one_mul] using hm.trans (Nat.mul_le_mul_left _ ht)

set_option maxHeartbeats 1000000 in
/-- Prefix dedup and every later matching site of a successful direct-job
publication, counted from the actual phase states and public page allocation. -/
theorem published_weight (g : Geometry) (oldWord word : LogicalKey → Nat)
    (prev : Output) (units : List Bucket) (out : Output)
    (hpub : runJob g oldWord word (adopt prev units) = .published out)
    (hd : 2 ≤ g.digit) (hBcap : g.bCapacity ≤ 64)
    (hprev : prev.tier.length ≤ g.aTierCapacity)
    (unitCount recA recB : Nat) (hunits : units.length ≤ unitCount)
    (hA : prev.records.length ≤ recA) (hB : (DirectMasks.records units).length ≤ recB) :
    weight 4 ((directEvents g word (adopt prev units) prev).map Event.comparison) ≤
      64^4*(64*(unitCount*(unitCount-1)/2) + directAllocatedCharge g recA recB) := by
  let inp := adopt prev units
  obtain ⟨hg,hi,ha,b,hb,hdist,_,_⟩ := NativeMatchDirectSuccess.later g oldWord word inp out hd hpub
  have ht := (DirectJobBSuccess g word inp b hi.2.2.2.2.1 hb).2.2.2.2.1
  have hs : pageRecords (directSources b) = b.tier := by
    simpa only [directSources,pageRecords,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
      NativeMatchPageProof.ofRecords_recs b.tier (ht.trans hBcap)
  have hraw : pageRecords (directRaw g word inp prev) =
      aResidual (analyticalA g word inp.aMain).state inp.aTier := by
    apply NativeMatchDirectInitialProof.allocatedRaw_projection g word inp _ (by omega) ha
      (pageAllocation g.routeCapacity) (pageAllocation g.radixCapacity)
      (bucketPages (pageAllocation g.aTierCapacity) prev.tier)
      (pageAllocation_covers _) (fun _ => pageAllocation_covers _)
    rw [NativeMatchDenseTraceProof.bucketPages_records,List.take_of_length_le
      (hprev.trans (pageAllocation_covers _))]
    rfl
  have hrawLen : (directRaw g word inp prev).length =
      g.aTopology.k*pageAllocation g.routeCapacity +
      (if 1 < g.aTopology.r then pageAllocation g.radixCapacity else 0) + pageAllocation g.aTierCapacity := by
    rw [directRaw,NativeMatchDirectRouteProof.allocatedRaw_length g oldWord word inp hg hd hi,
      NativeMatchDrainLayoutProof.bucketPages_length]
  have hw := NativeMatchDirectCount.plan_allocated g oldWord word inp b (directSources b)
    (directRaw g word inp prev) hg hd hi hb hBcap hs hraw hdist
    (pageAllocation g.insertionCapacity) (pageAllocation g.outputCapacity) recA recB hA hB
  rw [hrawLen,show (directSources b).length=1 from rfl] at hw
  have hp := prefix_weight units unitCount hunits
  have hu : inp.units = units := rfl
  have hdne : g.digit ≠ 1 := by omega
  change weight 4 ((directEvents g word inp prev).map Event.comparison) ≤ _
  simpa only [directEvents,hb,hdne,ite_false,hu,List.map_append,weight,List.sum_append,
    Nat.mul_add,directAllocatedCharge] using Nat.add_le_add hp hw

end RebuildBound.NativeMatchDirectEventsCount

namespace RebuildBound.NativeMatchDirectEventsCount
open Model Model.DirectJob Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchHierarchy

theorem first_digit_weight (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (prev : Output) (hd : g.digit = 1) (unitCount : Nat) (hu : inp.units.length ≤ unitCount) :
    weight 4 ((directEvents g word inp prev).map Event.comparison) ≤
      64^4*(64*(unitCount*(unitCount-1)/2)) := by
  have hp := prefix_weight inp.units unitCount hu
  cases hb : buildB g word inp with
  | error e => simpa only [directEvents,hb,List.append_nil] using hp
  | ok b => simpa only [directEvents,hb,hd,ite_true,List.append_nil] using hp

end RebuildBound.NativeMatchDirectEventsCount
namespace RebuildBound.NativeMatchRecordCount
open Model Model.Hierarchy Model.Online Spec HierarchyInvariantProof

theorem length_of_key_card (records : List Rec) (n : Nat)
    (hunique : (records.map Rec.key).Nodup)
    (hcard : (records.map Rec.key).toFinset.card ≤ n) : records.length ≤ n := by
  rwa [List.toFinset_card_of_nodup hunique, List.length_map] at hcard

theorem low_records (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    {N : Nat} {tr : Trace} (htrace : TracePremises geo.cfg N tr)
    (words : Words) (level ordinal : Nat) (h1 : 1 ≤ level) (hL : level < geo.cfg.levels)
    (ho : geo.cfg.seed level < ordinal) :
    (table geo.cfg geo.shapes tr words level ordinal).records.length ≤
      geo.cfg.load * (geo.cfg.digitAt level ordinal * geo.cfg.carry level) := by
  have h := (lowFor geo F htrace words level h1 hL ordinal ho).1
  exact length_of_key_card _ _ h.nodup h.card

theorem previous_records (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    {N : Nat} {tr : Trace} (htrace : TracePremises geo.cfg N tr)
    (words : Words) (level ordinal : Nat) (h1 : 1 ≤ level) (hL : level < geo.cfg.levels)
    (ho : geo.cfg.seed level < ordinal) :
    (prevInFor geo tr words level ordinal).length ≤
      geo.cfg.load * ((geo.cfg.digitAt level ordinal - 1) * geo.cfg.carry level) := by
  unfold prevInFor
  split_ifs with hd
  · simp
  · have hp : 2 ≤ geo.cfg.digitAt level ordinal := by
      have := digit_pos (geo.cfg.fanout level) ordinal
      change 1 ≤ geo.cfg.digitAt level ordinal at this
      omega
    have hseed : geo.cfg.fanout level ∣ geo.cfg.seed level := ⟨_, F.seed level h1 hL⟩
    have hprev := low_records geo F htrace words level (ordinal - 1) h1 hL
      (pred_gt hseed ho hp)
    obtain ⟨hf, _, _⟩ := F.fan level h1 hL
    have he : geo.cfg.digitAt level (ordinal - 1) = geo.cfg.digitAt level ordinal - 1 :=
      digit_pred (by omega) hp
    rw [he] at hprev
    exact hprev

theorem carry_records (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    {N : Nat} {tr : Trace} (htrace : TracePremises geo.cfg N tr)
    (words : Words) (level ordinal : Nat) (h2 : 2 ≤ level) (hL : level ≤ geo.cfg.levels)
    (ho : geo.cfg.seed level < ordinal) :
    (carryOf geo.cfg geo.shapes tr words level ordinal).records.length ≤
      geo.cfg.load * geo.cfg.carry level := by
  obtain ⟨hf, _, _⟩ := F.fan (level - 1) (by omega) (by omega)
  have hseed : geo.cfg.seed (level - 1) < ordinal * geo.cfg.fanout (level - 1) := by
    have hs := F.seed (level - 1) (by omega) (by omega)
    rw [show level - 1 + 1 = level by omega] at hs
    rw [hs, Nat.mul_comm ordinal]
    exact Nat.mul_lt_mul_of_pos_left ho (by omega)
  have h := (lowFor geo F htrace words (level - 1) (by omega) (by omega) _ hseed).1
  have hc := carry_ofFor F h2 hL (by omega) h
  exact length_of_key_card _ _ hc.nodup hc.card

theorem source_records (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct)
    {N : Nat} {tr : Trace} (htrace : TracePremises geo.cfg N tr)
    (words : Words) (level ordinal : Nat) (h1 : 1 ≤ level) (hL : level ≤ geo.cfg.levels)
    (ho : geo.cfg.seed level < ordinal) :
    (srcBFor geo tr words level ordinal).length ≤ geo.cfg.load * geo.cfg.carry level := by
  unfold srcBFor
  split_ifs with he
  · subst level
    exact (prefix_sublist _).length_le.trans (by simpa [Config.carry] using htrace.load (ordinal - geo.cfg.seed 1 - 1))
  · exact carry_records geo F htrace words level ordinal (by omega) hL ho

/-- Actual finite requester runs supply their own provenance witness. This bound
uses chronological input rate, not a fixed user-key universe or capacity success. -/
theorem finite_run_sources (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : OnlineGeom) (run : OnlineBatch.BatchRun)
    (halign : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hentries : 0 < g.unitEntries) (hi : (run.init.map Rec.key).Nodup)
    (words : Words) (level ordinal : Nat) (h1 : 1 ≤ level) (hL : level < geo.cfg.levels)
    (ho : geo.cfg.seed level < ordinal) :
    (prevInFor geo (OnlineBatch.traceOf g run) words level ordinal).length ≤
      geo.cfg.load * ((geo.cfg.digitAt level ordinal - 1) * geo.cfg.carry level) ∧
    (srcBFor geo (OnlineBatch.traceOf g run) words level ordinal).length ≤
      geo.cfg.load * geo.cfg.carry level := by
  obtain ⟨N, _, ht⟩ := ApiStructuralProof.run_premises geo.cfg g run halign hentries hi
  have F := HierarchySemanticsProof.lower hgeo.1
  exact ⟨previous_records geo F ht words level ordinal h1 hL ho,
    source_records geo F ht words level ordinal h1 hL.le ho⟩
end RebuildBound.NativeMatchRecordCount
namespace RebuildBound.NativeMatchHierarchyLocalCount
open Model Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open HierarchyInvariantProof HierarchyCoveringProof NativeMatchPhysicalInputs

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

set_option maxHeartbeats 1000000 in
/-- All per-job shape and population hypotheses come from the actual
unconditional hierarchy state. The public incoming-capacity link is geometric
arithmetic and is checked separately on the finite production family. -/
theorem separated_allocated (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    {N : Nat} (tr : Trace) (hT : TracePremises geo.cfg N tr) (words : Words)
    (level ordinal : Nat) (hj : JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs)
    (hW : WithinHorizon geo.cfg (.ordinary level ordinal)) (h2 : 2 ≤ level)
    (hd2 : 2 ≤ geo.cfg.digitAt level ordinal) (hno : ¬Fails geo.cfg geo.shapes tr words)
    (hlink : incomingCapacity geo.cfg geo.shapes level ≤
      (geo.shapes.sep level (geo.cfg.digitAt level ordinal)).bTierPages *
      (geo.shapes.sep level (geo.cfg.digitAt level ordinal)).C) :
    let g := geo.shapes.sep level (geo.cfg.digitAt level ordinal)
    weight 4 ((separatedEvents engineRule g (jobWord geo.cfg words level ordinal)
      (sepInputsAt geo.cfg geo.shapes tr words level ordinal) (engineOps g)
      (bucketPages g.aTierPages (table geo.cfg geo.shapes tr words level (ordinal-1)).tier)).map Event.comparison) ≤
    64^4 * NativeMatchJobAllocation.separatedCharge g
      (geo.cfg.load*((geo.cfg.digitAt level ordinal-1)*geo.cfg.carry level))
      (geo.cfg.load*geo.cfg.carry level) := by
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
      page.length ≤ g.C := by
    rw [hC]
    change ∀ page ∈ pagesOf _ _ _, page.length ≤ 64
    rw [hg,hC]
    exact pagesOf_fits _ _ _ (by simpa only [Nat.mul_comm] using hb)
  have hA : (sepInputsAt geo.cfg geo.shapes tr words level ordinal).aAll.length ≤
      geo.cfg.load*((geo.cfg.digitAt level ordinal-1)*geo.cfg.carry level) := by
    rw [sepAt_aAllFor geo]
    have h := NativeMatchRecordCount.previous_records geo LF hT words level ordinal h1 hL ho
    simpa only [prevInFor,show geo.cfg.digitAt level ordinal ≠ 1 by omega,ite_false] using h
  have hB : (sepInputsAt geo.cfg geo.shapes tr words level ordinal).bAll.length ≤
      geo.cfg.load*geo.cfg.carry level := by
    rw [sepAt_bAllFor geo words level ordinal (by rw [hg]; exact hP)]
    exact NativeMatchRecordCount.carry_records geo LF hT words level ordinal h2 hL.le ho
  have hn := sep_no_failure geo.cfg geo.shapes tr words level ordinal hj hW h2 (by omega) hno
  rw [hg] at hn ⊢
  exact NativeMatchSeparatedAllocationProof.separated_allocated engineRule g _ _ _ _
    D1Lemmas.engine_valid hvalid hC hs (SEngProof.engine_valid g hvalid) hn _ hraw
    (NativeMatchDrainLayoutProof.bucketPages_length _ _) hpages _ _ hA hB

end RebuildBound.NativeMatchHierarchyLocalCount

namespace RebuildBound.NativeMatchHierarchyLocalCount
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchJobTrace
open HierarchyInvariantProof HierarchyCoveringProof NativeMatchPhysicalInputs

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
/-- The API's already-proved unconditional correctness and live-population
contracts supply the top input population. No numeric key-universe bound is
compared with storage capacity. -/
theorem top_allocated (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (c : Api.Codec) (g : OnlineGeom) (run : OnlineBatch.BatchRun)
    (S : Schedule) (requests : List Api.Request)
    (hcorrect : ApiRunCorrect geo c g run S requests) (hpop : ApiTopPopulations geo g run)
    (halign : g.unitEntries*g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hentries : 0 < g.unitEntries) (words : Words) (ordinal : Nat)
    (hj : JobId.topFinish ordinal ∈ geo.cfg.potentialJobs)
    (hW : WithinHorizon geo.cfg (.topFinish ordinal)) (hdfs : geo.top.dfs = true)
    (hno : ¬Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run) words) :
    let tr := OnlineBatch.traceOf g run
    let prepared := prepOutput geo.cfg geo.shapes tr words ordinal
      (table geo.cfg geo.shapes tr words geo.cfg.levels (ordinal-1))
    let carry := carryOf geo.cfg geo.shapes tr words geo.cfg.levels ordinal
    weight 4 ((NativeMatchTopJobTrace.events geo.top tr.unsh
      (jobWord geo.cfg words geo.cfg.levels ordinal) (finishInputs prepared carry)
      (bucketPages geo.top.rPages prepared.tier) (bucketPages geo.top.bPages carry.tier)).map Event.comparison) ≤
      64^4 * NativeMatchJobAllocation.topCharge geo.top (32*geo.top.T) (32*geo.top.U) := by
  let tr := OnlineBatch.traceOf g run
  let prepared := prepOutput geo.cfg geo.shapes tr words ordinal
    (table geo.cfg geo.shapes tr words geo.cfg.levels (ordinal-1))
  let carry := carryOf geo.cfg geo.shapes tr words geo.cfg.levels ordinal
  have LF := HierarchySemanticsProof.lower hgeo.1
  have G := TopFacts.of_compatible hgeo.2
  obtain ⟨ho,hov⟩ := mem_finish.1 hj
  obtain ⟨N,_,hT⟩ := ApiStructuralProof.run_premises geo.cfg g run halign hentries hcorrect.1.initNodup
  have hLen : tr.init.length ≤ geo.init.C/2*geo.init.T := by
    rw [G.initC,G.topC,G.initT]
    exact hpop.1.trans G.capacity
  have hshape := (HierarchyStructuralStep geo hgeo tr hcorrect.1 hLen hcorrect.2.1 words ordinal ho hov).1
  obtain ⟨hr,hb⟩ := finish_lengths geo F tr words hno ordinal hj hW
  have hfit : TopTiersFit geo.top (finishInputs prepared carry) := by
    exact ⟨(List.length_filterMap_le _ _).trans hr,(List.length_filterMap_le _ _).trans hb⟩
  have hlayoutR : pageRecords (bucketPages geo.top.rPages prepared.tier) = (finishInputs prepared carry).carry := by
    rw [NativeMatchDenseTraceProof.bucketPages_records,List.take_of_length_le ?_]
    · rfl
    · simpa only [TopGeom.SR,G.topC,Nat.mul_comm] using hr
  have hlayoutB : pageRecords (bucketPages geo.top.bPages carry.tier) = (finishInputs prepared carry).bTier := by
    rw [NativeMatchDenseTraceProof.bucketPages_records,List.take_of_length_le ?_]
    · rfl
    · simpa only [TopGeom.SB,G.topC,Nat.mul_comm] using hb
  have hA : (finishInputs prepared carry).aAll.length ≤ 32*geo.top.T :=
    ((hpop.2 words ordinal ho hov).2.1).trans G.capacity
  have hB : (finishInputs prepared carry).bAll.length ≤ 32*geo.top.U := by
    have h := NativeMatchRecordCount.carry_records geo LF hT words geo.cfg.levels ordinal LF.levels2 le_rfl ho
    change carry.records.length ≤ 32*geo.top.U
    simpa only [LF.load,G.carryTop] using h
  have hn := top_no_failure geo.cfg geo.shapes tr words ordinal hj hW hno
  exact NativeMatchTopAllocationProof.top_allocated geo.top G.topValid G.topC tr.unsh
    (jobWord geo.cfg words geo.cfg.levels ordinal) (finishInputs prepared carry) hshape hfit hdfs hn
    _ _ hlayoutR hlayoutB (NativeMatchDrainLayoutProof.bucketPages_length _ _).le
    (NativeMatchDrainLayoutProof.bucketPages_length _ _).le _ _ hA hB

end RebuildBound.NativeMatchHierarchyLocalCount
namespace RebuildBound.NativeMatchHierarchyDirectCount
open Model Model.DirectJob Model.Hierarchy Model.Online Spec Spec.NativeMatch Spec.NativeMatchTrace
open Spec.NativeMatchHierarchy Spec.NativeMatchJobAllocation
open HierarchyInvariantProof HierarchyCoveringProof NativeMatchPhysicalInputs

theorem published (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (ordinal : Nat)
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
theorem allocated (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (g : OnlineGeom) (run : OnlineBatch.BatchRun)
    (halign : g.unitEntries*g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hentries : 0 < g.unitEntries) (hinit : (run.init.map Rec.key).Nodup)
    (words : Words) (ordinal : Nat)
    (hj : JobId.ordinary 1 ordinal ∈ geo.cfg.potentialJobs)
    (hW : WithinHorizon geo.cfg (.ordinary 1 ordinal))
    (hd2 : 2 ≤ geo.cfg.digitAt 1 ordinal)
    (hcap : (geo.direct (geo.cfg.digitAt 1 ordinal)).bCapacity ≤ 64)
    (hlink : (geo.direct (geo.cfg.digitAt 1 ordinal-1)).outputCapacity ≤
      (geo.direct (geo.cfg.digitAt 1 ordinal)).aTierCapacity)
    (hno : ¬Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run) words) :
    weight 4 ((jobEvents geo.cfg geo.shapes (OnlineBatch.traceOf g run) words
      (.ordinary 1 ordinal)).map Event.comparison) ≤
      64^4*(64*(g.unitsPerPrefix*(g.unitsPerPrefix-1)/2) +
        directAllocatedCharge (geo.direct (geo.cfg.digitAt 1 ordinal))
          (geo.cfg.load*((geo.cfg.digitAt 1 ordinal-1)*geo.cfg.carry 1))
          (geo.cfg.load*geo.cfg.carry 1)) := by
  let tr := OnlineBatch.traceOf g run
  let d := geo.cfg.digitAt 1 ordinal
  let prev := table geo.cfg geo.shapes tr words 1 (ordinal-1)
  let units := tr.units (ordinal-geo.cfg.seed 1-1)
  have LF := HierarchySemanticsProof.lower hgeo.1
  obtain ⟨N,_,hT⟩ := ApiStructuralProof.run_premises geo.cfg g run halign hentries hinit
  obtain ⟨h1,hL,ho,hov⟩ := mem_ordinary.1 hj
  have hfan := F.fanout_ge 1 hL (by omega)
  have hdpos : 1 ≤ d := (by dsimp [d]; exact HierarchyCoveringProof.digit_pos _ _)
  have hdle : d ≤ geo.cfg.fanout 1 := HierarchyCoveringProof.digit_le (by omega)
  have hD := (LF.direct d (by omega) hdpos).2.2
  have hdg : 2 ≤ (geo.direct d).digit := by rw [hD]; exact hd2
  have hdne : geo.cfg.digitAt 1 ordinal ≠ 1 := by omega
  obtain ⟨out,hpub⟩ := published geo.cfg geo.shapes tr words ordinal hj hW hno
  change runJob (geo.direct d) (jobWord geo.cfg words 1 (ordinal-1))
    (jobWord geo.cfg words 1 ordinal)
    (adopt (if d=1 then emptyOutput else prev) units) = .published out at hpub
  rw [if_neg hdne] at hpub
  have hpred : geo.cfg.seed 1 < ordinal-1 :=
    HierarchyInvariantProof.pred_gt (Nat.dvd_of_mod_eq_zero F.seed_dvd) ho hd2
  have hdprev : Config.digitOf (geo.cfg.fanout 1) (ordinal-1) = d-1 :=
    HierarchyInvariantProof.digit_pred (by omega) hd2
  have hp : JobId.ordinary 1 (ordinal-1) ∈ geo.cfg.potentialJobs :=
    mem_ordinary.2 ⟨h1,hL,hpred,by omega⟩
  have htime : time geo.cfg 1 (ordinal-1) ≤ time geo.cfg 1 ordinal := by
    exact Nat.mul_le_mul_right _ (Nat.sub_le ordinal 1)
  have hW' : WithinHorizon geo.cfg (.ordinary 1 (ordinal-1)) := htime.trans hW
  have hf : jobFails geo.cfg geo.shapes tr words (.ordinary 1 (ordinal-1)) = false := by
    apply Bool.eq_false_iff.mpr
    exact fun h => hno ⟨_,hp,hW',h⟩
  have hprev := NativeMatchPhysicalProducers.one_table F tr words hpred hf
  rw [hdprev] at hprev
  have hA := NativeMatchRecordCount.previous_records geo LF hT words 1 ordinal h1 hL ho
  simp only [prevInFor,hdne,ite_false] at hA
  have hB : (DirectMasks.records units).length ≤ geo.cfg.load*geo.cfg.carry 1 := by
    simpa only [Config.carry,Nat.sub_self,List.take_zero,List.foldr_nil,Nat.mul_one] using
      hT.load (ordinal-geo.cfg.seed 1-1)
  have hu : units.length ≤ g.unitsPerPrefix := List.length_take_le _ _
  have hw := NativeMatchDirectEventsCount.published_weight (geo.direct d)
    (jobWord geo.cfg words 1 (ordinal-1)) (jobWord geo.cfg words 1 ordinal) prev units out
    hpub hdg hcap (hprev.trans hlink) g.unitsPerPrefix _ _ hu hA hB
  simpa only [jobEvents,ite_true,if_neg hdne,d,prev,units,tr,Config.digitAt,
    HierarchyGeometry.shapes,hierarchyShapesWith] using hw

end RebuildBound.NativeMatchHierarchyDirectCount

namespace RebuildBound.NativeMatchHierarchyDirectCount
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatch Spec.NativeMatchTrace
open Spec.NativeMatchHierarchy HierarchyInvariantProof HierarchyCoveringProof

theorem first_allocated (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : OnlineGeom) (run : OnlineBatch.BatchRun) (words : Words) (ordinal : Nat)
    (hd : geo.cfg.digitAt 1 ordinal = 1) :
    weight 4 ((jobEvents geo.cfg geo.shapes (OnlineBatch.traceOf g run) words
      (.ordinary 1 ordinal)).map Event.comparison) ≤
      64^4*(64*(g.unitsPerPrefix*(g.unitsPerPrefix-1)/2)) := by
  have LF := HierarchySemanticsProof.lower hgeo.1
  have hf := (LF.fan 1 (by omega) (by have := LF.levels2; omega)).1
  have hD := (LF.direct 1 (by omega) (by omega)).2.2
  simp only [jobEvents,ite_true,show Config.digitOf (geo.cfg.fanout 1) ordinal=1 from hd]
  apply NativeMatchDirectEventsCount.first_digit_weight _ _ _ _ hD
  exact List.length_take_le _ _

end RebuildBound.NativeMatchHierarchyDirectCount
namespace RebuildBound.NativeMatchPhysicalFamily
open Model Model.Hierarchy Spec ConfigurationFamily NativeMatchPhysicalInputs

def IncomingFits (m : Member) (initialized : Bool) : Prop :=
  let geo := m.geometry initialized
  ∀ p ∈ geo.cfg.separatedClasses,
    incomingCapacity geo.cfg geo.shapes p.1 ≤
      (geo.shapes.sep p.1 p.2).bTierPages*(geo.shapes.sep p.1 p.2).C

instance (m : Member) (b : Bool) : Decidable (IncomingFits m b) :=
  inferInstanceAs (Decidable (∀ p ∈ _, _))

def ActualSeparatedRowsFit (m : Member) (initialized : Bool) : Prop :=
  let geo := m.geometry initialized
  ∀ p ∈ geo.cfg.separatedClasses,
    NativeMatchJobAllocation.separatedCharge (geo.shapes.sep p.1 p.2)
      (32*(p.2-1)*geo.cfg.carry p.1) (32*geo.cfg.carry p.1) ≤
      (NativeMatchInventory.ordinary m p.1 p.2).total

instance (m : Member) (b : Bool) : Decidable (ActualSeparatedRowsFit m b) :=
  inferInstanceAs (Decidable (∀ p ∈ _, _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem facts : ∀ m ∈ members, IncomingFits m true ∧ IncomingFits m false ∧
  ActualSeparatedRowsFit m true ∧ ActualSeparatedRowsFit m false := by decide +kernel

end RebuildBound.NativeMatchPhysicalFamily

namespace RebuildBound.NativeMatchDirectFamily
open Model Spec ConfigurationFamily NativeMatchInventory NativeMatchJobAllocation

def RowsFit (m : Member) (initialized : Bool) : Prop :=
  ∀ j ∈ List.range ((m.config initialized).fanout 1-1),
    let d := j+2
    (m.direct d).bCapacity ≤ 64 ∧
    (m.direct (d-1)).outputCapacity ≤ (m.direct d).aTierCapacity ∧
    64*(m.r0*(m.r0-1)/2) + directAllocatedCharge (m.direct d)
      (32*((d-1)*(m.config initialized).carry 1)) (32*(m.config initialized).carry 1) ≤
      (ordinary m 1 d).total

instance (m : Member) (b : Bool) : Decidable (RowsFit m b) :=
  inferInstanceAs (Decidable (∀ j ∈ _, _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem facts : ∀ m ∈ members, RowsFit m true ∧ RowsFit m false := by decide +kernel

end RebuildBound.NativeMatchDirectFamily

namespace RebuildBound.NativeMatchFamilyJobCount
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatch Spec.NativeMatchTrace
open Spec.NativeMatchHierarchy Spec.NativeMatchJobAllocation ConfigurationFamily
open HierarchyInvariantProof HierarchyCoveringProof NativeMatchPhysicalInputs

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

theorem shapes_chunk (geo : HierarchyGeometry) (h : Nat) : (geo.chunk h).shapes = geo.shapes := by
  unfold HierarchyGeometry.shapes HierarchyGeometry.chunk hierarchyShapesWith chunkConfig
  rw [(HierarchyHorizonFree geo.cfg (h*2^32) geo.rows).2.1]

theorem production_alignment (m : Member) (initialized : Bool) (h : Nat) :
    (⟨64,m.r0⟩ : OnlineGeom).unitEntries * (⟨64,m.r0⟩ : OnlineGeom).unitsPerPrefix =
      ((m.geometry initialized).chunk h).cfg.carryPositions 1 := by
  dsimp only [HierarchyGeometry.chunk,chunkConfig,Member.geometry,Member.config,Config.carryPositions,Config.carry]
  simp only [Nat.sub_self,List.take_zero,List.foldr_nil,Nat.mul_one]
  omega

set_option maxHeartbeats 3000000 in
theorem job_allocated (m : Member) (initialized : Bool) (hm : m ∈ members) (h : Nat)
    (c : Api.Codec) (run : OnlineBatch.BatchRun) (S : Schedule) (requests : List Api.Request)
    (hcorrect : ApiRunCorrect ((m.geometry initialized).chunk h) c ⟨64,m.r0⟩ run S requests)
    (hpop : ApiTopPopulations ((m.geometry initialized).chunk h) ⟨64,m.r0⟩ run)
    (words : Words) (j : JobId)
    (hj : j ∈ ((m.geometry initialized).chunk h).cfg.potentialJobs)
    (hW : WithinHorizon ((m.geometry initialized).chunk h).cfg j)
    (hno : ¬Fails ((m.geometry initialized).chunk h).cfg ((m.geometry initialized).chunk h).shapes
      (OnlineBatch.traceOf ⟨64,m.r0⟩ run) words) :
    weight 4 ((jobEvents ((m.geometry initialized).chunk h).cfg ((m.geometry initialized).chunk h).shapes
      (OnlineBatch.traceOf ⟨64,m.r0⟩ run) words j).map Event.comparison) ≤
      64^4*NativeMatchInventory.classCharge m (((m.geometry initialized).chunk h).cfg.classOf j) := by
  let geo := (m.geometry initialized).chunk h
  let g : OnlineGeom := ⟨64,m.r0⟩
  let tr := OnlineBatch.traceOf g run
  change weight 4 ((jobEvents geo.cfg geo.shapes tr words j).map Event.comparison) ≤
    64^4*NativeMatchInventory.classCharge m (geo.cfg.classOf j)
  change j ∈ geo.cfg.potentialJobs at hj
  change WithinHorizon geo.cfg j at hW
  change ¬Fails geo.cfg geo.shapes tr words at hno
  have hgeo := ConfigurationFamilyProbabilityProof.structural initialized m hm h
  have LF := HierarchySemanticsProof.lower hgeo.1
  have F := HierarchyCoveringFromProof.factsFor_chunk
    (ConfigurationFamilyProbabilityProof.coveringFacts initialized m hm)
    (ConfigurationFamilyProbabilityProof.chunkFacts initialized m hm) HierarchyHorizonFree h
  have hshape : geo.shapes = (m.geometry initialized).shapes := shapes_chunk _ _
  have halign := production_alignment m initialized h
  have hentries : 0 < g.unitEntries := by change 0 < 64; decide
  have hload : geo.cfg.load = 32 := rfl
  have hfanout : ∀ l, geo.cfg.fanout l = (m.geometry initialized).cfg.fanout l := fun _ => rfl
  have hcarry : ∀ l, geo.cfg.carry l = (m.geometry initialized).cfg.carry l := fun _ => rfl
  have hinit := hcorrect.1.initNodup
  have hcf : NativeMatchPhysicalFamily.IncomingFits m initialized ∧
      NativeMatchPhysicalFamily.ActualSeparatedRowsFit m initialized := by
    have H := NativeMatchPhysicalFamily.facts m hm
    cases initialized
    · exact ⟨H.2.1,H.2.2.2⟩
    · exact ⟨H.1,H.2.2.1⟩
  have hdf : NativeMatchDirectFamily.RowsFit m initialized := by
    have H := NativeMatchDirectFamily.facts m hm
    cases initialized
    · exact H.2
    · exact H.1
  cases j with
  | ordinary level ordinal =>
    obtain ⟨h1,hL,ho,hov⟩ := mem_ordinary.1 hj
    have hfan : 2 ≤ geo.cfg.fanout level := F.fanout_ge level hL h1
    have hdpos : 1 ≤ geo.cfg.digitAt level ordinal := HierarchyCoveringProof.digit_pos (geo.cfg.fanout level) ordinal
    have hdle : geo.cfg.digitAt level ordinal ≤ geo.cfg.fanout level :=
      HierarchyCoveringProof.digit_le (by omega)
    by_cases hl : level=1
    · subst level
      by_cases hd : geo.cfg.digitAt 1 ordinal=1
      · have hw := NativeMatchHierarchyDirectCount.first_allocated geo hgeo g run words ordinal hd
        change _ ≤ 64^4*NativeMatchInventory.classCharge m (.ordinary 1 (geo.cfg.digitAt 1 ordinal))
        rw [hd]
        simpa [
          NativeMatchInventory.classCharge,NativeMatchInventory.ordinary,NativeMatchInventory.SiteCharge.total,g] using hw
      · have hd2 : 2 ≤ geo.cfg.digitAt 1 ordinal := by omega
        have hrow := hdf (geo.cfg.digitAt 1 ordinal-2) (List.mem_range.mpr (by change _ < geo.cfg.fanout 1-1; omega))
        have he : geo.cfg.digitAt 1 ordinal-2+2=geo.cfg.digitAt 1 ordinal := by omega
        dsimp only at hrow
        rw [he] at hrow
        have hw := NativeMatchHierarchyDirectCount.allocated geo hgeo F g run halign hentries hinit
          words ordinal hj hW hd2 hrow.1 hrow.2.1 hno
        apply hw.trans
        change _ ≤ 64^4*(NativeMatchInventory.ordinary m 1 (geo.cfg.digitAt 1 ordinal)).total
        simpa only [geo,g,HierarchyGeometry.chunk,Member.geometry,chunkConfig,Member.config,Config.carry] using Nat.mul_le_mul_left (64^4) hrow.2.2
    · by_cases hd : geo.cfg.digitAt level ordinal=1
      · have hd' : Config.digitOf (geo.cfg.fanout level) ordinal=1 := hd
        simp only [jobEvents,hl,ite_false,hd',ite_true,weight,List.map_nil,List.sum_nil]
        exact Nat.zero_le _
      · have h2 : 2 ≤ level := by omega
        have hd2 : 2 ≤ geo.cfg.digitAt level ordinal := by omega
        have hclass := separated_class_mem geo.cfg level (geo.cfg.digitAt level ordinal) h2 hL hd2 hdle
        have hcbase : (level,geo.cfg.digitAt level ordinal) ∈ (m.geometry initialized).cfg.separatedClasses := by
          simpa only [geo,HierarchyGeometry.chunk,AdaptiveComposeProof.sepClasses_chunk] using hclass
        have hlink := hcf.1 _ hcbase
        have hrow := hcf.2 _ hcbase
        have hlink' : incomingCapacity geo.cfg geo.shapes level ≤
            (geo.shapes.sep level (geo.cfg.digitAt level ordinal)).bTierPages *
            (geo.shapes.sep level (geo.cfg.digitAt level ordinal)).C := by
          simpa only [incomingCapacity,hshape,hfanout] using hlink
        obtain ⟨N,_,hT⟩ := ApiStructuralProof.run_premises geo.cfg g run halign hentries hinit
        have hw := NativeMatchHierarchyLocalCount.separated_allocated geo hgeo F tr hT words level ordinal hj hW h2 hd2 hno hlink'
        have hw' : weight 4 ((jobEvents geo.cfg geo.shapes tr words (.ordinary level ordinal)).map Event.comparison) ≤
            64^4*NativeMatchJobAllocation.separatedCharge (geo.shapes.sep level (geo.cfg.digitAt level ordinal))
              (32*((geo.cfg.digitAt level ordinal-1)*geo.cfg.carry level)) (32*geo.cfg.carry level) := by
          have hd' : Config.digitOf (geo.cfg.fanout level) ordinal≠1 := hd
          simpa only [jobEvents,hl,ite_false,hd',hload] using hw
        apply hw'.trans
        apply Nat.mul_le_mul_left
        change _ ≤ (NativeMatchInventory.ordinary m level (geo.cfg.digitAt level ordinal)).total
        simpa only [hshape,hcarry,Nat.mul_assoc] using hrow
  | topPrepare ordinal => simp [jobEvents,weight,Config.classOf,NativeMatchInventory.classCharge]
  | initialization => simp [jobEvents,weight,Config.classOf,NativeMatchInventory.classCharge]
  | topFinish ordinal =>
    have hw := NativeMatchHierarchyLocalCount.top_allocated geo hgeo F c g run S requests hcorrect hpop
      halign hentries words ordinal hj hW (by rfl) hno
    have hr := (NativeMatchJobRows m hm initialized).2
    exact hw.trans (Nat.mul_le_mul_left _ hr)

end RebuildBound.NativeMatchFamilyJobCount

namespace RebuildBound.NativeMatchFamilyJobCount
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatch Spec.NativeMatchTrace
open Spec.NativeMatchHierarchy Spec.NativeMatchJobAllocation ConfigurationFamily
open Spec.NativeMatchOrdinals

theorem weight_flatMap {α : Type} (xs : List α) (events : α → List Event) :
    weight 4 ((xs.flatMap events).map Event.comparison) =
      (xs.map fun x => weight 4 ((events x).map Event.comparison)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [weight] at ih
    simp only [List.flatMap_cons,List.map_append,weight,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

set_option maxHeartbeats 1000000 in
theorem rebuild_allocated (m : Member) (initialized : Bool) (hm : m ∈ members) (h : Nat) (hh : 1 ≤ h)
    (c : Api.Codec) (run : OnlineBatch.BatchRun) (S : Schedule) (requests : List Api.Request)
    (hcorrect : ApiRunCorrect ((m.geometry initialized).chunk h) c ⟨64,m.r0⟩ run S requests)
    (hpop : ApiTopPopulations ((m.geometry initialized).chunk h) ⟨64,m.r0⟩ run)
    (words : Words)
    (hno : ¬Fails ((m.geometry initialized).chunk h).cfg ((m.geometry initialized).chunk h).shapes
      (OnlineBatch.traceOf ⟨64,m.r0⟩ run) words) :
    weight 4 ((rebuildEvents ((m.geometry initialized).chunk h).cfg ((m.geometry initialized).chunk h).shapes
      (OnlineBatch.traceOf ⟨64,m.r0⟩ run) words).map Event.comparison) ≤
      64^4*h*NativeMatchInventory.sMin m initialized := by
  let geo := (m.geometry initialized).chunk h
  let tr := OnlineBatch.traceOf (⟨64,m.r0⟩ : OnlineGeom) run
  let jobs := geo.cfg.potentialJobs.filter fun j => decide (WithinHorizon geo.cfg j)
  have hpoint : ∀ j ∈ jobs, weight 4 ((jobEvents geo.cfg geo.shapes tr words j).map Event.comparison) ≤
      64^4*NativeMatchInventory.classCharge m (geo.cfg.classOf j) := by
    intro j hj
    have hj' := List.mem_filter.mp hj
    exact job_allocated m initialized hm h c run S requests hcorrect hpop words j hj'.1
      (of_decide_eq_true hj'.2) hno
  have hsum : (jobs.map fun j => NativeMatchInventory.classCharge m (geo.cfg.classOf j)).sum ≤
      h*NativeMatchInventory.sMin m initialized := by
    have H := NativeMatchOrdinalCount.family_prefix initialized m hm (NativeMatchInventory.classCharge m)
      h hh (h*2^32) (Nat.le_refl _) (fun j => decide (WithinHorizon geo.cfg j))
    exact H
  change weight 4 ((jobs.flatMap (jobEvents geo.cfg geo.shapes tr words)).map Event.comparison) ≤ _
  rw [weight_flatMap]
  calc
    _ ≤ (jobs.map fun j => 64^4*NativeMatchInventory.classCharge m (geo.cfg.classOf j)).sum :=
      List.sum_le_sum hpoint
    _ = 64^4*(jobs.map fun j => NativeMatchInventory.classCharge m (geo.cfg.classOf j)).sum := by
      rw [List.sum_map_mul_left]
    _ ≤ 64^4*(h*NativeMatchInventory.sMin m initialized) := Nat.mul_le_mul_left _ hsum
    _ = _ := by rw [Nat.mul_assoc]

set_option maxHeartbeats 1000000 in
theorem adaptive_allocated (m : Member) (initialized : Bool) (hm : m ∈ members) (h : Nat) (hh : 1 ≤ h)
    (c : Api.Codec) (schedule : Schedule) (init : List Rec) (transcriptWidth width : Nat)
    (batches : List ApiAdaptive.Batch)
    (choose : ApiLegal.Chooser ((m.geometry initialized).chunk h).cfg
      (ApiAdaptive.shape (ApiAdaptive.frames width 64 batches)) schedule transcriptWidth)
    (hInit : ApiCapacity.InitialStateValid ((m.geometry initialized).chunk h).keyCapacity
      ((m.geometry initialized).chunk h).cfg.initialized init)
    (hhor : Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width 64 batches)) ≤
      ((m.geometry initialized).chunk h).cfg.horizon)
    (hS : SchedulePremises ((m.geometry initialized).chunk h).cfg schedule
      (Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width 64 batches))) transcriptWidth)
    (hcap : ∀ t : ApiLegal.Prefix ((m.geometry initialized).chunk h).cfg
        (ApiAdaptive.shape (ApiAdaptive.frames width 64 batches)) schedule transcriptWidth
        (Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width 64 batches))),
      ApiCapacity.LiveCapacity ((m.geometry initialized).chunk h).keyCapacity (Api.stateOf c init) (init.map Rec.key)
        ((ApiAdaptive.requestGroups (ApiLegal.adapt ((m.geometry initialized).chunk h).cfg
          (ApiAdaptive.shape (ApiAdaptive.frames width 64 batches)) schedule choose)
          (Adaptive.rowsOf (ApiLegal.erase t)
            (Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width 64 batches))))
          (ApiAdaptive.frames width 64 batches)).flatMap PublicApi.Group.lanes))
    (words : Words) (dummy : Nat → Nat → Nat) :
    let geo := (m.geometry initialized).chunk h
    let g : OnlineGeom := ⟨64,m.r0⟩
    let frames := ApiAdaptive.frames width 64 batches
    let compiled := ApiLegal.adapt geo.cfg (ApiAdaptive.shape frames) schedule choose
    let client := ApiAdaptive.run c geo.cfg geo.shapes g schedule init frames compiled
    let run := Adaptive.realized geo.cfg geo.shapes g schedule client words dummy
    ¬Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run) words →
    weight 4 ((rebuildEvents geo.cfg geo.shapes (OnlineBatch.traceOf g run) words).map Event.comparison) ≤
      64^4*h*NativeMatchInventory.sMin m initialized := by
  dsimp only
  intro hno
  have hgeo := ConfigurationFamilyProbabilityProof.structural initialized m hm h
  have H := ApiLegalLive ((m.geometry initialized).chunk h) hgeo c ⟨64,m.r0⟩ schedule init transcriptWidth
    width batches choose hInit (production_alignment m initialized h) (by change 0 < 64; decide)
    hhor hS hcap words dummy
  exact rebuild_allocated m initialized hm h hh c _ schedule _ H.1 H.2.1 words hno

end RebuildBound.NativeMatchFamilyJobCount

namespace RebuildBound

theorem NativeMatchProductionJobInventory : Spec.NativeMatchProductionJobInventory_statement := by
  intro m initialized hm h
  try dsimp only
  exact NativeMatchFamilyJobCount.job_allocated m initialized hm h

theorem NativeMatchRebuildInventory : Spec.NativeMatchRebuildInventory_statement := by
  intro m initialized hm h hh
  try dsimp only
  exact NativeMatchFamilyJobCount.rebuild_allocated m initialized hm h hh

theorem NativeMatchAdaptiveRebuildInventory : Spec.NativeMatchAdaptiveRebuildInventory_statement := by
  intro m initialized hm h hh
  try dsimp only
  intro c schedule init transcriptWidth width batches
  try dsimp only
  intro choose
  try dsimp only
  intro hInit hhor hS hcap words dummy
  exact NativeMatchFamilyJobCount.adaptive_allocated m initialized hm h hh c schedule init transcriptWidth
    width batches choose hInit hhor hS hcap words dummy

theorem NativeMatchNoComparisonPaths : Spec.NativeMatchNoComparisonPaths_statement := by
  intro cfg sh tr words ordinal
  exact ⟨rfl,rfl⟩

end RebuildBound
