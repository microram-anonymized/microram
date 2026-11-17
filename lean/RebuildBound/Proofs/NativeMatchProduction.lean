import RebuildBound.Proofs.NativeMatchHierarchyCounts
import RebuildBound.Proofs.NativeMatchHierarchy
import RebuildBound.Proofs.NativeRoutingActual
import RebuildBound.Proofs.NativeMatchRelabel
import RebuildBound.Proofs.IdealKeyLaw
import RebuildBound.Spec.NativeMatch.Production
import RebuildBound.Proofs.NativeMatchAllocation
import RebuildBound.Proofs.IdealGeometryFamily
import RebuildBound.Proofs.IdealGeometry.Arithmetic
import RebuildBound.Proofs.ApiLegal
import RebuildBound.Proofs.NativeMatchJobs
import RebuildBound.Proofs.NativeMatchDenseTrace.Physical
import RebuildBound.Proofs.NativeMatch
import RebuildBound.Proofs.NativeKey
import RebuildBound.Proofs.IdealMeasurable
import Mathlib.Tactic
namespace RebuildBound.NativeMatchDenseScheduleProof
open Model Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchPhysical
open NativeMatchDenseTraceProof NativeMatchPhysicalProof

theorem batch_weight (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun)
    (hT : TraceStructural geo.cfg (OnlineBatch.traceOf g run))
    (hInit : run.init.length ≤ geo.init.C/2*geo.init.T)
    (hUnsh : UnshPromise geo.cfg geo.shapes (OnlineBatch.traceOf g run))
    (words : Words) (snapshots : Nat → Snapshot (allocatedSlots geo.cfg.levels geo.cfg.fanout).length)
    (t : Nat) (hr : 0 < g.unitsPerPrefix)
    (hc : ∀ c ∈ (physicalSchedule geo.cfg snapshots (OnlineBatch.chunkStart (OnlineBatch.widths run) t)).tables,
      1 ≤ c.1 ∧ c.1 ≤ geo.cfg.levels ∧ c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1)
    (hfill : ∀ slot, (OnlineBatch.slots run)[t]? = some slot → slot.probes = true → ∃ units,
      fillDenseUnits g.unitsPerPrefix 2 (snapshotAt run snapshots t).consumed
        (OnlineBatch.stateAt g run slot.op).frozen.length = some units) :
    weight 2 ((batchEvents geo.cfg geo.shapes g run (physicalSchedule geo.cfg snapshots) words t).map Event.comparison) ≤
      (3*g.unitsPerPrefix+(allocatedSlots geo.cfg.levels geo.cfg.fanout).length)*14*8^2 := by
  unfold batchEvents
  cases hs : (OnlineBatch.slots run)[t]? with
  | none => simp [weight]
  | some slot =>
    by_cases hp : slot.probes = true
    · simp only [hp,ite_true]
      obtain ⟨units,hu⟩ := hfill slot hs hp
      have h := physical_query_weight geo hgeo (OnlineBatch.traceOf g run) hT hInit hUnsh words
        (OnlineBatch.stateAt g run slot.op) g.unitsPerPrefix (snapshotAt run snapshots t).consumed
        hr units hu (requester_unique g run slot.op) slot.record.key (snapshotAt run snapshots t).deltas hc
      simpa only [batchPages,hs,OnlineBatch.slotSchedule,physicalSchedule,Nat.add_sub_cancel_left,snapshotAt] using h
    · simp [hp,weight]

theorem weight_flatMap {A : Type} (xs : List A) (events : A → List Event) (count : Nat) :
    weight count ((xs.flatMap events).map Event.comparison) =
      (xs.map fun x => weight count ((events x).map Event.comparison)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.map_append,weight,List.sum_append,List.map_cons,List.sum_cons]
    exact congrArg (fun v => _ + v) ih

theorem prefix_weight (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun)
    (hT : TraceStructural geo.cfg (OnlineBatch.traceOf g run))
    (hInit : run.init.length ≤ geo.init.C/2*geo.init.T)
    (hUnsh : UnshPromise geo.cfg geo.shapes (OnlineBatch.traceOf g run))
    (words : Words) (snapshots : Nat → Snapshot (allocatedSlots geo.cfg.levels geo.cfg.fanout).length)
    (n : Nat) (hr : 0 < g.unitsPerPrefix)
    (hc : ∀ t < n, ∀ c ∈ (physicalSchedule geo.cfg snapshots (OnlineBatch.chunkStart (OnlineBatch.widths run) t)).tables,
      1 ≤ c.1 ∧ c.1 ≤ geo.cfg.levels ∧ c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1)
    (hfill : ∀ t < n, ∀ slot, (OnlineBatch.slots run)[t]? = some slot → slot.probes = true → ∃ units,
      fillDenseUnits g.unitsPerPrefix 2 (snapshotAt run snapshots t).consumed
        (OnlineBatch.stateAt g run slot.op).frozen.length = some units) :
    weight 2 ((batchPrefixEvents geo.cfg geo.shapes g run (physicalSchedule geo.cfg snapshots) words n).map Event.comparison) ≤
      n*((3*g.unitsPerPrefix+(allocatedSlots geo.cfg.levels geo.cfg.fanout).length)*14*8^2) := by
  rw [batchPrefixEvents,weight_flatMap]
  calc
    _ ≤ ((List.range n).map fun _ => (3*g.unitsPerPrefix+
      (allocatedSlots geo.cfg.levels geo.cfg.fanout).length)*14*8^2).sum := by
      apply List.sum_le_sum
      intro t ht
      exact batch_weight geo hgeo g run hT hInit hUnsh words snapshots t hr
        (hc t (List.mem_range.mp ht)) (hfill t (List.mem_range.mp ht))
    _ = _ := by simp
end RebuildBound.NativeMatchDenseScheduleProof
namespace RebuildBound.NativeMatchDenseScheduleProof
open Model Model.Hierarchy Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchPhysical
open ConfigurationFamily

theorem family_prefix_weight (initialized : Bool) (member : Member) (hm : member ∈ members)
    (h n : Nat) (hn : n ≤ h*2^32) (g : Online.OnlineGeom) (hg : g.unitsPerPrefix = member.r0)
    (run : OnlineBatch.BatchRun)
    (hT : TraceStructural ((member.geometry initialized).chunk h).cfg (OnlineBatch.traceOf g run))
    (hInit : run.init.length ≤ ((member.geometry initialized).chunk h).init.C/2*
      ((member.geometry initialized).chunk h).init.T)
    (hUnsh : UnshPromise ((member.geometry initialized).chunk h).cfg
      ((member.geometry initialized).chunk h).shapes (OnlineBatch.traceOf g run))
    (words : Words)
    (snapshots : Nat → Snapshot (allocatedSlots (member.config initialized).levels
      (member.config initialized).fanout).length)
    (hc : ∀ t < n, ∀ c ∈ (physicalSchedule (member.config initialized) snapshots
      (OnlineBatch.chunkStart (OnlineBatch.widths run) t)).tables,
      1 ≤ c.1 ∧ c.1 ≤ (member.config initialized).levels ∧
        c.2 ≤ (member.config initialized).seed c.1 +
          (chunkConfig (member.config initialized) h).ordinals c.1)
    (hfill : ∀ t < n, ∀ slot, (OnlineBatch.slots run)[t]? = some slot → slot.probes = true → ∃ units,
      fillDenseUnits g.unitsPerPrefix 2 (snapshotAt run snapshots t).consumed
        (OnlineBatch.stateAt g run slot.op).frozen.length = some units) :
    weight 2 ((batchPrefixEvents ((member.geometry initialized).chunk h).cfg
      ((member.geometry initialized).chunk h).shapes g run
      (physicalSchedule (member.config initialized) snapshots) words n).map Event.comparison) ≤
      h * (2^32 * NativeMatchInventory.denseBuckets member * 14 * 8^2) := by
  have hr : ∀ m ∈ members, 0 < m.r0 := by decide +kernel
  have hp := prefix_weight ((member.geometry initialized).chunk h)
    (IdealGeometryProof.structural_chunk _ (IdealGeometryFamily initialized member hm).1 h)
    g run hT hInit hUnsh words snapshots n (by rw [hg]; exact hr member hm) hc hfill
  have ha : (allocatedSlots ((member.geometry initialized).chunk h).cfg.levels
      ((member.geometry initialized).chunk h).cfg.fanout).length = NativeMatchInventory.arenaSlots member :=
    (NativeMatchPhysicalAllocation initialized member hm).1
  have he : 3*g.unitsPerPrefix+(allocatedSlots ((member.geometry initialized).chunk h).cfg.levels
      ((member.geometry initialized).chunk h).cfg.fanout).length = NativeMatchInventory.denseBuckets member := by
    rw [hg,ha]; rfl
  calc
    _ ≤ n*(NativeMatchInventory.denseBuckets member*14*8^2) :=
      hp.trans_eq (congrArg (fun x => n*(x*14*8^2)) he)
    _ ≤ (h*2^32)*(NativeMatchInventory.denseBuckets member*14*8^2) := Nat.mul_le_mul_right _ hn
    _ = _ := by ring
end RebuildBound.NativeMatchDenseScheduleProof
namespace RebuildBound.NativeMatchDenseScheduleProof
open Model Spec Spec.NativeMatchPhysical

theorem ready_fill {slots : Nat} (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun)
    (snapshots : Nat → Snapshot slots) (n : Nat) (h : ready g run snapshots n = true)
    (t : Nat) (ht : t < n) (slot : OnlineBatch.Slot) (hs : (OnlineBatch.slots run)[t]? = some slot)
    (hp : slot.probes = true) : ∃ units,
      fillDenseUnits g.unitsPerPrefix 2 (snapshotAt run snapshots t).consumed
        (OnlineBatch.stateAt g run slot.op).frozen.length = some units := by
  have hh := List.all_eq_true.mp h t (List.mem_range.mpr ht)
  simp only [hs,hp,ite_true] at hh
  cases he : fillDenseUnits g.unitsPerPrefix 2 (snapshotAt run snapshots t).consumed
      (OnlineBatch.stateAt g run slot.op).frozen.length with
  | none => simp [he] at hh
  | some units => exact ⟨units,rfl⟩
end RebuildBound.NativeMatchDenseScheduleProof

namespace RebuildBound.NativeMatchProductionProof
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatchPhysical Spec.NativeMatchProduction
open OnlineCorrectnessProof OnlineFreshProof

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem alignment (member : ConfigurationFamily.Member) (hm : member ∈ ConfigurationFamily.members)
    (initialized : Bool) (h : Nat) :
    64*member.r0 = ((member.geometry initialized).chunk h).cfg.carryPositions 1 := by
  have hc : ∀ m ∈ ConfigurationFamily.members, ∀ i : Bool,
      64*m.r0 = (m.config i).carryPositions 1 := by decide +kernel
  exact hc member hm initialized

theorem structural {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members) :
    ctx.geo.Structural :=
  IdealGeometryProof.structural_chunk _ (IdealGeometryFamily initialized member hm).1 h

theorem contracts {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    ∃ requests, ApiRunCorrect ctx.geo ctx.codec ctx.unit (ctx.run tape) ctx.schedule requests ∧
      ApiTopPopulations ctx.geo ctx.unit (ctx.run tape) := by
  have hc := ApiLegalLive ctx.geo (structural ctx hm) ctx.codec ctx.unit ctx.schedule ctx.init
    ctx.transcriptWidth ctx.batchWidth ctx.batches ctx.choose hv.1 (alignment member hm initialized h)
    (by change 0 < 64; decide) hv.2.1 hv.2.2.1 hv.2.2.2 (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
  exact ⟨_,hc.1,hc.2.1⟩

theorem init_bound {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    (ctx.run tape).init.length ≤ ctx.geo.init.C/2*ctx.geo.init.T := by
  have G := HierarchyInvariantProof.TopFacts.of_compatible (structural ctx hm).2
  change ctx.init.length ≤ _
  rw [G.initC,G.topC,G.initT]
  exact hv.1.2.1.trans G.capacity

theorem schedule_coordinates {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) (t : Nat) (ht : t < ctx.accesses) :
    ∀ c ∈ (ctx.schedule (OnlineBatch.chunkStart (OnlineBatch.widths (ctx.run tape)) t)).tables,
      1 ≤ c.1 ∧ c.1 ≤ ctx.geo.cfg.levels ∧ c.2 ≤ ctx.geo.cfg.seed c.1+ctx.geo.cfg.ordinals c.1 := by
  let j := OnlineBatch.chunkStart (OnlineBatch.widths (ctx.run tape)) t
  have hj : j < ctx.accesses := (BatchFreshProof.chunkStart_le _ _).trans_lt ht
  have hs := hv.2.2.1
  have F := HierarchySemanticsProof.lower (structural ctx hm).1
  intro c hc
  have hp : Published ctx.geo.cfg c := hs.coords j hj c hc
  refine ⟨hp.1,hp.2.1,coordinate_horizon F hp ?_⟩
  exact ((tiles_bounds (hs.tile j hj) c hc).2.2.trans (hs.consumed j hj).2).trans
    (Nat.add_le_add_left (Nat.le_trans (Nat.le_of_lt hj) hv.2.1) _)
end RebuildBound.NativeMatchProductionProof

namespace RebuildBound.NativeMatchProductionProof
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatch Spec.NativeMatchTrace
open Spec.NativeMatchPhysical Spec.NativeMatchProduction

theorem dense_budget {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape)
    (hr : ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true) :
    weight 2 ((batchPrefixEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape)
      ctx.schedule (IdealHierarchy.words tape) ctx.accesses).map Event.comparison) ≤
      h*(2^32*NativeMatchInventory.denseBuckets member*14*8^2) := by
  obtain ⟨requests,hcorrect,_⟩ := contracts ctx hm hv tape
  exact NativeMatchDenseScheduleProof.family_prefix_weight initialized member hm h ctx.accesses
    hv.2.1 ctx.unit rfl (ctx.run tape) hcorrect.1 (init_bound ctx hm hv tape) hcorrect.2.1
    (IdealHierarchy.words tape) ctx.snapshots (schedule_coordinates ctx hm hv tape)
    (NativeMatchDenseScheduleProof.ready_fill ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses hr)

open MeasureTheory in
open scoped ENNReal in
theorem capacity_reserve {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hh : 1 ≤ h) (hv : ctx.Valid) :
    IdealKey.tapeLaw {tape | Fails ctx.geo.cfg ctx.geo.shapes
      (OnlineBatch.traceOf ctx.unit (ctx.run tape)) (IdealHierarchy.words tape)} +
      (h : ℝ≥0∞)*((NativeMatchInventory.weight member initialized : ℝ≥0∞)/(2:ℝ≥0∞)^128) ≤
      (h : ℝ≥0∞)*ENNReal.ofReal (1/(2:ℝ)^64) :=
  NativeMatchCapacityAllocation initialized member hm h hh ctx.codec ctx.unit ctx.schedule ctx.init
    ctx.transcriptWidth ctx.batchWidth ctx.batches ctx.choose hv.1 (alignment member hm initialized h)
    (by change 0 < 64; decide) hv.2.1 hv.2.2.1 hv.2.2.2
end RebuildBound.NativeMatchProductionProof

namespace RebuildBound.NativeMatchInventoryRules
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

def Only (rule : Rule) (events : List Event) : Prop := ∀ e ∈ events, e.rule = rule

theorem append {rule : Rule} {a b : List Event} (ha : Only rule a) (hb : Only rule b) :
    Only rule (a++b) := by intro e he; exact (List.mem_append.mp he).elim (ha e) (hb e)
theorem flatMap {A : Type} {rule : Rule} (xs : List A) (events : A → List Event)
    (h : ∀ x ∈ xs, Only rule (events x)) : Only rule (xs.flatMap events) := by
  intro e he
  obtain ⟨x,hx,he⟩ := List.mem_flatMap.mp he
  exact h x hx e he

theorem writer {State Op : Type} {rule : Rule} (step : State → Op → State)
    (events : State → Op → List Event) (h : ∀ state op, Only rule (events state op))
    (state : State) (ops : List Op) : Only rule (eventsOf step events state ops) := by
  induction ops generalizing state with
  | nil => intro e he; simp [eventsOf] at he
  | cons op ops ih => exact append (h state op) (ih _)

theorem pair (site : Site) (fresh old : DirectMask64.Payload) (fm om : Mask) :
    Only .rebuild32 (pairEvents site fresh old fm om) := by
  intro e he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
  rfl

theorem prefix_rule (data : Nat → DirectMask64.Payload) (unit : Nat) (masks : List Mask) (ops : List Nat) :
    Only .rebuild32 (prefixTrace data unit masks ops) := by
  induction ops generalizing masks with
  | nil => intro e he; simp [prefixTrace] at he
  | cons p ps ih => exact append (pair _ _ _ _ _) (ih _)

theorem pool (sources targets : List Page) : Only .rebuild32 (poolTrace sources targets) := by
  induction sources generalizing targets with
  | nil => intro e he; simp [poolTrace] at he
  | cons source sources ih => exact append (flatMap _ _ (fun _ _ => pair _ _ _ _ _)) (ih _)

theorem fixed (source : Page) (pages : List Page) (ops : List Nat) :
    Only .rebuild32 (fixedTrace source pages ops) := by
  induction ops generalizing pages with
  | nil => intro e he; simp [fixedTrace] at he
  | cons op ops ih => exact append (pair _ _ _ _ _) (ih _)

theorem grouped (bucket : Bucket) (home : Rec → Bool) (pages : List Page) :
    Only .rebuild32 (groupedOfferEvents bucket home pages) := by
  induction pages generalizing bucket with
  | nil => intro e he; simp [groupedOfferEvents] at he
  | cons page pages ih => exact append (pair _ _ _ _ _) (ih _)

theorem site {rule : Rule} (tag : Site) (events : List Event) (h : Only rule events) :
    Only rule (atSite tag events) := by
  intro e he
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp he
  exact h old ho

theorem drain (shedPages tierPages : Nat) (state : SFin) :
    Only .rebuild32 (NativeMatchJobTrace.drainEvents shedPages tierPages state) :=
  writer _ _ (fun _ _ => append (pair _ _ _ _ _) (pair _ _ _ _ _)) _ _

theorem ordinary_finish (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : NativeMatchJobTrace.FinishGhost) :
    Only .rebuild32 (NativeMatchJobTrace.finishEvents g word bMain ghost) := by
  apply writer
  intro state i
  apply append (fixed _ _ _)
  apply writer
  intro acc q
  apply append (grouped _ _ _)
  apply writer
  intro state pg
  exact pair _ _ _ _ _

theorem top_finish (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : NativeMatchTopJobTrace.Ghost) :
    Only .rebuild32 (NativeMatchTopJobTrace.finishEvents g word bMain ghost) := by
  apply writer
  intro state i
  apply append (fixed _ _ _)
  apply writer
  intro acc q
  exact append (pair _ _ _ _ _) (site _ _ (pool _ _))

theorem separated (rule : CapRule) (g : SepGeom) (word : LogicalKey → Nat) (inp : SInputs)
    (ops : List (Nat×Nat)) (pages : List Page) :
    Only .rebuild32 (NativeMatchJobTrace.separatedEvents rule g word inp ops pages) :=
  append (append (pool _ _) (ordinary_finish _ _ _ _)) (drain _ _ _)

theorem top (g : TopGeom) (unsh : Rec → Bool) (word : LogicalKey → Nat) (inp : TopInputs)
    (carryPages bpages : List Page) :
    Only .rebuild32 (NativeMatchTopJobTrace.events g unsh word inp carryPages bpages) :=
  append (append (pool _ _) (top_finish _ _ _ _)) (drain _ _ _)

theorem direct_plan (g : DirectJob.Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : DirectJob.Table) (sources raw : List Page) (shedPages tierPages : Nat) :
    Only .rebuild32 (NativeMatchDirectPlanTrace.events g word inp b sources raw shedPages tierPages) :=
  append (append (pool _ _) (ordinary_finish _ _ _ _)) (drain _ _ _)

theorem direct (g : DirectJob.Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs) (prev : Output) :
    Only .rebuild32 (NativeMatchHierarchy.directEvents g word inp prev) := by
  apply append (prefix_rule _ _ _ _)
  cases hb : DirectJob.buildB g word inp with
  | error e => intro e he; simp at he
  | ok b =>
    by_cases hd : g.digit = 1
    · intro e he; simp [hd] at he
    · simpa only [hb,hd,ite_false] using direct_plan g word inp b _ _ _ _

theorem job (cfg : Config) (sh : Hierarchy.Shapes) (tr : Hierarchy.Trace) (words : Hierarchy.Words)
    (j : JobId) : Only .rebuild32 (NativeMatchHierarchy.jobEvents cfg sh tr words j) := by
  cases j with
  | initialization => intro e he; simp [NativeMatchHierarchy.jobEvents] at he
  | topPrepare ordinal => intro e he; simp [NativeMatchHierarchy.jobEvents] at he
  | topFinish ordinal => exact top _ _ _ _ _ _
  | ordinary level ordinal =>
    simp only [NativeMatchHierarchy.jobEvents]
    split
    · exact direct _ _ _ _
    · split
      · intro e he; simp at he
      · exact separated _ _ _ _ _ _

theorem dense (page : Page) (key : LogicalKey) (active : Bool) : Only .dense64 (denseEvents page key active) := by
  unfold denseEvents
  split_ifs
  · split
    · intro e he; simp at he
    · apply flatMap
      intro column hc e he
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp he
      rfl
  · intro e he; simp at he

theorem dense_scan (pages : List Page) (key : LogicalKey) : Only .dense64 (denseScanEvents pages key) :=
  flatMap _ _ (fun _ _ => dense _ _ _)
theorem cascade (key : LogicalKey) (table : Nat×Nat→Output) (cs : List (Nat×Nat)) :
    Only .dense64 (cascadeEvents key table cs) := flatMap _ _ (fun _ _ => dense_scan _ _)
theorem batch (cfg : Config) (sh : Hierarchy.Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (schedule : Online.Schedule) (words : Hierarchy.Words) (t : Nat) :
    Only .dense64 (batchEvents cfg sh g run schedule words t) := by
  unfold batchEvents
  split
  · intro e he; simp at he
  · split_ifs
    · exact append (dense_scan _ _) (cascade _ _ _)
    · intro e he; simp at he
end RebuildBound.NativeMatchInventoryRules

namespace RebuildBound.NativeMatchInventoryRules
open Model Spec Spec.NativeMatch Spec.NativeMatchTrace Spec.NativeMatchHierarchy

theorem rebuild (cfg : Config) (sh : Hierarchy.Shapes) (tr : Hierarchy.Trace) (words : Hierarchy.Words) :
    Only .rebuild32 (rebuildEvents cfg sh tr words) := flatMap _ _ (fun j _ => job cfg sh tr words j)
theorem dense_prefix (cfg : Config) (sh : Hierarchy.Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (schedule : Online.Schedule) (words : Hierarchy.Words) (n : Nat) :
    Only .dense64 (batchPrefixEvents cfg sh g run schedule words n) :=
  flatMap _ _ (fun t _ => batch cfg sh g run schedule words t)

theorem comparisons_append (rule : Rule) (a b : List Event) :
    comparisons rule (a++b) = comparisons rule a ++ comparisons rule b := by
  simp [comparisons,List.filter_append]

theorem comparisons_same (rule : Rule) (events : List Event) (h : Only rule events) :
    comparisons rule events = events.map Event.comparison := by
  rw [comparisons,List.filter_eq_self.mpr]
  intro e he
  simp [h e he]

theorem comparisons_other (first second : Rule) (hne : first ≠ second)
    (events : List Event) (h : Only first events) : comparisons second events = [] := by
  have hf : events.filter (fun e => e.rule == second) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simp [h e he,hne]
  simp only [comparisons,hf,List.map_nil]

theorem projections (cfg : Config) (sh : Hierarchy.Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (schedule : Online.Schedule) (words : Hierarchy.Words) (n : Nat) :
    comparisons .rebuild32 (referenceEvents cfg sh g run schedule words n) =
      (rebuildEvents cfg sh (OnlineBatch.traceOf g run) words).map Event.comparison ∧
    comparisons .dense64 (referenceEvents cfg sh g run schedule words n) =
      (batchPrefixEvents cfg sh g run schedule words n).map Event.comparison := by
  have hr := rebuild cfg sh (OnlineBatch.traceOf g run) words
  have hd := dense_prefix cfg sh g run schedule words n
  constructor
  · simp only [referenceEvents,comparisons_append,comparisons_same _ _ hr,
      comparisons_other .dense64 .rebuild32 (by decide) _ hd,List.append_nil]
  · simp only [referenceEvents,comparisons_append,comparisons_same _ _ hd,
      comparisons_other .rebuild32 .dense64 (by decide) _ hr,List.nil_append]
end RebuildBound.NativeMatchInventoryRules

namespace RebuildBound.NativeMatchProductionProof
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatch Spec.NativeMatchTrace
open Spec.NativeMatchPhysical Spec.NativeMatchHierarchy Spec.NativeMatchProduction

theorem rebuild_budget (checked : NativeMatchAdaptiveRebuildInventory_statement)
    {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hh : 1 ≤ h) (hv : ctx.Valid) (tape : IdealKey.Tape)
    (hf : ¬ctx.capacityBad tape) :
    weight 4 ((rebuildEvents ctx.geo.cfg ctx.geo.shapes
      (OnlineBatch.traceOf ctx.unit (ctx.run tape)) (IdealHierarchy.words tape)).map Event.comparison) ≤
      h*(64^4*NativeMatchInventory.sMin member initialized) := by
  have hb := checked member initialized hm h hh ctx.codec ctx.schedule ctx.init
    ctx.transcriptWidth ctx.batchWidth ctx.batches ctx.choose hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) hf
  convert hb using 1 <;> first | rfl | ring

theorem weights (checked : NativeMatchAdaptiveRebuildInventory_statement)
    {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hh : 1 ≤ h) (hv : ctx.Valid) (tape : IdealKey.Tape) :
    weight 4 (comparisons .rebuild32 (ctx.inventory tape)) ≤ h*(64^4*NativeMatchInventory.sMin member initialized) ∧
    weight 2 (comparisons .dense64 (ctx.inventory tape)) ≤ h*(2^32*NativeMatchInventory.denseBuckets member*14*8^2) := by
  by_cases hc : ctx.capacityBad tape ∨ ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = false
  · have he : ctx.inventory tape = [] := by
      unfold Context.inventory physicalChargedEvents
      exact ite_eq_left hc
    simp [he,comparisons,weight]
  · have hf : ¬ctx.capacityBad tape := fun h => hc (Or.inl h)
    have hr : ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true := by
      cases he : ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses
      · exact False.elim (hc (Or.inr he))
      · rfl
    have he : ctx.inventory tape = referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape)
        ctx.schedule (IdealHierarchy.words tape) ctx.accesses := by
      unfold Context.inventory physicalChargedEvents
      exact ite_eq_right hc
    rw [he]
    have hp := NativeMatchInventoryRules.projections ctx.geo.cfg ctx.geo.shapes ctx.unit
      (ctx.run tape) ctx.schedule (IdealHierarchy.words tape) ctx.accesses
    rw [hp.1,hp.2]
    exact ⟨rebuild_budget checked ctx hm hh hv tape hf,dense_budget ctx hm hv tape hr⟩
end RebuildBound.NativeMatchProductionProof

namespace RebuildBound.NativeMatchInventoryProof
open Model Spec Spec.NativeMatch Spec.NativeNormalize Spec.NativeMatchTrace
open MeasureTheory ProbabilityTheory
open scoped ENNReal

local instance {A : Type} : MeasurableSpace (List A) := ⊤
local instance {A : Type} : DiscreteMeasurableSpace (List A) := ⟨fun _ => trivial⟩

/-- Local finite dependence follows the exact writer through its actual states.
The state may contain arbitrary function-valued payloads; no countability of
that state type is used. -/
theorem eventsOf_finiteRead {State Op : Type}
    (step : IdealKey.Tape → State → Op → State)
    (events : IdealKey.Tape → State → Op → List Event)
    (hstep : ∀ state op, IdealKey.FiniteRead (fun tape => step tape state op))
    (hevents : ∀ state op, IdealKey.FiniteRead (fun tape => events tape state op))
    (ops : List Op) (initial : IdealKey.Tape → State)
    (hinit : IdealKey.FiniteRead initial) :
    IdealKey.FiniteRead (fun tape => eventsOf (step tape) (events tape) (initial tape) ops) := by
  induction ops generalizing initial with
  | nil => exact IdealKey.FiniteRead.const []
  | cons op ops ih =>
    have hnow := hinit.bind (fun state tape => events tape state op) (fun state => hevents state op)
    have hnext := hinit.bind (fun state tape => step tape state op) (fun state => hstep state op)
    exact (hnow.pair (ih _ hnext)).comp (fun p => p.1 ++ p.2)

/-- Both adaptive operation selection and a selected stopping prefix can be
computed from prior exact replies; only their actual finite-read witnesses
are needed. -/
theorem dynamic_events_finiteRead {State Op : Type}
    (step : IdealKey.Tape → State → Op → State)
    (events : IdealKey.Tape → State → Op → List Event)
    (hstep : ∀ state op, IdealKey.FiniteRead (fun tape => step tape state op))
    (hevents : ∀ state op, IdealKey.FiniteRead (fun tape => events tape state op))
    (ops : IdealKey.Tape → List Op) (hops : IdealKey.FiniteRead ops)
    (initial : IdealKey.Tape → State) (hinit : IdealKey.FiniteRead initial) :
    IdealKey.FiniteRead (fun tape => eventsOf (step tape) (events tape) (initial tape) (ops tape)) :=
  hops.bind _ (fun xs => eventsOf_finiteRead step events hstep hevents xs initial hinit)

/-- The operation source may be the already registered adaptive interaction.
Its records are chosen from prior exact rows; the writer receives no stored
key map and does not assume independence of that interaction. -/
theorem adaptive_events_finiteRead {State Op : Type}
    (cfg : Model.Config) (sh : Model.Hierarchy.Shapes)
    (g : Model.Online.OnlineGeom) (schedule : Model.Online.Schedule)
    {m : Nat} (client : Model.Adaptive.AdaptiveRun m)
    (step : IdealKey.Tape → State → Op → State)
    (events : IdealKey.Tape → State → Op → List Event)
    (hstep : ∀ state op, IdealKey.FiniteRead (fun tape => step tape state op))
    (hevents : ∀ state op, IdealKey.FiniteRead (fun tape => events tape state op))
    (selectOps : List Model.OnlineBatch.Op × List (Fin m → Nat) → List Op)
    (selectInitial : List Model.OnlineBatch.Op × List (Fin m → Nat) → State) :
    IdealKey.FiniteRead (fun tape =>
      let interaction := Model.Adaptive.interact cfg sh g schedule client
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
      eventsOf (step tape) (events tape) (selectInitial interaction) (selectOps interaction)) := by
  have hread := IdealAdaptiveFiniteRead cfg sh g schedule m client
  exact dynamic_events_finiteRead step events hstep hevents
    _ (hread.comp selectOps) _ (hread.comp selectInitial)

theorem comparisons_fibres (rule : Rule) (events : IdealKey.Tape → List Event)
    (hread : IdealKey.FiniteRead events) :
    ∀ l, MeasurableSet {tape | comparisons rule (events tape) = l} := by
  intro l
  exact (IdealFiniteReadMeasurable _ _ (hread.comp (comparisons rule)))
    (measurableSet_singleton l)

/-- Independence is proved on the unconditional product experiment, rather
than required of the event writer. -/
theorem comparisons_independent {Stored : Type} [MeasurableSpace Stored]
    (ν : Measure Stored) [IsProbabilityMeasure ν] (rule : Rule)
    (events : IdealKey.Tape → List Event) (hread : IdealKey.FiniteRead events) :
    IndepFun (fun p : IdealKey.Tape × Stored => comparisons rule (events p.1))
      Prod.snd (IdealKey.tapeLaw.prod ν) :=
  indepFun_prod (IdealFiniteReadMeasurable _ _ (hread.comp (comparisons rule))) measurable_id

theorem mem_comparisons (rule : Rule) (events : List Event) (c : Comparison LogicalKey) :
    c ∈ comparisons rule events ↔ ∃ e ∈ events, e.rule = rule ∧ e.comparison = c := by
  simp only [comparisons, List.mem_map, List.mem_filter, beq_iff_eq]
  aesop

theorem bad_iff (stored : LogicalKey → Fingerprint 128) (events : List Event) :
    (∃ e ∈ events, e.bad stored) ↔
      (∃ c ∈ comparisons .rebuild32 events, falseMatch (count := 4) (width := 32) stored c) ∨
      (∃ c ∈ comparisons .dense64 events, falseMatch (count := 2) (width := 64) stored c) := by
  constructor
  · rintro ⟨e, he, hb⟩
    cases hr : e.rule with
    | rebuild32 => exact Or.inl ⟨e.comparison, (mem_comparisons _ _ _).mpr ⟨e, he, hr, rfl⟩,
        by simpa [Event.bad, hr] using hb⟩
    | dense64 => exact Or.inr ⟨e.comparison, (mem_comparisons _ _ _).mpr ⟨e, he, hr, rfl⟩,
        by simpa [Event.bad, hr] using hb⟩
  · rintro (⟨c, hc, hb⟩ | ⟨c, hc, hb⟩)
    · obtain ⟨e, he, hr, rfl⟩ := (mem_comparisons _ _ _).mp hc
      exact ⟨e, he, by simpa [Event.bad, hr] using hb⟩
    · obtain ⟨e, he, hr, rfl⟩ := (mem_comparisons _ _ _).mp hc
      exact ⟨e, he, by simpa [Event.bad, hr] using hb⟩

theorem weight_map {A B : Type} (f : A → B) (count : Nat) (cmps : List (Comparison A)) :
    weight count (mapComparisons f cmps) = weight count cmps := by
  simp [mapComparisons, weight, List.map_map, Function.comp_def]

/-- The actual reference writer's two rule projections supply the hypotheses
of the existing random-function theorem. Both geometries share the same
normalization tape. No independence between individual comparisons is used. -/
theorem independent_bound (events : IdealKey.Tape → List Event)
    (hread : IdealKey.FiniteRead events) (rebuildBudget denseBudget : Nat)
    (hrebuild : ∀ tape, weight 4 (comparisons .rebuild32 (events tape)) ≤ rebuildBudget)
    (hdense : ∀ tape, weight 2 (comparisons .dense64 (events tape)) ≤ denseBudget) :
    (IdealKey.tapeLaw.prod (tapeLaw 128)) {p | ∃ e ∈ events p.1, e.bad p.2} ≤
      min 1 (matchBound 4 32 rebuildBudget + matchBound 2 64 denseBudget) := by
  have hr := NativeMatchIndependent IdealKey.tapeLaw 4 32 rebuildBudget
    (fun tape => comparisons .rebuild32 (events tape))
    (comparisons_fibres _ _ hread) hrebuild
  have hd := NativeMatchIndependent IdealKey.tapeLaw 2 64 denseBudget
    (fun tape => comparisons .dense64 (events tape))
    (comparisons_fibres _ _ hread) hdense
  apply le_min prob_le_one
  have heq : {p : IdealKey.Tape × Tape 128 | ∃ e ∈ events p.1, e.bad p.2} =
      {p | ∃ c ∈ comparisons .rebuild32 (events p.1), falseMatch (count := 4) (width := 32) p.2 c} ∪
      {p | ∃ c ∈ comparisons .dense64 (events p.1), falseMatch (count := 2) (width := 64) p.2 c} := by
    ext p
    exact bad_iff p.2 (events p.1)
  rw [heq]
  exact (measure_union_le _ _).trans (add_le_add hr hd)

/-- The sixteen-byte block adapter is injective only on its advertised
fixed-width domain, never on all logical byte strings. -/
theorem block16_inj {a b : LogicalKey} (ha : a.length = 16) (hb : b.length = 16)
    (h : block16 a = block16 b) : a = b := by
  apply (NativeKeyShort id Function.injective_id 16 (by decide) (by decide) a b ha hb).mp
  have heq := (segments 16 8).symm.injective h
  simpa [NativeKey.shortStored, ha, hb] using heq

theorem falseMatch_map_iff {count width : Nat}
    (σ : Fingerprint (width * count) → Fingerprint (width * count))
    (encode : LogicalKey → Fingerprint (width * count)) (c : Comparison LogicalKey)
    (hinj : ∀ p ∈ c.2, encode p = encode c.1 → p = c.1) :
    falseMatch (σ ∘ encode) c ↔ falseMatch σ (encode c.1, c.2.map encode) := by
  have hm : encode c.1 ∈ c.2.map encode ↔ c.1 ∈ c.2 := by
    constructor
    · intro h
      obtain ⟨p, hp, he⟩ := List.mem_map.mp h
      exact (hinj p hp he) ▸ hp
    · intro h
      exact List.mem_map.mpr ⟨c.1, h, rfl⟩
  simp only [falseMatch, hm, List.map_map, Function.comp_apply]

theorem permutation_comparison_bound (count width : Nat)
    (encode : LogicalKey → Fingerprint (width * count))
    (cmp : IdealKey.Tape → List (Comparison LogicalKey))
    (hread : IdealKey.FiniteRead cmp) (budget : Nat)
    (hbudget : ∀ tape, weight count (cmp tape) ≤ budget)
    (hinj : ∀ tape c, c ∈ cmp tape → ∀ k ∈ c.2, encode k = encode c.1 → k = c.1) :
    (IdealKey.tapeLaw.prod (permLaw (width * count)))
        {p | ∃ c ∈ cmp p.1, falseMatch (count := count) (width := width)
          (fun key => p.2 (encode key)) c} ≤ matchBound count width budget := by
  have hmeas := IdealFiniteReadMeasurable _ _ (hread.comp (mapComparisons encode))
  have hbound := NativeMatchPermutation IdealKey.tapeLaw count width budget
    (fun tape => mapComparisons encode (cmp tape))
    (fun l => hmeas (measurableSet_singleton l))
    (fun tape => (weight_map encode count (cmp tape)).trans_le (hbudget tape))
  convert hbound using 1
  congr 1
  ext p
  simp only [mapComparisons, List.mem_map]
  constructor
  · rintro ⟨c, hc, hb⟩
    exact ⟨(encode c.1, c.2.map encode), ⟨c, hc, rfl⟩,
      (falseMatch_map_iff p.2 encode c (hinj p.1 c hc)).mp hb⟩
  · rintro ⟨d, ⟨c, hc, rfl⟩, hb⟩
    exact ⟨c, hc, (falseMatch_map_iff p.2 encode c (hinj p.1 c hc)).mpr hb⟩

/-- Fixed-width sixteen-byte comparisons use the existing permutation theorem
through the native zero-filled block adapter. -/
theorem permutation_bound (events : IdealKey.Tape → List Event)
    (hread : IdealKey.FiniteRead events) (rebuildBudget denseBudget : Nat)
    (hrebuild : ∀ tape, weight 4 (comparisons .rebuild32 (events tape)) ≤ rebuildBudget)
    (hdense : ∀ tape, weight 2 (comparisons .dense64 (events tape)) ≤ denseBudget)
    (hwidth : ∀ tape e, e ∈ events tape →
      e.subject.length = 16 ∧ ∀ k ∈ e.partners, k.length = 16) :
    (IdealKey.tapeLaw.prod (permLaw 128))
        {p | ∃ e ∈ events p.1, e.bad (fun key => p.2 (block16 key))} ≤
      min 1 (matchBound 4 32 rebuildBudget + matchBound 2 64 denseBudget) := by
  have hinj : ∀ rule tape c, c ∈ comparisons rule (events tape) →
      ∀ k ∈ c.2, block16 k = block16 c.1 → k = c.1 := by
    intro rule tape c hc k hk he
    obtain ⟨e, hevent, _, rfl⟩ := (mem_comparisons rule _ _).mp hc
    exact block16_inj ((hwidth tape e hevent).2 k hk) (hwidth tape e hevent).1 he
  have hr := permutation_comparison_bound 4 32 block16
    (fun tape => comparisons .rebuild32 (events tape))
    (hread.comp (comparisons .rebuild32)) rebuildBudget hrebuild (hinj .rebuild32)
  have hd := permutation_comparison_bound 2 64 block16
    (fun tape => comparisons .dense64 (events tape))
    (hread.comp (comparisons .dense64)) denseBudget hdense (hinj .dense64)
  apply le_min prob_le_one
  have heq : {p : IdealKey.Tape × Equiv.Perm (Fingerprint 128) |
      ∃ e ∈ events p.1, e.bad (fun key => p.2 (block16 key))} =
      {p | ∃ c ∈ comparisons .rebuild32 (events p.1),
        falseMatch (count := 4) (width := 32) (fun key => p.2 (block16 key)) c} ∪
      {p | ∃ c ∈ comparisons .dense64 (events p.1),
        falseMatch (count := 2) (width := 64) (fun key => p.2 (block16 key)) c} := by
    ext p
    exact bad_iff _ (events p.1)
  rw [heq]
  exact (measure_union_le _ _).trans (add_le_add hr hd)

end RebuildBound.NativeMatchInventoryProof

namespace RebuildBound.NativeMatchInventoryProof
open Spec Spec.NativeMatch MeasureTheory
open scoped ENNReal

theorem combined_reserve (rebuild dense h : Nat) :
    min 1 (matchBound 4 32 (h*rebuild) + matchBound 2 64 (h*dense)) ≤
      (h : ℝ≥0∞) * (((rebuild+dense : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞)^128) := by
  apply (min_le_right _ _).trans
  apply (add_le_add (min_le_right _ _) (min_le_right _ _)).trans_eq
  simp only [show 32*4=128 by decide,show 64*2=128 by decide,Nat.cast_mul,Nat.cast_add]
  rw [← ENNReal.add_div,← mul_add,mul_div_assoc]
end RebuildBound.NativeMatchInventoryProof

namespace RebuildBound.NativeMatchProductionProof
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatch Spec.NativeMatchTrace
open Spec.NativeMatchPhysical Spec.NativeMatchHierarchy Spec.NativeMatchProduction Spec.NativeNormalize
open MeasureTheory ProbabilityTheory
open scoped ENNReal

local instance : MeasurableSpace (List (Comparison LogicalKey)) := ⊤
local instance : DiscreteMeasurableSpace (List (Comparison LogicalKey)) := ⟨fun _ => trivial⟩

theorem inventory_read (checked : NativeMatchGlobalFiniteRead_statement)
    {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) : IdealKey.FiniteRead ctx.inventory := by
  classical
  have hr := (IdealAdaptiveFiniteRead ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule
    ctx.transcriptWidth ctx.client).comp
    (fun result => (⟨result.1,ctx.client.init,ctx.client.unsh⟩ : OnlineBatch.BatchRun))
  have hf := (hr.comp (OnlineBatch.traceOf ctx.unit)).bind _
    (IdealFailureProof.fails_finiteRead ctx.geo.cfg ctx.geo.shapes)
  have hs := hr.comp (fun run => ready ctx.unit run ctx.snapshots ctx.accesses = false)
  have he := (checked.2 ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.transcriptWidth ctx.client ctx.accesses).1
  have hh := ((hf.pair hs).pair he).comp (fun p => if p.1.1 ∨ p.1.2 then [] else p.2)
  convert hh using 1
  funext tape
  dsimp only [Context.inventory,physicalChargedEvents,adaptiveEvents,Adaptive.realized]
  congr 1

theorem independent (checked : NativeMatchGlobalFiniteRead_statement)
    {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (Stored : Type) [MeasurableSpace Stored]
    (law : Measure Stored) [IsProbabilityMeasure law] (rule : Rule) :
    IndepFun (fun p : IdealKey.Tape × Stored => comparisons rule (ctx.inventory p.1)) Prod.snd
      (IdealKey.tapeLaw.prod law) :=
  NativeMatchInventoryProof.comparisons_independent law rule ctx.inventory (inventory_read checked ctx)

theorem random_function (read : NativeMatchGlobalFiniteRead_statement)
    (count : NativeMatchAdaptiveRebuildInventory_statement)
    {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hh : 1 ≤ h) (hv : ctx.Valid) :
    (IdealKey.tapeLaw.prod (tapeLaw 128)) {p | ∃ e ∈ ctx.inventory p.1, e.bad p.2} ≤
      (h:ℝ≥0∞)*((NativeMatchInventory.weight member initialized:ℝ≥0∞)/(2:ℝ≥0∞)^128) := by
  have hb := NativeMatchInventoryProof.independent_bound ctx.inventory (inventory_read read ctx)
    (h*(64^4*NativeMatchInventory.sMin member initialized))
    (h*(2^32*NativeMatchInventory.denseBuckets member*14*8^2))
    (fun tape => (weights count ctx hm hh hv tape).1)
    (fun tape => (weights count ctx hm hh hv tape).2)
  exact hb.trans (NativeMatchInventoryProof.combined_reserve _ _ h)

theorem combined (read : NativeMatchGlobalFiniteRead_statement)
    (count : NativeMatchAdaptiveRebuildInventory_statement)
    {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hh : 1 ≤ h) (hv : ctx.Valid) :
    (IdealKey.tapeLaw.prod (tapeLaw 128))
      {p | ctx.capacityBad p.1 ∨ ∃ e ∈ ctx.inventory p.1, e.bad p.2} ≤
        (h:ℝ≥0∞)*ENNReal.ofReal (1/(2:ℝ)^64) := by
  have hp := measurePreserving_fst (μ := IdealKey.tapeLaw) (ν := tapeLaw 128)
  have hc := Measure.le_map_apply (μ := IdealKey.tapeLaw.prod (tapeLaw 128))
    hp.measurable.aemeasurable {tape | ctx.capacityBad tape}
  rw [hp.map_eq] at hc
  have hu := measure_union_le (μ := IdealKey.tapeLaw.prod (tapeLaw 128))
    {p : IdealKey.Tape × Tape 128 | ctx.capacityBad p.1}
    {p | ∃ e ∈ ctx.inventory p.1, e.bad p.2}
  exact (hu.trans (add_le_add hc (random_function read count ctx hm hh hv))).trans
    (capacity_reserve ctx hm hh hv)
end RebuildBound.NativeMatchProductionProof

namespace RebuildBound.NativeMatchRouting16Proof
open Model Spec Spec.NativeMatch Spec.NativeNormalize Spec.NativeMatchRouting16 MeasureTheory

instance : IsProbabilityMeasure law := by unfold law; infer_instance

theorem block_injective {a b : LogicalKey} (ha : a.length = 16) (hb : b.length = 16)
    (he : block a = block b) : a = b := by
  apply (NativeKeyShort id Function.injective_id 16 (by decide) (by decide) a b ha hb).mp
  have h := (segments 16 8).symm.injective he
  simpa [NativeKey.shortStored,ha,hb] using h

theorem index_injective : Function.Injective index := by
  intro a b he
  cases a with
  | inl a =>
    rcases a with ⟨fa,ka⟩
    cases b with
    | inl b =>
      rcases b with ⟨fb,kb⟩
      by_cases ha : ka.length = 16 <;> by_cases hb : kb.length = 16
      · simp only [index,ha,hb,ite_true,Sum.inl.injEq,Prod.mk.injEq] at he
        rw [he.1,block_injective ha hb he.2]
      · simp [index,ha,hb] at he
      · simp [index,ha,hb] at he
      · simpa [index,ha,hb] using he
    | inr b => by_cases ha : ka.length = 16 <;> simp [index,ha] at he
  | inr a =>
    cases b with
    | inl b => by_cases hb : b.2.length = 16 <;> simp [index,hb] at he
    | inr b => simpa [index] using he

theorem canonical_measurable : Measurable canonical :=
  Measurable.of_eval fun c => measurable_pi_apply (index c)

theorem canonical_law : law.map canonical = IdealKey.tapeLaw :=
  Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Coord => wordLaw 64) index_injective

theorem permute_injective (σ : Equiv.Perm (Fingerprint 128)) : Function.Injective (permute σ) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hp : a.1 = b.1 ∧ a.2 = b.2 := by simpa [permute,Prod.mk.injEq] using h
      exact congrArg Sum.inl (Prod.ext hp.1 hp.2)
    | inr b => simp [permute] at h
  | inr a =>
    cases b with
    | inl b => simp [permute] at h
    | inr b => simpa [permute] using h

theorem reindex_measurable (σ : Equiv.Perm (Fingerprint 128)) :
    Measurable (fun tape : Tape => tape ∘ permute σ) :=
  Measurable.of_eval fun c => measurable_pi_apply (permute σ c)

theorem reindex_law (σ : Equiv.Perm (Fingerprint 128)) :
    law.map (fun tape : Tape => tape ∘ permute σ) = law :=
  Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Coord => wordLaw 64) (permute_injective σ)

/-- This is precisely NativeMatchRelabel on the real stored-key coordinates;
the extension leaves every dummy and every out-of-domain coordinate unchanged. -/
theorem real_relabel (σ : Equiv.Perm (Fingerprint 128)) (tape : Tape) :
    (fun c => (tape ∘ permute σ) (.inl c)) =
      relabel σ (fun c => tape (.inl c)) := rfl

theorem real_joint_law :
    ((permLaw 128).prod (storedTapeLaw IdealKey.Family 128 64)).map
      (fun p => (p.1,relabel p.1 p.2)) =
        (permLaw 128).prod (storedTapeLaw IdealKey.Family 128 64) :=
  (NativeMatchRelabel IdealKey.Family 128 64).2

/-- A common unconditional experiment supplies the full canonical tape jointly
independent of the normalization permutation. No inventory hypothesis occurs. -/
theorem native_joint_law :
    Measurable (fun p : Equiv.Perm (Fingerprint 128) × Tape => (p.1,native p.1 p.2)) ∧
    ((permLaw 128).prod law).map (fun p => (p.1,native p.1 p.2)) =
      (permLaw 128).prod IdealKey.tapeLaw := by
  have hm : Measurable (Function.uncurry fun (σ : Equiv.Perm (Fingerprint 128))
      (tape : Tape) => tape ∘ permute σ) :=
    measurable_from_prod_countable_right reindex_measurable
  have hs := (MeasurePreserving.id (permLaw 128)).skew_product hm (ae_of_all _ reindex_law)
  have hc : MeasurePreserving canonical law IdealKey.tapeLaw := ⟨canonical_measurable,canonical_law⟩
  have hj := ((MeasurePreserving.id (permLaw 128)).prod hc).comp hs
  exact ⟨hj.measurable,hj.map_eq⟩

theorem native_real (σ : Equiv.Perm (Fingerprint 128)) (tape : Tape)
    (family : IdealKey.Family) (key : LogicalKey) (hk : key.length = 16) :
    native σ tape (.inl (family,key)) = tape (.inl (family,σ (block key))) := by
  simp [native,index,permute,hk]
theorem native_dummy (σ : Equiv.Perm (Fingerprint 128)) (tape : Tape) (dummy : Nat × Nat) :
    native σ tape (.inr dummy) = tape (.inr (.inr dummy)) := rfl
end RebuildBound.NativeMatchRouting16Proof

namespace RebuildBound.NativeMatchRouting16Bound
open Model Spec Spec.NativeMatch Spec.NativeNormalize Spec.NativeMatchTrace MeasureTheory
open scoped ENNReal

theorem bound (events : IdealKey.Tape → List Event) (hread : IdealKey.FiniteRead events)
    (rebuildBudget denseBudget : Nat)
    (hrebuild : ∀ tape, weight 4 (comparisons .rebuild32 (events tape)) ≤ rebuildBudget)
    (hdense : ∀ tape, weight 2 (comparisons .dense64 (events tape)) ≤ denseBudget)
    (hwidth : ∀ tape e, e ∈ events tape → e.subject.length = 16 ∧ ∀ key ∈ e.partners, key.length = 16) :
    ((permLaw 128).prod NativeMatchRouting16.law)
      {p | ∃ e ∈ events (NativeMatchRouting16.native p.1 p.2),
        e.bad (fun key => p.1 (NativeMatchRouting16.block key))} ≤
      min 1 (matchBound 4 32 rebuildBudget + matchBound 2 64 denseBudget) := by
  have hp : MeasurePreserving (fun p : Equiv.Perm (Fingerprint 128) × NativeMatchRouting16.Tape =>
      (p.1,NativeMatchRouting16.native p.1 p.2)) ((permLaw 128).prod NativeMatchRouting16.law)
      ((permLaw 128).prod IdealKey.tapeLaw) :=
    ⟨NativeMatchRouting16Proof.native_joint_law.1,NativeMatchRouting16Proof.native_joint_law.2⟩
  have hs := (Measure.measurePreserving_swap (μ := permLaw 128) (ν := IdealKey.tapeLaw)).comp hp
  have hm := Measure.le_map_apply (μ := (permLaw 128).prod NativeMatchRouting16.law) hs.measurable.aemeasurable
    {p : IdealKey.Tape × Equiv.Perm (Fingerprint 128) | ∃ e ∈ events p.1,
      e.bad (fun key => p.2 (block16 key))}
  rw [hs.map_eq] at hm
  exact hm.trans (NativeMatchInventoryProof.permutation_bound events hread rebuildBudget denseBudget
    hrebuild hdense hwidth)
end RebuildBound.NativeMatchRouting16Bound

namespace RebuildBound.NativeMatchProductionProof
open Model Model.Hierarchy Model.Online Spec Spec.NativeMatch Spec.NativeMatchTrace
open Spec.NativeMatchPhysical Spec.NativeMatchHierarchy Spec.NativeMatchProduction Spec.NativeNormalize
open MeasureTheory
open scoped ENNReal

theorem run_ready {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) : RunReady member initialized h (ctx.run tape) := by
  obtain ⟨_,hcorrect,_⟩ := contracts ctx hm hv tape
  exact ⟨hv.1.1,init_bound ctx hm hv tape,hcorrect.2.1⟩

theorem inventory_keys (checked : NativeMatchInventoryKeys_statement)
    {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (tape : IdealKey.Tape) :
    ∀ e ∈ ctx.inventory tape,
      e.subject ∈ NativeRoutingActual.usedKeys (ctx.run tape) ∧
        ∀ key ∈ e.partners, key ∈ NativeRoutingActual.usedKeys (ctx.run tape) := by
  by_cases hc : ctx.capacityBad tape ∨ ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = false
  · have he : ctx.inventory tape = [] := by
      unfold Context.inventory physicalChargedEvents
      exact ite_eq_left hc
    simp [he]
  · have he : ctx.inventory tape = referenceEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape)
        ctx.schedule (IdealHierarchy.words tape) ctx.accesses := by
      unfold Context.inventory physicalChargedEvents
      exact ite_eq_right hc
    rw [he]
    exact checked member initialized hm h (ctx.run tape) (run_ready ctx hm hv tape)
      ctx.schedule (IdealHierarchy.words tape) ctx.accesses (fun hf => hc (Or.inl hf))

theorem sixteen (read : NativeMatchGlobalFiniteRead_statement)
    (count : NativeMatchAdaptiveRebuildInventory_statement) (keys : NativeMatchInventoryKeys_statement)
    {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hh : 1 ≤ h) (hv : ctx.Valid)
    (hwidth : ∀ tape key, key ∈ NativeRoutingActual.usedKeys (ctx.run tape) → key.length = 16) :
    ((permLaw 128).prod NativeMatchRouting16.law)
      {p | ∃ e ∈ ctx.inventory (NativeMatchRouting16.native p.1 p.2),
        e.bad (fun key => p.1 (NativeMatchRouting16.block key))} ≤
      (h:ℝ≥0∞)*((NativeMatchInventory.weight member initialized:ℝ≥0∞)/(2:ℝ≥0∞)^128) := by
  have hb := NativeMatchRouting16Bound.bound ctx.inventory (inventory_read read ctx)
    (h*(64^4*NativeMatchInventory.sMin member initialized))
    (h*(2^32*NativeMatchInventory.denseBuckets member*14*8^2))
    (fun tape => (weights count ctx hm hh hv tape).1)
    (fun tape => (weights count ctx hm hh hv tape).2) (fun tape e he =>
      ⟨hwidth tape e.subject ((inventory_keys keys ctx hm hv tape e he).1),
        fun key hk => hwidth tape key ((inventory_keys keys ctx hm hv tape e he).2 key hk)⟩)
  exact hb.trans (NativeMatchInventoryProof.combined_reserve _ _ h)
end RebuildBound.NativeMatchProductionProof

namespace RebuildBound.NativeMatchProductionProof
open Model Spec Spec.NativeMatchProduction Spec.NativeRoutingActual

theorem used_width {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) (width : Nat) (hw : InputWidth ctx.client width) :
    ∀ tape key, key ∈ usedKeys (ctx.run tape) → key.length = width :=
  NativeRoutingActualProof.realized_width ctx.geo (structural ctx hm).1 ctx.unit ctx.schedule
    ctx.client (alignment member hm initialized h) (by change 0 < 64; decide) hv.1.1 width hw
end RebuildBound.NativeMatchProductionProof
namespace RebuildBound
open Model Spec NativeMatchProductionProof

theorem NativeMatchProductionDense : NativeMatchProductionDense_statement := by
  intro member initialized hm h ctx hv tape hr
  exact dense_budget ctx hm hv tape hr

theorem NativeMatchProductionFiniteRead : NativeMatchProductionFiniteRead_statement := by
  intro member initialized h ctx
  exact inventory_read NativeMatchGlobalFiniteRead ctx

theorem NativeMatchProductionWeights : NativeMatchProductionWeights_statement := by
  intro member initialized hm h hh ctx hv tape
  exact weights NativeMatchAdaptiveRebuildInventory ctx hm hh hv tape

theorem NativeMatchProductionIndependence : NativeMatchProductionIndependence_statement := by
  intro member initialized h ctx Stored _ law _ rule
  exact independent NativeMatchGlobalFiniteRead ctx Stored law rule

theorem NativeMatchProductionRandomFunction : NativeMatchProductionRandomFunction_statement := by
  intro member initialized hm h hh ctx hv
  exact random_function NativeMatchGlobalFiniteRead NativeMatchAdaptiveRebuildInventory ctx hm hh hv

theorem NativeMatchProductionSixteen : NativeMatchProductionSixteen_statement := by
  intro member initialized hm h hh ctx hv hw
  apply sixteen NativeMatchGlobalFiniteRead NativeMatchAdaptiveRebuildInventory NativeMatchInventoryKeys ctx hm hh hv
  exact NativeRoutingActualProof.realized_width ctx.geo (structural ctx hm).1 ctx.unit ctx.schedule
    ctx.client (alignment member hm initialized h) (by change 0 < 64; decide) hv.1.1 16 hw

theorem NativeMatchProductionCombined : NativeMatchProductionCombined_statement := by
  intro member initialized hm h hh ctx hv
  exact combined NativeMatchGlobalFiniteRead NativeMatchAdaptiveRebuildInventory ctx hm hh hv
end RebuildBound
