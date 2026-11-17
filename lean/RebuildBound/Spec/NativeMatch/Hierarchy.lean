import RebuildBound.Spec.NativeMatch.Jobs
import RebuildBound.Spec.ConfigurationFamily
import RebuildBound.Spec.ApiStructural
import RebuildBound.Spec.IdealFailure
import RebuildBound.Spec.HierarchyChunkBase
import RebuildBound.Spec.NativeMatch.DenseTrace

/-! Physical matching continuation and exact-reference inventory for the
production family. Trailing unused slots are related by lane equality; no
state is repacked after deletion. Native capacity-stop timing and compiled
instruction execution remain separate obligations. -/

namespace RebuildBound.Spec.NativeMatchDirectJobTrace
open Model Model.DirectJob NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchJobTrace

/-- A genuine DFS repartitions the surviving pool into its range outputs.
Only this branch creates new single-page groups; the direct branch retains
its original groups through every deletion. -/
def dfsInitialGhost (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) : FinishGhost :=
  let route := (analyticalA g word inp.aMain).state
  let leaves := (distributeA g word (pageRecords (poolExact sources raw))).leaves
  ⟨finishInitial b route.main leaves,onePageLeaves leaves⟩

def dfsInitialNative (stored : LogicalKey → Stored) (g : Geometry) (word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page) : FinishGhost :=
  let route := (analyticalA g word inp.aMain).state
  let leaves := (distributeA g word (pageRecords (poolNative stored sources raw))).leaves
  ⟨finishInitial b route.main leaves,onePageLeaves leaves⟩

end RebuildBound.Spec.NativeMatchDirectJobTrace

namespace RebuildBound.Spec.NativeMatchDirectPlanTrace
open Model Model.DirectJob NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchJobTrace
open NativeMatchDirectJobTrace

def initialGhost (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) : FinishGhost :=
  match g.ranges with
  | .direct => NativeMatchDirectJobTrace.initialGhost g word inp b sources raw
  | .dfs _ _ _ => dfsInitialGhost g word inp b sources raw

def initialNative (stored : LogicalKey → Stored) (g : Geometry) (word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page) : FinishGhost :=
  match g.ranges with
  | .direct => NativeMatchDirectJobTrace.initialNative stored g word inp b sources raw
  | .dfs _ _ _ => dfsInitialNative stored g word inp b sources raw

def events (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (shedPages tierPages : Nat) : List Event :=
  poolTrace sources raw ++ NativeMatchJobTrace.finishEvents g.finishTopology word b.bLanes
    (initialGhost g word inp b sources raw) ++
    NativeMatchJobTrace.drainEvents shedPages tierPages (finishState g word inp b)

def native (stored : LogicalKey → Stored) (g : Geometry) (word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page) (shedPages tierPages : Nat) : Output :=
  let finish := finishNative stored g.finishTopology word b.bLanes
    (initialNative stored g word inp b sources raw)
  ⟨finish.state.main,NativeMatchJobTrace.drainNative stored shedPages tierPages finish.state⟩

end RebuildBound.Spec.NativeMatchDirectPlanTrace

namespace RebuildBound.Spec.NativeMatchPrefixProducer
open Model Model.DirectJob NativeMatch NativeMatch.Lanes NativeMatchTrace

def pages (units : List Bucket) : List Page := units.map Page.ofBucket

def data (units : List Bucket) (i : Nat) : DirectMask64.Payload := ((pages units).getD i default).1

def masks (units : List Bucket) : List Mask := (pages units).map Prod.snd

def events (units : List Bucket) : List Event :=
  prefixTrace (data units) 1 (masks units) (List.range (DirectMaskIndex.pairs 1 units.length))

def masked (stored : LogicalKey → Stored) (units : List Bucket) : List Bucket :=
  DirectMask64.buckets (data units)
    (prefixRun stored (data units) 1 (masks units) (List.range (DirectMaskIndex.pairs 1 units.length)))

/-- The producer indexes the actual surviving payload records. It does not
restore records from an independently recomputed exact winner list after a
false positive has deleted a source lane. -/
def nativeBuildB (stored : LogicalKey → Stored) (g : Geometry) (word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) : Except CheckEvent Table :=
  let masked := masked stored inp.units
  let records := DirectMasks.records masked
  let chunks := DirectMaskedRecords.chunks masked
  let homes := DirectGroups.groups g.U
    (fun i => DirectPrefix.cachedHome word g.U records[i]!) chunks.flatten
  let remaining := chunks.map (fun source => DirectRemaining.run 64 source homes)
  match drainBounded .produceB (bSite g) g.bCapacity 0 [] remaining with
  | .error e => .error e
  | .ok tier => .ok ⟨(DirectB.main 64 homes).map (fun rs => rs.map (fun i => records[i]!)),
      tier.map (fun i => records[i]!)⟩

end RebuildBound.Spec.NativeMatchPrefixProducer

namespace RebuildBound.Spec.NativeMatchHierarchy
open Model

/-- Physical lanes agree at every address. Only trailing unused storage may
have a different list length; internal holes and record order are preserved. -/
def LaneEq (a b : Bucket) : Prop := ∀ i, a.getD i none = b.getD i none

def OutputEq (a b : Output) : Prop := a.main = b.main ∧ LaneEq a.tier b.tier

end RebuildBound.Spec.NativeMatchHierarchy

namespace RebuildBound.Spec.NativeMatchHierarchy
open Model Model.Hierarchy Model.DirectJob NativeMatchTrace

/-- Public slot capacities determine physical page allocations. The production
family uses multiples of 64; this definition is total for other capacities. -/
def pageAllocation (slots : Nat) : Nat := (slots+63)/64

def directSources (b : Table) : List Page := [Page.ofRecords b.tier]

def directRaw (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (prev : Output) : List Page :=
  NativeMatchDirectJobTrace.allocatedRaw g word inp (pageAllocation g.routeCapacity)
    (pageAllocation g.radixCapacity) (bucketPages (pageAllocation g.aTierCapacity) prev.tier)

def directEvents (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (prev : Output) : List Event :=
  NativeMatchPrefixProducer.events inp.units ++
    match buildB g word inp with
    | .error _ => []
    | .ok b => if g.digit = 1 then [] else
        NativeMatchDirectPlanTrace.events g word inp b (directSources b) (directRaw g word inp prev)
          (pageAllocation g.insertionCapacity) (pageAllocation g.outputCapacity)

/-- A reference job's comparison inventory uses the actual reference inputs
and each original tier's allocated physical pages. No stored-key map occurs.
Initialization and top preparation reuse their existing nonmatching paths. -/
def jobEvents (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) : JobId → List Event
  | .ordinary level ordinal =>
    let digit := Config.digitOf (cfg.fanout level) ordinal
    if level = 1 then
      let prev := if digit = 1 then emptyOutput else Hierarchy.table cfg sh tr words 1 (ordinal-1)
      directEvents (sh.direct digit) (jobWord cfg words 1 ordinal)
        (adopt prev (tr.units (ordinal-cfg.seed 1-1))) prev
    else if digit = 1 then [] else
      let g := sh.sep level digit
      NativeMatchJobTrace.separatedEvents engineRule g (jobWord cfg words level ordinal)
        (sepInputsAt cfg sh tr words level ordinal) (engineOps g)
        (bucketPages g.aTierPages (Hierarchy.table cfg sh tr words level (ordinal-1)).tier)
  | .topFinish ordinal =>
    let prev := Hierarchy.table cfg sh tr words cfg.levels (ordinal-1)
    let prepared := prepOutput cfg sh tr words ordinal prev
    let carry := carryOf cfg sh tr words cfg.levels ordinal
    NativeMatchTopJobTrace.events sh.top tr.unsh (jobWord cfg words cfg.levels ordinal)
      (finishInputs prepared carry) (bucketPages sh.top.rPages prepared.tier)
      (bucketPages sh.top.bPages carry.tier)
  | .topPrepare _ => []
  | .initialization => []

end RebuildBound.Spec.NativeMatchHierarchy

namespace RebuildBound.Spec.NativeMatchHierarchy
open Model Model.Hierarchy Model.DirectJob NativeMatch NativeMatch.Lanes NativeMatchTrace

/-- Matching refinement of the direct producer and range plan. The native B
producer uses actual surviving records and may return failure. Later matching
phases use unlimited continuation; runtime stop/check timing is a separate
boundary, covered by the reference capacity event in agreement results. -/
def directNative (stored : LogicalKey → Stored) (g : Geometry) (word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (prev : Output) : Option Output :=
  match NativeMatchPrefixProducer.nativeBuildB stored g word inp with
  | .error _ => none
  | .ok b => some (if g.digit = 1 then finishOutput g b.bLanes (b.tier.map some)
      else NativeMatchDirectPlanTrace.native stored g word inp b (directSources b) (directRaw g word inp prev)
        (pageAllocation g.insertionCapacity) (pageAllocation g.outputCapacity))

def nativeStep (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes)
    (tr : Trace) (words : Words) (level ordinal : Nat) (prev carry : Output) : Option Output :=
  let digit := Config.digitOf (cfg.fanout level) ordinal
  if level = cfg.levels then
    let prepared := prepOutput cfg sh tr words ordinal prev
    some (NativeMatchTopJobTrace.native stored sh.top tr.unsh (jobWord cfg words level ordinal)
      (finishInputs prepared carry) (bucketPages sh.top.rPages prepared.tier)
      (bucketPages sh.top.bPages carry.tier))
  else if level = 1 then
    let prev := if digit = 1 then emptyOutput else prev
    directNative stored (sh.direct digit) (jobWord cfg words 1 ordinal)
      (adopt prev (tr.units (ordinal-cfg.seed 1-1))) prev
  else if digit = 1 then some carry else
    let g := sh.sep level digit
    some (NativeMatchJobTrace.separatedNative stored engineRule g (jobWord cfg words level ordinal)
      (sepInputs g prev carry) (engineOps g) (bucketPages g.aTierPages prev.tier))

/-- The existing hierarchy's same lexicographic dependency recursion, with
only its matching job transitions refined. There is no independent state
oracle; every parent consumes the recursively produced native child output. -/
def nativeTable (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes)
    (tr : Trace) (words : Words) : Nat → Nat → Option Output
  | level, ordinal =>
    if level = 0 ∨ cfg.levels < level ∨ ordinal ≤ cfg.seed level then
      some (base cfg sh tr words level)
    else do
      let prev ← nativeTable stored cfg sh tr words level (ordinal-1)
      let carry ← if level = 1 then some emptyOutput else
        nativeTable stored cfg sh tr words (level-1) (ordinal*cfg.fanout (level-1))
      nativeStep stored cfg sh tr words level ordinal prev carry
termination_by level ordinal => (level,ordinal)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

end RebuildBound.Spec.NativeMatchHierarchy

namespace RebuildBound.Spec.NativeMatchHierarchy
open Model Model.Hierarchy NativeMatchTrace IdealKey

def rebuildEvents (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) : List Event :=
  (cfg.potentialJobs.filter fun j => decide (WithinHorizon cfg j)).flatMap (jobEvents cfg sh tr words)

def referenceEvents (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (schedule : Online.Schedule) (words : Words) (n : Nat) : List Event :=
  rebuildEvents cfg sh (OnlineBatch.traceOf g run) words ++ batchPrefixEvents cfg sh g run schedule words n

def adaptiveEvents (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (schedule : Online.Schedule) {m : Nat} (client : Adaptive.AdaptiveRun m) (n : Nat)
    (tape : Tape) : List Event :=
  referenceEvents cfg sh g (Adaptive.realized cfg sh g schedule client
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)) schedule (IdealHierarchy.words tape) n

/-- This guard charges a capacity failure to its existing unconditional event.
The exact reference and its overflow continuation are not changed. -/
noncomputable def chargedEvents (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (schedule : Online.Schedule) {m : Nat} (client : Adaptive.AdaptiveRun m) (n : Nat)
    (tape : Tape) : List Event := by
  classical
  exact if Fails cfg sh (OnlineBatch.traceOf g (Adaptive.realized cfg sh g schedule client
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape))) (IdealHierarchy.words tape)
    then [] else adaptiveEvents cfg sh g schedule client n tape
end RebuildBound.Spec.NativeMatchHierarchy

namespace RebuildBound.Spec.NativeMatchHierarchy
open Model Model.Hierarchy Model.Online NativeMatch NativeMatch.Lanes

/-- Existing API structural correctness supplies these finite-run facts.
No bound on the number of historical distinct identities is required. -/
def RunReady (m : ConfigurationFamily.Member) (initialized : Bool) (h : Nat)
    (run : OnlineBatch.BatchRun) : Prop :=
  let geo := (m.geometry initialized).chunk h
  let tr := OnlineBatch.traceOf ⟨64,m.r0⟩ run
  (run.init.map Rec.key).Nodup ∧ tr.init.length ≤ geo.init.C/2*geo.init.T ∧
    UnshPromise geo.cfg geo.shapes tr

def OffEvents (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes)
    (tr : Trace) (words : Words) : Prop :=
  ∀ j ∈ cfg.potentialJobs, WithinHorizon cfg j →
    ∀ e ∈ jobEvents cfg sh tr words j, ¬e.bad stored

def RebuildMismatch (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes)
    (tr : Trace) (words : Words) : Prop :=
  ∃ level ordinal, time cfg level ordinal ≤ cfg.seed 1+cfg.ordinals 1 ∧
    ¬∃ out, nativeTable stored cfg sh tr words level ordinal = some out ∧
      OutputEq out (table cfg sh tr words level ordinal)

end RebuildBound.Spec.NativeMatchHierarchy

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.DirectJob Model.Online NativeMatch NativeMatch.Lanes NativeMatchTrace

/-- Actual chronological prefix masks feed the existing B producer, including
record restoration from the records that really survived the native masks. -/
def NativeMatchPrefixProducer_statement : Prop :=
  ∀ (_bridge : NativeMatchLanesBridge_statement) (stored : LogicalKey → Stored)
    (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs),
    (∀ bucket ∈ inp.units, bucket.length ≤ 64) →
    (∀ bucket ∈ inp.units, (bucket.recs.map Rec.key).Nodup) →
    (∀ e ∈ NativeMatchPrefixProducer.events inp.units, ¬e.bad stored) →
    NativeMatchPrefixProducer.nativeBuildB stored g word inp = buildB g word inp

/-- Complete direct and DFS range plans, with the physical groups selected by
that plan, finish offers and both final class directions. -/
def NativeMatchDirectPlanFull_statement : Prop :=
  ∀ (_bridge : NativeMatchLanesBridge_statement) (_retained : NativeMatchRetained_statement)
    (_classes : NativeMatchClassBridge_statement) (stored : LogicalKey → Stored)
    (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (b : Table)
    (sources raw : List Page) (shedPages tierPages : Nat),
    g.Valid → 2 ≤ g.digit → inp.Valid g oldWord → buildB g word inp = .ok b →
    g.bCapacity ≤ 64 → pageRecords sources = b.tier →
    pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier →
    DirectJob.firstFailure (distributeA g word
      (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).trace = none →
    DirectJob.firstFailure (analyticalFinish g word b (analyticalA g word inp.aMain).state.main
      (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves).trace = none →
    g.insertionCapacity ≤ 64*shedPages → g.outputCapacity ≤ 64*tierPages →
    (∀ e ∈ NativeMatchDirectPlanTrace.events g word inp b sources raw shedPages tierPages, ¬e.bad stored) →
    NativeMatchDirectPlanTrace.native stored g word inp b sources raw shedPages tierPages =
      ⟨(NativeMatchDirectJobTrace.finishState g word inp b).main,
       (sDrain (NativeMatchDirectJobTrace.finishState g word inp b)).1 ++
        List.replicate (64*tierPages-(sDrain (NativeMatchDirectJobTrace.finishState g word inp b)).1.length) none⟩

/-- Every actual requester unit has its allocated physical width, and the
chronological prefix has at most its configured number of units. -/
def NativeMatchRequesterLayout_statement : Prop :=
  ∀ (g : OnlineGeom) (run : OnlineBatch.BatchRun), 0 < g.unitEntries → ∀ i,
    ((OnlineBatch.traceOf g run).units i).length ≤ g.unitsPerPrefix ∧
      ∀ bucket ∈ (OnlineBatch.traceOf g run).units i, bucket.length = g.unitEntries

/-- This is the actual recursive hierarchy, not independent local executions.
All public page/capacity links are checked on every family member and both
starts, and the prefix layout is obtained from the real requester. -/
def NativeMatchHierarchyReplay_statement : Prop :=
  ∀ (m : ConfigurationFamily.Member) (initialized : Bool), m ∈ ConfigurationFamily.members →
  ∀ (h : Nat) (run : OnlineBatch.BatchRun), NativeMatchHierarchy.RunReady m initialized h run →
  ∀ (stored : LogicalKey → Stored) (words : Words),
  let geo := (m.geometry initialized).chunk h
  let tr := OnlineBatch.traceOf ⟨64,m.r0⟩ run
  ¬Fails geo.cfg geo.shapes tr words → NativeMatchHierarchy.OffEvents stored geo.cfg geo.shapes tr words →
  ∀ level ordinal, time geo.cfg level ordinal ≤ geo.cfg.seed 1+geo.cfg.ordinals 1 →
    ∃ out, NativeMatchHierarchy.nativeTable stored geo.cfg geo.shapes tr words level ordinal = some out ∧
      NativeMatchHierarchy.OutputEq out (table geo.cfg geo.shapes tr words level ordinal)

/-- Any first mismatch on a finite dependency prefix is covered by the
unconditional reference capacity event or an event from an exact pre-state. -/
def NativeMatchHierarchyDivergence_statement : Prop :=
  ∀ (m : ConfigurationFamily.Member) (initialized : Bool), m ∈ ConfigurationFamily.members →
  ∀ (h : Nat) (run : OnlineBatch.BatchRun), NativeMatchHierarchy.RunReady m initialized h run →
  ∀ (stored : LogicalKey → Stored) (words : Words),
  let geo := (m.geometry initialized).chunk h
  let tr := OnlineBatch.traceOf ⟨64,m.r0⟩ run
  NativeMatchHierarchy.RebuildMismatch stored geo.cfg geo.shapes tr words →
    Fails geo.cfg geo.shapes tr words ∨
      ∃ j ∈ geo.cfg.potentialJobs, WithinHorizon geo.cfg j ∧
        ∃ e ∈ NativeMatchHierarchy.jobEvents geo.cfg geo.shapes tr words j, e.bad stored

/-- Exact reference job inventories have finite logical routing dependence.
Their construction has no stored-key argument. -/
def NativeMatchHierarchyFiniteRead_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (tr : Trace) (j : JobId),
    IdealKey.FiniteRead (fun tape =>
      NativeMatchHierarchy.jobEvents cfg sh tr (IdealHierarchy.words tape) j)

end RebuildBound.Spec

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online NativeMatchHierarchy

def NativeMatchGlobalFiniteRead_statement : Prop :=
  (∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineBatch.BatchRun)
      (schedule : Schedule) (n : Nat),
    IdealKey.FiniteRead (fun tape => referenceEvents cfg sh g run schedule (IdealHierarchy.words tape) n)) ∧
  (∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (schedule : Schedule)
      (m : Nat) (client : Adaptive.AdaptiveRun m) (n : Nat),
    IdealKey.FiniteRead (adaptiveEvents cfg sh g schedule client n) ∧
    IdealKey.FiniteRead (chargedEvents cfg sh g schedule client n))

end RebuildBound.Spec

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online NativeMatchTrace NativeMatchHierarchy

/-- The constructed comparison inventory uses only keys actually supplied by
this finite branch, including superseded and blind lanes. The capacity guard
can therefore discharge this fact on the unconditional product experiment. -/
def NativeMatchInventoryKeys_statement : Prop :=
  ∀ (m : ConfigurationFamily.Member) (initialized : Bool), m ∈ ConfigurationFamily.members →
  ∀ (h : Nat) (run : OnlineBatch.BatchRun), RunReady m initialized h run →
  ∀ (schedule : Schedule) (words : Words) (n : Nat),
  let geo := (m.geometry initialized).chunk h
  let tr := OnlineBatch.traceOf ⟨64,m.r0⟩ run
  let keys := run.init.map Rec.key ++ (OnlineBatch.slots run).map (fun slot => slot.record.key)
  ¬Fails geo.cfg geo.shapes tr words →
  ∀ e ∈ referenceEvents geo.cfg geo.shapes ⟨64,m.r0⟩ run schedule words n,
    e.subject ∈ keys ∧ ∀ key ∈ e.partners, key ∈ keys

end RebuildBound.Spec
