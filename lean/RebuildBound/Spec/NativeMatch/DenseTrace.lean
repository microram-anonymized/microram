import RebuildBound.Spec.NativeMatch.Trace
import RebuildBound.Spec.NativeMatch.Dense
import RebuildBound.Spec.Model.Probe
import RebuildBound.Spec.HierarchyStructural

namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

def Page.live (p : Page) : NativeMatchDense.Live := fun i => p.2.getLsbD i.val
def Page.keys (p : Page) : (Fin 64) → LogicalKey := logicalKeys p.1

def exactIndex (p : Page) (key : LogicalKey) : Option (Fin 64) :=
  (List.finRange 64).find? fun i => p.live i && (p.keys i == key)

/-- Logical partner decoding of the concrete row/column selector. -/
def densePartners {K : Type} (keys : Fin 64 → K) (live : NativeMatchDense.Live)
    (column : Bool) (subset : Fin 8) : List K :=
  ((List.finRange 8).filter fun j => live (NativeMatchDense.subsetSlot column subset j)).map
    fun j => keys (NativeMatchDense.subsetSlot column subset j)

def denseEvent (p : Page) (key : LogicalKey) (column : Bool) (s : Fin 8) : Event :=
  ⟨if column then .denseColumn else .denseRow, key,
    densePartners p.keys p.live column s, .dense64⟩

/-- Only the fourteen other subsets of a key-holding reference page are charged.
The index and lists are computed from logical records before any mask clear. -/
def denseEvents (p : Page) (key : LogicalKey) (active : Bool) : List Event :=
  if active then
    match exactIndex p key with
    | none => []
    | some present =>
      ([false, true] : List Bool).flatMap fun column =>
        ((List.finRange 8).filter fun s =>
          s != (if column then NativeMatchDense.colOf present else NativeMatchDense.rowOf present)).map
          (denseEvent p key column)
  else []

/-- A finite, local normalization-collision event; later composition embeds it
in the unconditional chronological normalization experiment. -/
def denseNormalizeBad (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey) : Prop :=
  ∃ i : (Fin 64), p.live i = true ∧ p.keys i ≠ key ∧ stored (p.keys i) = stored key

def denseHit (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey) (active : Bool) : Bool :=
  NativeMatchDense.hit (stored ∘ p.keys) p.live (stored key) active

def denseSelected (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey) : (Fin 64) :=
  NativeMatchDense.selected (stored ∘ p.keys) p.live (stored key)

/-- The native verified slot becomes a one-bit match word; gating precedes both
selection and deferred removal, exactly as in the dense wave. -/
def denseMask (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey) (active : Bool) : Mask :=
  if denseHit stored p key active then (1 : Mask) <<< (denseSelected stored p key).val else 0

def denseRecord (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey) (active : Bool) : Option Rec :=
  if denseHit stored p key active then some (p.1 (denseSelected stored p key).val) else none

def denseClear (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey) (active : Bool) : Page :=
  (p.1, p.2 &&& ~~~denseMask stored p key active)


/-- Physical contiguous pages; the last short page is zero-occupancy padded. -/
def bucketPages : Nat → Model.Bucket → List Page
  | 0, _ => []
  | n + 1, b => Page.ofBucket b :: bucketPages n (b.drop 64)

def allBucketPages (b : Model.Bucket) : List Page := bucketPages ((b.length + 63) / 64) b

def denseScan (stored : LogicalKey → Stored) (pages : List Page) (key : LogicalKey) : Option Rec :=
  pages.foldl (fun found p => (denseRecord stored p key true).orElse (fun _ => found)) none

def denseScanEvents (pages : List Page) (key : LogicalKey) : List Event :=
  pages.flatMap fun p => denseEvents p key true

def denseScanNormalizeBad (stored : LogicalKey → Stored) (pages : List Page) (key : LogicalKey) : Prop :=
  ∃ p ∈ pages, denseNormalizeBad stored p key

/-- Exact fallback compares complete stored bytes. -/
def storedLatest (stored : LogicalKey → Stored) (key : LogicalKey) (records : List Rec) : Option Rec :=
  records.reverse.find? (fun r => stored r.key == stored key)

def listNormalizeBad (stored : LogicalKey → Stored) (records : List Rec) (key : LogicalKey) : Prop :=
  ∃ r ∈ records, r.key ≠ key ∧ stored r.key = stored key

def scanNormalizeBad (stored : LogicalKey → Stored) (table : Output) (key : LogicalKey) : Prop :=
  denseScanNormalizeBad stored (allBucketPages table.tier) key ∨
    listNormalizeBad stored table.records key

/-- Hashed main probing remains the existing exact scan. Dense tiers use the
verified native finite operation; a main hit precedes a tier hit in production. -/
def nativeScan (stored : LogicalKey → Stored) (key : LogicalKey) (table : Output) (address : Nat) : Option Rec :=
  (storedLatest stored key ((table.main.getD address []).recs)).orElse fun _ =>
    denseScan stored (allBucketPages table.tier) key

end RebuildBound.Spec.NativeMatchTrace



namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

structure ProbeFrame where
  coordinate : Nat × Nat
  foundBefore : Option Rec
  address : Nat
  events : List Event
  deriving DecidableEq, Repr

/-- The existing exact cascade determines the state at every pre-comparison
cut. No stored-key map is an input to this inventory or to its chosen addresses. -/
def cascadeTrace (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (real : Nat × Nat → Nat) (dummy : Nat → Nat × Nat → Nat)
    (cs : List (Nat × Nat)) (initial : Option Rec) (offset : Nat) : List ProbeFrame :=
  cs.zipIdx.map fun ci =>
    let before := (Probe.cascade key tableAt real dummy (cs.take ci.2) initial offset).found
    ⟨ci.1, before, if before.isSome then dummy (offset + ci.2) ci.1 else real ci.1,
      denseScanEvents (allBucketPages (tableAt ci.1).tier) key⟩

def cascadeEvents (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (cs : List (Nat × Nat)) : List Event :=
  cs.flatMap fun c => denseScanEvents (allBucketPages (tableAt c).tier) key

def cascadeNormalizeBad (stored : LogicalKey → Stored) (key : LogicalKey)
    (tableAt : Nat × Nat → Output) (cs : List (Nat × Nat)) : Prop :=
  ∃ c ∈ cs, scanNormalizeBad stored (tableAt c) key

def nativeCascade (stored : LogicalKey → Stored) (key : LogicalKey)
    (tableAt : Nat × Nat → Output) (real : Nat × Nat → Nat)
    (dummy : Nat → Nat × Nat → Nat) (cs : List (Nat × Nat))
    (initial : Option Rec) (offset : Nat) : Probe.Result :=
  Probe.cascadeWith (fun c a => nativeScan stored key (tableAt c) a) real dummy cs initial offset

end RebuildBound.Spec.NativeMatchTrace

namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

/-- Every key is matched against the same unmodified pre-batch page. The native
wave ORs these words and performs one occupancy write after all lookups. -/
def denseDeferredMask (stored : LogicalKey → Stored) (p : Page) (keys : List LogicalKey) : Mask :=
  keys.foldl (fun mask key => mask ||| denseMask stored p key true) 0

def denseDeferredClear (stored : LogicalKey → Stored) (p : Page) (keys : List LogicalKey) : Page :=
  (p.1, p.2 &&& ~~~denseDeferredMask stored p keys)

def denseBatchEvents (p : Page) (keys : List LogicalKey) : List Event :=
  keys.flatMap fun key => denseEvents p key true

end RebuildBound.Spec.NativeMatchTrace

namespace RebuildBound.Spec.NativeMatchTrace
open Model Model.Hierarchy Model.Online NativeMatch NativeMatch.Lanes

/-- Every physical dense page at the exact operation-start requester state.
Frozen units retain their page boundary and chronological order. -/
def requesterPages (st : Requester.State) (consumedUnits : Nat) : List Page :=
  (st.frozen.drop consumedUnits).flatMap allBucketPages ++ allBucketPages st.current

def batchPages (cfg : Config) (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun)
    (S : Online.Schedule) (t : Nat) : List Page :=
  match (OnlineBatch.slots run)[t]? with
  | none => []
  | some s => requesterPages (OnlineBatch.stateAt g run s.op)
      (((OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).consumed - cfg.seed 1) *
        g.unitsPerPrefix)

def batchEvents (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Online.Schedule) (words : Words) (t : Nat) : List Event :=
  match (OnlineBatch.slots run)[t]? with
  | none => []
  | some s => if s.probes then
      denseScanEvents (batchPages cfg g run S t) s.record.key ++
        cascadeEvents s.record.key (fun c => table cfg sh (OnlineBatch.traceOf g run) words c.1 c.2)
          (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables
    else []

def batchNormalizeBad (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun) (S : Online.Schedule)
    (words : Words) (t : Nat) : Prop :=
  match (OnlineBatch.slots run)[t]? with
  | none => False
  | some s => s.probes = true ∧
      (listNormalizeBad stored (Probe.earlier run s) s.record.key ∨
       denseScanNormalizeBad stored (batchPages cfg g run S t) s.record.key ∨
       cascadeNormalizeBad stored s.record.key
         (fun c => table cfg sh (OnlineBatch.traceOf g run) words c.1 c.2)
         (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables)

/-- The concrete dense implementation is plugged into the existing cascade.
Earlier batch lanes supply exactly the existing forwarding result. -/
def nativeBatch (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun) (S : Online.Schedule)
    (words : Words) (dummy : Nat → Nat → Nat) (t : Nat) : Probe.Result :=
  match (OnlineBatch.slots run)[t]? with
  | none => ⟨none, []⟩
  | some s => if s.probes then
      nativeCascade stored s.record.key
        (fun c => table cfg sh (OnlineBatch.traceOf g run) words c.1 c.2)
        (fun c => bucket cfg c.1 c.2 (jobWord cfg words c.1 c.2 s.record.key))
        (fun i c => bucket cfg c.1 c.2 (dummy t i))
        (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables
        ((storedLatest stored s.record.key (Probe.earlier run s)).orElse (fun _ =>
          denseScan stored (batchPages cfg g run S t) s.record.key)) 0
    else ⟨none, []⟩

/-- A finite chronological inventory, independent of the stored-key map. -/
def batchPrefixEvents (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Online.Schedule) (words : Words) (n : Nat) : List Event :=
  (List.range n).flatMap (batchEvents cfg sh g run S words)

end RebuildBound.Spec.NativeMatchTrace

namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

/-- Apply the deferred native mask once per physical page, then decode exactly
the allocated unit prefix. Padding lanes are never inserted into requester state. -/
def denseClearUnit (stored : LogicalKey → Stored) (unit : Model.Bucket)
    (keys : List LogicalKey) : Model.Bucket :=
  (((allBucketPages unit).map (fun p => denseDeferredClear stored p keys)).flatMap Page.bucket).take unit.length

def unitBatchEvents (unit : Model.Bucket) (keys : List LogicalKey) : List Event :=
  (allBucketPages unit).flatMap fun p => denseBatchEvents p keys

def unitNormalizeBad (stored : LogicalKey → Stored) (unit : Model.Bucket)
    (keys : List LogicalKey) : Prop :=
  ∃ p ∈ allBucketPages unit, ∃ key ∈ keys, denseNormalizeBad stored p key

end RebuildBound.Spec.NativeMatchTrace

namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeMatch.Lanes

def requesterKeys : Requester.Op → List LogicalKey
  | .access r _ => [r.key]
  | .batch lanes => lanes.map Rec.key

/-- Exact complete-stored-key batch duplicate test, including later lanes. -/
def storedSuperseded (stored : LogicalKey → Stored) (lanes : List Rec) (i : Nat) (r : Rec) : Bool :=
  (lanes.drop (i + 1)).any (fun s => stored s.key == stored r.key)

def nativeRequesterStep (stored : LogicalKey → Stored) (entries : Nat) (st : Requester.State) :
    Requester.Op → Requester.State
  | .access r real =>
    Requester.insert entries ⟨st.frozen, denseClearUnit stored st.current [r.key]⟩
      (if real then some r else none)
  | .batch lanes =>
    lanes.zipIdx.foldl
      (fun s ri => Requester.insert entries s
        (if storedSuperseded stored lanes ri.2 ri.1 then none else some ri.1))
      ⟨st.frozen, denseClearUnit stored st.current (lanes.map Rec.key)⟩

def requesterEvents (st : Requester.State) (op : Requester.Op) : List Event :=
  unitBatchEvents st.current (requesterKeys op)

def requesterNormalizeBad (stored : LogicalKey → Stored) (st : Requester.State) (op : Requester.Op) : Prop :=
  unitNormalizeBad stored st.current (requesterKeys op) ∨
    match op with
    | .access _ _ => False
    | .batch lanes => ∃ r ∈ lanes, listNormalizeBad stored lanes r.key

def requesterTrace (entries : Nat) (st : Requester.State) (ops : List Requester.Op) : List Event :=
  eventsOf (Requester.step entries) requesterEvents st ops

def requesterNormalizeOf (stored : LogicalKey → Stored) (entries : Nat) :
    Requester.State → List Requester.Op → Prop
  | _, [] => False
  | st, op :: rest => requesterNormalizeBad stored st op ∨
      requesterNormalizeOf stored entries (Requester.step entries st op) rest

end RebuildBound.Spec.NativeMatchTrace

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online NativeMatch NativeMatch.Lanes NativeMatchTrace

def NativeMatchDenseRecord_statement : Prop :=
  ∀ (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey)
    (hu : (p.bucket.recs.map Rec.key).Nodup)
    (hn : ¬ denseNormalizeBad stored p key)
    (hoff : ∀ e ∈ denseEvents p key true, ¬ e.bad stored),
denseRecord stored p key true = DirectPrefix.latest key p.bucket.recs

def NativeMatchDenseRemoval_statement : Prop :=
  ∀ (stored : LogicalKey → Stored) (p : Page) (key : LogicalKey)
    (hu : (p.bucket.recs.map Rec.key).Nodup)
    (hn : ¬ denseNormalizeBad stored p key)
    (hoff : ∀ e ∈ denseEvents p key true, ¬ e.bad stored),
(denseClear stored p key true).bucket = Requester.clearKey key p.bucket

def NativeMatchDenseDeferredRemoval_statement : Prop :=
  ∀ (stored : LogicalKey → Stored) (p : Page) (keys : List LogicalKey)
    (hu : (p.bucket.recs.map Rec.key).Nodup)
    (hn : ∀ key ∈ keys, ¬ denseNormalizeBad stored p key)
    (hoff : ∀ e ∈ denseBatchEvents p keys, ¬ e.bad stored),
(denseDeferredClear stored p keys).bucket =
      keys.foldl (fun unit key => Requester.clearKey key unit) p.bucket

def NativeMatchCascadeProjection_statement : Prop :=
  ∀ (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (real : Nat × Nat → Nat) (dummy : Nat → Nat × Nat → Nat)
    (cs : List (Nat × Nat)) (initial : Option Rec) (offset : Nat),
Probe.cascadeWith (fun c a => Probe.scan key (tableAt c) a) real dummy cs initial offset =
      Probe.cascade key tableAt real dummy cs initial offset

def NativeMatchBatchAgreement_statement : Prop :=
  ∀ (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun)
    (hT : TraceStructural geo.cfg (OnlineBatch.traceOf g run))
    (hInit : run.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hUnsh : UnshPromise geo.cfg geo.shapes (OnlineBatch.traceOf g run))
    (S : Online.Schedule) (words : Words) (stored : LogicalKey → Stored)
    (dummy : Nat → Nat → Nat) (t : Nat)
    (hc : ∀ c ∈ (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables,
      1 ≤ c.1 ∧ c.1 ≤ geo.cfg.levels ∧ c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1)
    (hn : ¬ batchNormalizeBad stored geo.cfg geo.shapes g run S words t)
    (hoff : ∀ e ∈ batchEvents geo.cfg geo.shapes g run S words t, ¬ e.bad stored),
nativeBatch stored geo.cfg geo.shapes g run S words dummy t =
      Probe.batch geo.cfg geo.shapes g run S words dummy t

def NativeMatchBatchDivergence_statement : Prop :=
  ∀ (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun)
    (hT : TraceStructural geo.cfg (OnlineBatch.traceOf g run))
    (hInit : run.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hUnsh : UnshPromise geo.cfg geo.shapes (OnlineBatch.traceOf g run))
    (S : Online.Schedule) (words : Words) (stored : LogicalKey → Stored)
    (dummy : Nat → Nat → Nat) (n : Nat)
    (hc : ∀ t < n, ∀ c ∈ (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables,
      1 ≤ c.1 ∧ c.1 ≤ geo.cfg.levels ∧ c.2 ≤ geo.cfg.seed c.1 + geo.cfg.ordinals c.1)
    (hd : ∃ t < n, nativeBatch stored geo.cfg geo.shapes g run S words dummy t ≠
      Probe.batch geo.cfg geo.shapes g run S words dummy t),
(∃ t < n, batchNormalizeBad stored geo.cfg geo.shapes g run S words t) ∨
      ∃ e ∈ batchPrefixEvents geo.cfg geo.shapes g run S words n, e.bad stored

def NativeMatchDenseUnitCount_statement : Prop :=
  ∀ (pages : List Page) (key : LogicalKey)
    (hu : ((pageRecords pages).map Rec.key).Nodup),
(denseScanEvents pages key).length ≤ 14

def NativeMatchRequesterCount_statement : Prop :=
  ∀ (st : Requester.State) (n : Nat)
    (hu : Requester.Unique st) (key : LogicalKey),
(denseScanEvents (requesterPages st n) key).length ≤
      ((st.frozen.drop n).length + 1) * 14

def NativeMatchRequesterPages_statement : Prop :=
  ∀ (st : Requester.State) (n : Nat),
(requesterPages st n).length =
      ((st.frozen.drop n).map (fun b => (b.length + 63) / 64)).sum +
        (st.current.length + 63) / 64

def NativeMatchDenseUnitRemoval_statement : Prop :=
  ∀ (stored : LogicalKey → Stored) (unit : Model.Bucket)
    (keys : List LogicalKey) (hu : (unit.recs.map Rec.key).Nodup)
    (hn : ¬ unitNormalizeBad stored unit keys)
    (hoff : ∀ e ∈ unitBatchEvents unit keys, ¬ e.bad stored),
denseClearUnit stored unit keys = keys.foldl (fun unit key => Requester.clearKey key unit) unit

def NativeMatchRequesterAgreement_statement : Prop :=
  ∀ (stored : LogicalKey → Stored) (entries : Nat) (ops : List Requester.Op)
    (hn : ¬ requesterNormalizeOf stored entries ⟨[], []⟩ ops)
    (hoff : ∀ e ∈ requesterTrace entries ⟨[], []⟩ ops, ¬ e.bad stored),
ops.foldl (nativeRequesterStep stored entries) ⟨[], []⟩ = Requester.run entries ⟨[], []⟩ ops

def NativeMatchRequesterDivergence_statement : Prop :=
  ∀ (stored : LogicalKey → Stored) (entries : Nat)
    (st : Requester.State) (ops : List Requester.Op) (hu : Requester.Unique st)
    (hd : ops.foldl (nativeRequesterStep stored entries) st ≠ Requester.run entries st ops),
requesterNormalizeOf stored entries st ops ∨ ∃ e ∈ requesterTrace entries st ops, e.bad stored

def NativeMatchDenseEventPartners_statement : Prop :=
  ∀ (p : Page) (key : LogicalKey) (e : Event)
    (he : e ∈ denseEvents p key true),
e.partners.length ≤ 8 ∧ e.rule = .dense64

end RebuildBound.Spec
