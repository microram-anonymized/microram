import RebuildBound.Spec.NativeMatch.Production

/-! Native production dispatch and faithful adaptive API continuation.
Exact-byte bucket fallbacks select the first physical lane; forwarding retains
its latest earlier record. The shared cascade computes later real/dummy probes.
The actual native selected records generate postrecords and future requests.
Public policy/schedule linkage, compiled execution, cryptographic replacement,
normalization representation and stop obligations remain explicit. -/

namespace RebuildBound.Spec.NativeMatchDispatch
open Model NativeMatch NativeMatch.Lanes NativeMatchTrace

/-- Exact mask extraction selects the first occupied physical lane, matching
`tzcnt`; chronology across pages and forwarding are separate choices. -/
def storedFirst (stored : LogicalKey → Stored) (key : LogicalKey) (records : List Rec) : Option Rec :=
  records.find? (fun r => stored r.key == stored key)

end RebuildBound.Spec.NativeMatchDispatch
namespace RebuildBound.Spec.NativeMatchDispatch
open Model NativeMatch NativeMatch.Lanes NativeMatchTrace

/-- Exact full-stored-key comparison used by scalar ClearFromCurrentUnit and
by MatchMaskFromKeyLines when a dense wave uses its fallback. -/
def storedClear (stored : LogicalKey → Stored) (unit : Model.Bucket) (keys : List LogicalKey) : Model.Bucket :=
  unit.map fun lane => lane.filter fun r => !(keys.any fun key => stored r.key == stored key)

def exactPageMask (stored : LogicalKey → Stored) (page : Page) (key : LogicalKey) : Mask :=
  maskOfBits fun i => page.live i && (stored (page.keys i) == stored key)

/-- The native public saturating dense-work loop. -/
def denseWork (buckets : List Nat) : Nat :=
  buckets.foldl (fun count buckets => count + min buckets ((2 ^ 16 + 1) - count)) 0

/-- Production stored-16-byte branch in ProbeLevelArenaBatchLanes. -/
def batchCross (enabled : Bool) (lanes : Nat) (denseBuckets : List Nat) : Bool :=
  enabled && decide (64 ≤ lanes) && decide (16 ≤ denseWork denseBuckets) &&
    decide (denseWork denseBuckets < 2 ^ 16 + 1)

/-- Bucket-worker variant: amortization uses this shard's bucket count while
the cap still uses the complete plan's saturated dense work. -/
def workerCross (enabled : Bool) (lanes workerBuckets : Nat) (denseBuckets : List Nat) : Bool :=
  enabled && decide (64 ≤ lanes) && decide (16 ≤ workerBuckets) &&
    decide (denseWork denseBuckets < 2 ^ 16 + 1)

def pageMask (cross : Bool) (stored : LogicalKey → Stored) (page : Page) (key : LogicalKey) : Mask :=
  if cross then denseMask stored page key true else exactPageMask stored page key

def pageRecord (cross : Bool) (stored : LogicalKey → Stored) (page : Page) (key : LogicalKey) : Option Rec :=
  if cross then denseRecord stored page key true else storedFirst stored key page.bucket.recs

/-- Scalar and blind upsert paths always use the exact complete-byte clear. -/
def scalarRequesterStep (stored : LogicalKey → Stored) (entries : Nat) (st : Requester.State)
    (record : Rec) (real : Bool) : Requester.State :=
  Requester.insert entries ⟨st.frozen, storedClear stored st.current [record.key]⟩
    (if real then some record else none)

end RebuildBound.Spec.NativeMatchDispatch
namespace RebuildBound.Spec.NativeMatchDispatch
open Model NativeMatch NativeMatch.Lanes NativeMatchTrace

/-- Public dense dispatch descriptors. Scalar reads retain the exact fallback;
tile and worker descriptors use the audited production thresholds. -/
inductive Mode where
  | scalar
  | tile (enabled : Bool) (lanes : Nat) (denseBuckets : List Nat)
  | worker (enabled : Bool) (lanes workerBuckets : Nat) (denseBuckets : List Nat)
  deriving DecidableEq, Repr

def Mode.cross : Mode → Bool
  | .scalar => false
  | .tile enabled lanes buckets => batchCross enabled lanes buckets
  | .worker enabled lanes count buckets => workerCross enabled lanes count buckets

def scanPages (mode : Nat → Mode) (stored : LogicalKey → Stored) (pages : List Page)
    (key : LogicalKey) : Option Rec :=
  pages.zipIdx.foldl (fun found pi => (pageRecord (mode pi.2).cross stored pi.1 key).orElse (fun _ => found)) none

/-- Every key is tested against the original page; the masks are ORed before
one occupancy write, including when the exact byte comparison is selected. -/
def deferredMask (cross : Bool) (stored : LogicalKey → Stored) (p : Page) (keys : List LogicalKey) : Mask :=
  keys.foldl (fun mask key => mask ||| pageMask cross stored p key) 0

def deferredClear (cross : Bool) (stored : LogicalKey → Stored) (p : Page) (keys : List LogicalKey) : Page :=
  (p.1, p.2 &&& ~~~deferredMask cross stored p keys)

def clearUnit (mode : Nat → Mode) (stored : LogicalKey → Stored) (unit : Model.Bucket)
    (keys : List LogicalKey) : Model.Bucket :=
  (((allBucketPages unit).zipIdx.map fun pi => deferredClear (mode pi.2).cross stored pi.1 keys).flatMap
    Page.bucket).take unit.length

/-- Scalar and blind operations always clear exact stored bytes. A batch uses
its page dispatch, then the existing per-lane insertion engine and full stored
key supersession test. -/
def requesterStep (mode : Nat → Mode) (stored : LogicalKey → Stored) (entries : Nat)
    (st : Requester.State) : Requester.Op → Requester.State
  | .access record real => scalarRequesterStep stored entries st record real
  | .batch lanes => lanes.zipIdx.foldl
      (fun state ri => Requester.insert entries state
        (if storedSuperseded stored lanes ri.2 ri.1 then none else some ri.1))
      ⟨st.frozen, clearUnit mode stored st.current (lanes.map Rec.key)⟩

end RebuildBound.Spec.NativeMatchDispatch
namespace RebuildBound.Spec.NativeMatchApi
open Model Model.Hierarchy Model.DirectJob Model.Online Model.OnlineBatch NativeMatch NativeMatch.Lanes NativeMatchTrace
open NativeMatchDispatch NativeMatchHierarchy

/-- Public dispatch identifies an online unit or published tier and its page.
The descriptor itself computes the audited scalar/tile/worker selector. -/
inductive Location where
  | unit (ordinal : Nat)
  | tier (coordinate : Nat × Nat)
  deriving DecidableEq, Repr
abbrev Policy := Nat → Location → Nat → NativeMatchDispatch.Mode

inductive Stop where
  | tableProducer (coordinate : Nat × Nat)
  deriving DecidableEq, Repr

/-- The API engine retains its own native postrecords, selected records,
requester state and observed rows across every public frame. -/
structure State (m : Nat) where
  ops : List OnlineBatch.Op
  requests : List Api.Request
  selected : List Probe.Result
  rows : List (Fin m → Nat)
  requester : Requester.State

def empty {m : Nat} : State m := ⟨[],[],[],[],⟨[],[]⟩⟩

def traceFromState (g : OnlineGeom) (init : List Rec) (unsh : Rec → Bool) (st : Requester.State) : Trace :=
  ⟨fun i => (st.frozen.drop (i*g.unitsPerPrefix)).take g.unitsPerPrefix, init, unsh⟩

def requireTables (lookup : Nat × Nat → Option Output) : List (Nat × Nat) → Except Stop Unit
  | [] => .ok ()
  | c :: cs => match lookup c with
    | none => .error (.tableProducer c)
    | some _ => requireTables lookup cs

/-- Frozen/current units retain their physical page group and chronological
order. The newest hit replaces the preceding accumulator. -/
def scanRequester (policy : Policy) (operation : Nat) (stored : LogicalKey → Stored)
    (st : Requester.State) (consumed : Nat) (key : LogicalKey) : Option Rec :=
  let older := ((st.frozen.drop consumed).zipIdx consumed).foldl
    (fun found ui => (scanPages (policy operation (.unit ui.2)) stored (allBucketPages ui.1) key).orElse
      (fun _ => found)) none
  (scanPages (policy operation (.unit st.frozen.length)) stored (allBucketPages st.current) key).orElse
    (fun _ => older)

def scanOutput (policy : Policy) (operation : Nat) (stored : LogicalKey → Stored)
    (coordinate : Nat × Nat) (out : Output) (key : LogicalKey) (address : Nat) : Option Rec :=
  (storedFirst stored key (out.main.getD address []).recs).orElse fun _ =>
    scanPages (policy operation (.tier coordinate)) stored (allBucketPages out.tier) key

/-- One batch lane queries the actual pre-operation native requester state.
Earlier lanes affect forwarding only; no lane has yet mutated the unit. -/
def query (policy : Policy) (stored : LogicalKey → Stored) (cfg : Config) (sh : Shapes)
    (g : OnlineGeom) (schedule : Schedule) (init : List Rec) (unsh : Rec → Bool)
    (words : Words) (dummy : Nat → Nat → Nat) (operation start lane : Nat)
    (st : Requester.State) (earlier : List Rec) (key : LogicalKey) : Except Stop Probe.Result := do
  let tr := traceFromState g init unsh st
  let lookup := fun c => nativeTable stored cfg sh tr words c.1 c.2
  let cs := (schedule start).tables
  requireTables lookup cs
  let found := (storedLatest stored key earlier).orElse fun _ =>
    scanRequester policy operation stored st (((schedule start).consumed-cfg.seed 1)*g.unitsPerPrefix) key
  pure (Probe.cascadeWith
    (fun c address => scanOutput policy operation stored c ((lookup c).getD emptyOutput) key address)
    (fun c => bucket cfg c.1 c.2 (jobWord cfg words c.1 c.2 key))
    (fun i c => bucket cfg c.1 c.2 (dummy (start+lane) i)) cs found 0)

/-- Native selected records, including tombstones and flags, determine every
postrecord before the next lane forwards or the next frame chooses requests. -/
def chunk (policy : Policy) (stored : LogicalKey → Stored) (codec : Api.Codec)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (schedule : Schedule) (init : List Rec)
    (words : Words) (dummy : Nat → Nat → Nat) (operation start : Nat) (st : Requester.State) :
    List Rec → List Api.Request → Except Stop (List Rec × List Probe.Result)
  | _, [] => .ok ([],[])
  | earlier, q :: qs => do
    let selected ← query policy stored cfg sh g schedule init (fun r => codec.flag r.val)
      words dummy operation start earlier.length st earlier q.key
    let record := Api.postRecord codec q selected.found
    let rest ← chunk policy stored codec cfg sh g schedule init words dummy operation start st
      (earlier ++ [record]) qs
    pure (record :: rest.1, selected :: rest.2)

/-- One chosen public group. The chunk result carries the postrecords computed
from the native selections, before any requester mutation. -/
def operation (policy : Policy) (stored : LogicalKey → Stored) (codec : Api.Codec)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (schedule : Schedule) (init : List Rec)
    (words : Words) (dummy : Nat → Nat → Nat) {m : Nat} (state : State m) :
    PublicApi.Group Api.Request → Except Stop (OnlineBatch.Op × List Probe.Result)
  | .blind q => .ok (.blind (Api.postRecord codec q none), [⟨none,[]⟩])
  | .chunk qs => do
      let result ← chunk policy stored codec cfg sh g schedule init words dummy state.ops.length
        state.rows.length state.requester [] qs
      pure (.batch result.1, result.2)

/-- Reuse the requester insert engine after the complete batch lookup wave.
Blind operations follow the source's scalar exact-byte removal path. -/
def issueFrame (policy : Policy) (stored : LogicalKey → Stored) (codec : Api.Codec)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (schedule : Schedule) (init : List Rec)
    (words : Words) (dummy : Nat → Nat → Nat) {m : Nat} (choose : ApiAdaptive.Chooser m)
    (state : State m) (frame : ApiAdaptive.Frame) : Except Stop (State m) := do
  let group := ApiAdaptive.requests choose state.rows frame
  let result ← operation policy stored codec cfg sh g schedule init words dummy state group
  let requester := requesterStep (policy state.ops.length (.unit state.requester.frozen.length))
    stored g.unitEntries state.requester result.1.requester
  pure ⟨state.ops ++ [result.1], state.requests ++ group.lanes, state.selected ++ result.2,
    state.rows ++ result.2.map (fun result i => result.addresses.getD i.val 0), requester⟩

def execute (policy : Policy) (stored : LogicalKey → Stored) (codec : Api.Codec)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (schedule : Schedule) (init : List Rec)
    (words : Words) (dummy : Nat → Nat → Nat) {m : Nat} (choose : ApiAdaptive.Chooser m) :
    State m → List ApiAdaptive.Frame → Except Stop (State m)
  | state, [] => .ok state
  | state, frame :: rest => do
      let next ← issueFrame policy stored codec cfg sh g schedule init words dummy choose state frame
      execute policy stored codec cfg sh g schedule init words dummy choose next rest

def run (policy : Policy) (stored : LogicalKey → Stored) (codec : Api.Codec)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (schedule : Schedule) (init : List Rec)
    (words : Words) (dummy : Nat → Nat → Nat) {m : Nat} (choose : ApiAdaptive.Chooser m)
    (frames : List ApiAdaptive.Frame) : Except Stop (State m) :=
  execute policy stored codec cfg sh g schedule init words dummy choose empty frames

end RebuildBound.Spec.NativeMatchApi
namespace RebuildBound.Spec.NativeMatchApi
open Model Model.Hierarchy Model.Online

/-- Reference cut at an operation boundary. This is an observation of the
existing exact run; it is never used to compute a native postrecord. -/
def referenceState (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineBatch.BatchRun)
    (S : Schedule) (words : Words) (dummy : Nat → Nat → Nat) (requests : List Api.Request)
    (j m : Nat) : State m :=
  let count := ((OnlineBatch.widths run).take j).sum
  let selected := (List.range count).map (Probe.batch cfg sh g run S words dummy)
  ⟨run.ops.take j, requests.take count, selected,
    selected.map (fun result i => result.addresses.getD i.val 0), OnlineBatch.stateAt g run j⟩

end RebuildBound.Spec.NativeMatchApi
namespace RebuildBound.Spec.NativeMatchApi
open Model Model.Hierarchy Model.Online NativeMatch NativeMatch.Lanes NativeMatchProduction
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def production (ctx : Context member initialized h) (policy : Policy)
    (stored : LogicalKey→Stored) (tape : IdealKey.Tape) : Except Stop (State ctx.transcriptWidth) :=
  run policy stored ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ctx.compiled ctx.frames

/-- Full exact API observation, with its actual adaptive request sequence and
physical requester state. The native engine does not consult this result. -/
def reference (ctx : Context member initialized h) (tape : IdealKey.Tape) : State ctx.transcriptWidth :=
  let run := ctx.run tape
  let rows := (Adaptive.interact ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)).2
  let requests := (ApiAdaptive.requestGroups ctx.compiled rows ctx.frames).flatMap PublicApi.Group.lanes
  ⟨run.ops,requests,(List.range ctx.accesses).map (Probe.batch ctx.geo.cfg ctx.geo.shapes ctx.unit run
    ctx.schedule (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)),rows,
    OnlineBatch.stateAt ctx.unit run run.ops.length⟩
end RebuildBound.Spec.NativeMatchApi
namespace RebuildBound.Spec.NativeMatchApi
open Model NativeMatch NativeMatch.Lanes NativeMatchProduction NativeRoutingActual
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def normalizationBad (ctx : Context member initialized h) (stored : LogicalKey→Stored)
    (tape : IdealKey.Tape) : Prop :=
  NativeNormalize.collision ((usedKeys (ctx.run tape)).map fun key=>(key,stored key))

def mismatch (ctx : Context member initialized h) (policy : Policy) (stored : LogicalKey→Stored)
    (tape : IdealKey.Tape) : Prop := production ctx policy stored tape≠.ok (reference ctx tape)
end RebuildBound.Spec.NativeMatchApi
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchDispatch NativeMatchApi NativeMatchProduction NativeRoutingActual

/-- Exact-byte fallbacks retain the source's first physical lane selector. -/
def NativeMatchApiFallback_statement : Prop :=
  ∀ (stored : LogicalKey→Stored) key records, (records.map Rec.key).Nodup →
    ¬listNormalizeBad stored records key → storedFirst stored key records=DirectPrefix.latest key records

def NativeMatchApiDispatch_statement : Prop :=
  ∀ (mode : Mode) (stored : LogicalKey→Stored) (page : Page) key,
    (page.bucket.recs.map Rec.key).Nodup → ¬denseNormalizeBad stored page key →
    (mode.cross=true → ∀ e∈denseEvents page key true, ¬e.bad stored) →
    pageRecord mode.cross stored page key=DirectPrefix.latest key page.bucket.recs ∧
      ∀ slot : Fin 64, (pageMask mode.cross stored page key).getLsbD slot.val=true ↔
        page.live slot=true ∧ page.keys slot=key

/-- Batch removals reuse their query-wave events. Scalar and blind clears
use exact stored bytes, and the used-key collision event covers both paths. -/
def NativeMatchApiRemoval_statement : Prop :=
  ∀ (mode : Nat→Mode) (stored : LogicalKey→Stored) (cfg : Config) (sh : Shapes)
    (g : OnlineGeom) (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words)
    j op, run.ops[j]?=some op →
    ¬NativeNormalize.collision ((usedKeys run).map fun key=>(key,stored key)) →
    (∀ e∈batchPrefixEvents cfg sh g run S words (OnlineBatch.slots run).length, ¬e.bad stored) →
    requesterStep mode stored g.unitEntries (OnlineBatch.stateAt g run j) op.requester=
      Requester.step g.unitEntries (OnlineBatch.stateAt g run j) op.requester

/-- Native selected records drive postrecords and all later adaptive requests.
All exact-reference structural and uniqueness properties are derived from the
legal API context; no execution-agreement premise is supplied. -/
def NativeMatchApiProjection_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member∈ConfigurationFamily.members → ctx.Valid →
    ∀ (policy : Policy) (stored : LogicalKey→Stored) tape,
    ¬ctx.capacityBad tape → NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses=true →
    ¬normalizationBad ctx stored tape → (∀ e∈ctx.inventory tape, ¬e.bad stored) →
    production ctx policy stored tape=.ok (reference ctx tape)

def NativeMatchApiDivergence_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member∈ConfigurationFamily.members → ctx.Valid →
    ∀ (policy : Policy) (stored : LogicalKey→Stored) tape, mismatch ctx policy stored tape →
    ctx.capacityBad tape ∨ NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit
      ctx.snapshots ctx.client ctx.accesses tape ∨ normalizationBad ctx stored tape ∨
      ∃ e∈ctx.inventory tape, e.bad stored
end RebuildBound.Spec
