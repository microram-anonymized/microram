import RebuildBound.Spec.NativeMatch.HierarchyCounts
import RebuildBound.Spec.NativeMatch.Allocation
import RebuildBound.Spec.NativeRouting.Actual
import RebuildBound.Spec.ApiLegal

/-! The production experiment contains only public geometry, a legal logical-key
client, and a public publication schedule. Capacity and ring-plan stops guard
charges on the unconditional experiment; they do not condition its law.
Cryptographic replacement, finite normalization, other stops, and compiled
execution remain separate obligations. -/
namespace RebuildBound.Spec.NativeMatchPhysical
open Model
structure Snapshot (slots : Nat) where
  deltas : List (Publication slots)
  consumed : Nat

def physicalSchedule (cfg : Config) {slots : Nat} (snapshots : Nat → Snapshot slots) : Online.Schedule :=
  fun t => ⟨cfg.seed 1 + (snapshots t).consumed, hashedEntries (publications (snapshots t).deltas)⟩

def snapshotAt {slots : Nat} (run : OnlineBatch.BatchRun) (snapshots : Nat → Snapshot slots) (t : Nat) :=
  snapshots (OnlineBatch.chunkStart (OnlineBatch.widths run) t)
end RebuildBound.Spec.NativeMatchPhysical

namespace RebuildBound.Spec.NativeMatchPhysical
open Model
/-- Successful FillDensePrefix for every potential probing slot. This observes
its production ring-gap check, not a count supplied by the caller. -/
def ready {slots : Nat} (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun)
    (snapshots : Nat → Snapshot slots) (n : Nat) : Bool :=
  (List.range n).all fun t =>
    match (OnlineBatch.slots run)[t]? with
    | none => true
    | some slot => if slot.probes then
        (fillDenseUnits g.unitsPerPrefix 2 (snapshotAt run snapshots t).consumed
          (OnlineBatch.stateAt g run slot.op).frozen.length).isSome
      else true
end RebuildBound.Spec.NativeMatchPhysical


namespace RebuildBound.Spec.NativeMatchHierarchy
open Model Model.Hierarchy NativeMatchTrace NativeMatchPhysical IdealKey

/-- A reference ring-plan stop uses the same public FillDensePrefix guard as
production. It is charged on the unconditional experiment, separately from
matching and capacity. -/
def ringStopped (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom) {slots : Nat}
    (snapshots : Nat → Snapshot slots) {m : Nat} (client : Adaptive.AdaptiveRun m) (n : Nat)
    (tape : Tape) : Prop :=
  ready g (Adaptive.realized cfg sh g (physicalSchedule cfg snapshots) client
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)) snapshots n = false

noncomputable def physicalChargedEvents (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    {slots : Nat} (snapshots : Nat → Snapshot slots) {m : Nat} (client : Adaptive.AdaptiveRun m)
    (n : Nat) (tape : Tape) : List Event := by
  classical
  let run := Adaptive.realized cfg sh g (physicalSchedule cfg snapshots) client
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
  exact if Fails cfg sh (OnlineBatch.traceOf g run) (IdealHierarchy.words tape) ∨
      ready g run snapshots n = false then []
    else referenceEvents cfg sh g run (physicalSchedule cfg snapshots) (IdealHierarchy.words tape) n
end RebuildBound.Spec.NativeMatchHierarchy


namespace RebuildBound.Spec.NativeMatchTrace
open Model NativeMatch NativeNormalize

/-- The two production segment geometries are charged separately. This is a
projection of the pre-state event writer, with no stored-key input. -/
def comparisons (rule : Rule) (events : List Event) : List (Comparison LogicalKey) :=
  (events.filter fun e => e.rule == rule).map Event.comparison

def mapComparisons {A B : Type} (f : A → B) (cmps : List (Comparison A)) :
    List (Comparison B) := cmps.map fun c => (f c.1, c.2.map f)

def block16 (key : LogicalKey) : Fingerprint 128 :=
  (segments 16 8).symm (NativeKey.keyBlock key)

end RebuildBound.Spec.NativeMatchTrace


namespace RebuildBound.Spec.NativeMatchRouting16
open Model NativeMatch NativeNormalize

def block (key : LogicalKey) : Fingerprint 128 := (segments 16 8).symm (NativeKey.keyBlock key)
abbrev Coord := (IdealKey.Family × Fingerprint 128) ⊕ IdealKey.Coord
abbrev Tape := Coord → Fingerprint 64
noncomputable def law : MeasureTheory.Measure Tape :=
  MeasureTheory.Measure.infinitePi fun _ => wordLaw 64

def index : IdealKey.Coord → Coord
  | .inl (family,key) => if key.length = 16 then .inl (family,block key) else .inr (.inl (family,key))
  | .inr dummy => .inr (.inr dummy)

def canonical (tape : Tape) : IdealKey.Tape := fun c => tape (index c)

def permute (σ : Equiv.Perm (Fingerprint 128)) : Coord → Coord
  | .inl (family,key) => .inl (family,σ key)
  | .inr c => .inr c

def native (σ : Equiv.Perm (Fingerprint 128)) (tape : Tape) : IdealKey.Tape :=
  fun c => tape (permute σ (index c))
end RebuildBound.Spec.NativeMatchRouting16


namespace RebuildBound.Spec.NativeMatchProduction
open Model Model.Hierarchy Model.Online NativeMatchPhysical

/-- Public schedule and legal API client for the production 64-slot units.
The context contains no stored-key values or matching-error assumptions. -/
structure Context (member : ConfigurationFamily.Member) (initialized : Bool) (windows : Nat) where
  codec : Api.Codec
  init : List Rec
  transcriptWidth : Nat
  batchWidth : Nat
  batches : List ApiAdaptive.Batch
  snapshots : Nat → Snapshot (allocatedSlots (member.config initialized).levels
    (member.config initialized).fanout).length
  choose : ApiLegal.Chooser ((member.geometry initialized).chunk windows).cfg
    (ApiAdaptive.shape (ApiAdaptive.frames batchWidth 64 batches))
    (physicalSchedule (member.config initialized) snapshots) transcriptWidth

namespace Context
variable {member : ConfigurationFamily.Member} {initialized : Bool} {windows : Nat}

def geo (_ctx : Context member initialized windows) := (member.geometry initialized).chunk windows
def unit (_ctx : Context member initialized windows) : OnlineGeom := ⟨64,member.r0⟩
def schedule (ctx : Context member initialized windows) := physicalSchedule (member.config initialized) ctx.snapshots
def frames (ctx : Context member initialized windows) := ApiAdaptive.frames ctx.batchWidth 64 ctx.batches
def accesses (ctx : Context member initialized windows) := Adaptive.slotCount (ApiAdaptive.shape ctx.frames)
def compiled (ctx : Context member initialized windows) :=
  ApiLegal.adapt ctx.geo.cfg (ApiAdaptive.shape ctx.frames) ctx.schedule ctx.choose
def client (ctx : Context member initialized windows) : Adaptive.AdaptiveRun ctx.transcriptWidth :=
  ApiAdaptive.run ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init ctx.frames ctx.compiled

def run (ctx : Context member initialized windows) (tape : IdealKey.Tape) :=
  Adaptive.realized ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)

def Valid (ctx : Context member initialized windows) : Prop :=
  ApiCapacity.InitialStateValid ctx.geo.keyCapacity ctx.geo.cfg.initialized ctx.init ∧
  ctx.accesses ≤ ctx.geo.cfg.horizon ∧
  SchedulePremises ctx.geo.cfg ctx.schedule ctx.accesses ctx.transcriptWidth ∧
  ∀ t : ApiLegal.Prefix ctx.geo.cfg (ApiAdaptive.shape ctx.frames) ctx.schedule ctx.transcriptWidth ctx.accesses,
    ApiCapacity.LiveCapacity ctx.geo.keyCapacity (Api.stateOf ctx.codec ctx.init) (ctx.init.map Rec.key)
      ((ApiAdaptive.requestGroups ctx.compiled (Adaptive.rowsOf (ApiLegal.erase t) ctx.accesses) ctx.frames).flatMap
        PublicApi.Group.lanes)
end Context
end RebuildBound.Spec.NativeMatchProduction

namespace RebuildBound.Spec.NativeMatchProduction.Context
open Model Model.Hierarchy NativeMatchTrace NativeMatchHierarchy NativeMatchPhysical
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
noncomputable def inventory (ctx : Context member initialized h) : IdealKey.Tape → List Event :=
  physicalChargedEvents ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.snapshots ctx.client ctx.accesses

def capacityBad (ctx : Context member initialized h) (tape : IdealKey.Tape) : Prop :=
  Fails ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape)) (IdealHierarchy.words tape)
end RebuildBound.Spec.NativeMatchProduction.Context

namespace RebuildBound.Spec
open Model Model.Hierarchy NativeMatch NativeMatchTrace NativeNormalize NativeMatchPhysical NativeMatchProduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal

def NativeMatchProductionDense_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool), member ∈ ConfigurationFamily.members →
    ∀ h (ctx : Context member initialized h), ctx.Valid → ∀ tape,
    ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true →
    weight 2 ((batchPrefixEvents ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape)
      ctx.schedule (IdealHierarchy.words tape) ctx.accesses).map Event.comparison) ≤
        h*(2^32*NativeMatchInventory.denseBuckets member*14*8^2)

def NativeMatchProductionFiniteRead_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h (ctx : Context member initialized h),
    IdealKey.FiniteRead ctx.inventory

def NativeMatchProductionWeights_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool), member ∈ ConfigurationFamily.members →
    ∀ h, 1 ≤ h → ∀ ctx : Context member initialized h, ctx.Valid → ∀ tape,
    weight 4 (comparisons .rebuild32 (ctx.inventory tape)) ≤ h*(64^4*NativeMatchInventory.sMin member initialized) ∧
    weight 2 (comparisons .dense64 (ctx.inventory tape)) ≤ h*(2^32*NativeMatchInventory.denseBuckets member*14*8^2)

/-- Independence is a derived property of the actual reference event writer
on the unconditional product law, including adaptive client decisions. -/
def NativeMatchProductionIndependence_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h (ctx : Context member initialized h)
    (Stored : Type) [MeasurableSpace Stored] (law : Measure Stored) [IsProbabilityMeasure law] rule,
    letI : MeasurableSpace (List (Comparison LogicalKey)) := ⊤
    IndepFun
      (fun p : IdealKey.Tape × Stored => comparisons rule (ctx.inventory p.1)) Prod.snd
      (IdealKey.tapeLaw.prod law)

def NativeMatchProductionRandomFunction_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool), member ∈ ConfigurationFamily.members →
    ∀ h, 1 ≤ h → ∀ ctx : Context member initialized h, ctx.Valid →
    (IdealKey.tapeLaw.prod (tapeLaw 128)) {p | ∃ e ∈ ctx.inventory p.1, e.bad p.2} ≤
      (h:ℝ≥0∞)*((NativeMatchInventory.weight member initialized:ℝ≥0∞)/(2:ℝ≥0∞)^128)

/-- Native stored-key routing at width sixteen is relabeled by its actual
normalization permutation; dummy coordinates remain unchanged. -/
def NativeMatchProductionSixteen_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool), member ∈ ConfigurationFamily.members →
    ∀ h, 1 ≤ h → ∀ ctx : Context member initialized h, ctx.Valid →
    NativeRoutingActual.InputWidth ctx.client 16 →
    ((permLaw 128).prod NativeMatchRouting16.law)
      {p | ∃ e ∈ ctx.inventory (NativeMatchRouting16.native p.1 p.2),
        e.bad (fun key => p.1 (NativeMatchRouting16.block key))} ≤
      (h:ℝ≥0∞)*((NativeMatchInventory.weight member initialized:ℝ≥0∞)/(2:ℝ≥0∞)^128)

/-- Exact arithmetic reserves matching error alongside the actual canonical
capacity-failure probability, before rounding the combined target. -/
def NativeMatchProductionCombined_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool), member ∈ ConfigurationFamily.members →
    ∀ h, 1 ≤ h → ∀ ctx : Context member initialized h, ctx.Valid →
    (IdealKey.tapeLaw.prod (tapeLaw 128))
      {p | ctx.capacityBad p.1 ∨ ∃ e ∈ ctx.inventory p.1, e.bad p.2} ≤
        (h:ℝ≥0∞)*ENNReal.ofReal (1/(2:ℝ)^64)
end RebuildBound.Spec
