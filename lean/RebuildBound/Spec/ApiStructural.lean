import RebuildBound.Spec.Model.ApiAdaptive
import RebuildBound.Spec.ApiCorrectness.Core
import RebuildBound.Spec.OnlineBase
import RebuildBound.Spec.HierarchyLive

/-! Deterministic request semantics and live populations without a key universe.
The constructor derives trace structure, flags and every logical prefix before
logical capacity is used. Records use exact logical byte keys; no
probability law or native correspondence is asserted here. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.PublicApi

/-- Derived properties of a physical request run, valid on every reference tape.
This is a conclusion, never a client admissibility assumption. -/
def ApiRunCorrect (geo : HierarchyGeometry) (c : Api.Codec) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (requests : List Api.Request) : Prop :=
  TraceStructural geo.cfg (OnlineBatch.traceOf g run) ∧
  UnshPromise geo.cfg geo.shapes (OnlineBatch.traceOf g run) ∧
  ∀ words dummy,
    Api.Implements c geo.cfg geo.shapes g run S words dummy requests ∧
    ApiCorrect c geo.cfg geo.shapes g run S words dummy requests

/-- The four population conclusions for all potential top ordinals in the
configured inventory. Beyond the finite frozen trace, empty inputs retain the
last complete-unit logical prefix. Physical continuation and agreement with the
final partial unit are separate obligations. -/
def ApiTopPopulations (geo : HierarchyGeometry) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) : Prop :=
  run.init.length ≤ geo.keyCapacity ∧
  ∀ (words : Words) v, geo.cfg.seed geo.cfg.levels < v →
    v ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels →
    (prepInputsAt geo.cfg geo.shapes (OnlineBatch.traceOf g run) words v).aAll.length ≤
      geo.keyCapacity ∧
    (finishInputsAt geo.cfg geo.shapes (OnlineBatch.traceOf g run) words v).aAll.length ≤
      geo.keyCapacity ∧
    (finishInputsAt geo.cfg geo.shapes (OnlineBatch.traceOf g run) words v).live.length ≤
      geo.keyCapacity

/-- Actual initialization size suffices for deterministic correctness. Neither
live capacity nor a bound on keys or on historical distinct keys is required. -/
def ApiExecutionStructural_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ (c : Api.Codec) g S init (groups : List (PublicApi.Group Api.Request)) m,
    (geo.cfg.initialized = false → init = []) →
    (init.map Rec.key).Nodup → init.length ≤ geo.init.C / 2 * geo.init.T →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → (groups.flatMap Group.lanes).length ≤ geo.cfg.horizon →
    (∀ group ∈ groups, ApiExecution.Valid group) →
    SchedulePremises geo.cfg S (groups.flatMap Group.lanes).length m →
    ApiRunCorrect geo c g (ApiExecution.run c geo.cfg geo.shapes g S init groups)
      S (groups.flatMap Group.lanes)

/-- Live capacity and public cut alignment now derive the actual job loads;
API prefix correspondence, trace structure and flags are all conclusions. -/
def ApiExecutionLive_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ (c : Api.Codec) g S init (groups : List (PublicApi.Group Api.Request)) m,
    ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized init →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → (groups.flatMap Group.lanes).length ≤ geo.cfg.horizon →
    (∀ group ∈ groups, ApiExecution.Valid group) →
    GroupsFit g.unitEntries 0 groups →
    SchedulePremises geo.cfg S (groups.flatMap Group.lanes).length m →
    ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c init)
      (init.map Rec.key) (groups.flatMap Group.lanes) →
    let run := ApiExecution.run c geo.cfg geo.shapes g S init groups
    ApiRunCorrect geo c g run S (groups.flatMap Group.lanes) ∧ ApiTopPopulations geo g run

/-- Generated public frames preserve each batch's decision point. The chooser
can introduce new keys on every observation branch, with no common dictionary. -/
def ApiAdaptiveStructural_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ (c : Api.Codec) g S init m width batches (choose : ApiAdaptive.Chooser m),
    let fs := ApiAdaptive.frames width g.unitEntries batches
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    (geo.cfg.initialized = false → init = []) →
    (init.map Rec.key).Nodup → init.length ≤ geo.init.C / 2 * geo.init.T →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    ∀ words dummy,
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs choose
    let t := Adaptive.transcript geo.cfg geo.shapes g S a n words dummy
    let qs := (ApiAdaptive.requestGroups choose (Adaptive.rowsOf t n) fs).flatMap Group.lanes
    ApiRunCorrect geo c g (Adaptive.realized geo.cfg geo.shapes g S a words dummy) S qs

/-- Branchwise logical capacity suffices for adaptive live populations. Rows
retain the existing Nat-valued transcript interface; legal-observation types
and probability/exposure laws are established by separate contracts. -/
def ApiAdaptiveLive_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ (c : Api.Codec) g S init m width batches (choose : ApiAdaptive.Chooser m),
    let fs := ApiAdaptive.frames width g.unitEntries batches
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized init →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    (∀ t : Fin n → Fin m → Nat,
      ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c init) (init.map Rec.key)
        ((ApiAdaptive.requestGroups choose (Adaptive.rowsOf t n) fs).flatMap Group.lanes)) →
    ∀ words dummy,
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs choose
    let t := Adaptive.transcript geo.cfg geo.shapes g S a n words dummy
    let qs := (ApiAdaptive.requestGroups choose (Adaptive.rowsOf t n) fs).flatMap Group.lanes
    let realized := Adaptive.realized geo.cfg geo.shapes g S a words dummy
    ApiRunCorrect geo c g realized S qs ∧ ApiTopPopulations geo g realized

end RebuildBound.Spec
