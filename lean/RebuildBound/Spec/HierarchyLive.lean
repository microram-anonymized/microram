import RebuildBound.Spec.ApiCapacity
import RebuildBound.Spec.HierarchyStructural
import RebuildBound.Spec.RequesterCuts

/-! Intermediate composition of chronological cuts and independent logical
capacity. API prefix correctness and the local flag promise are named premises
here; the eventual request-level theorem must derive them. No per-job population
bound or bound on historical keys is assumed. The total finite-run trace has an
empty tail; its cuts saturate at the last complete requester unit. A physical
continuation is a separate obligation. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online

/-- Map correspondence at every logical lane prefix, stated separately from
capacity and from physical flag construction. -/
def ApiPrefixCorrespondence (c : Api.Codec) (run : OnlineBatch.BatchRun)
    (requests : List Api.Request) : Prop :=
  ∀ t, t ≤ requests.length →
    Api.stateOf c (Api.historyAt run t) =
      Api.stateAt (Api.stateOf c run.init) requests t

/-- Initialization, preparation, finish A and finish live winners inherit
capacity from the corresponding logical prefixes. Every potential top ordinal
in the configured inventory is covered: trace cuts past the supplied frozen units saturate at the last
complete-unit prefix. This does not append physical operations. -/
def HierarchyLivePopulations_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ (g : OnlineGeom) (run : OnlineBatch.BatchRun) (c : Api.Codec)
      (requests : List Api.Request),
    ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized run.init →
    0 < g.unitEntries →
    RequesterCuts.WidthsFit g.unitEntries 0 (OnlineBatch.widths run) →
    TraceStructural geo.cfg (OnlineBatch.traceOf g run) →
    UnshPromise geo.cfg geo.shapes (OnlineBatch.traceOf g run) →
    requests.length = (OnlineBatch.slots run).length →
    ApiPrefixCorrespondence c run requests →
    ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c run.init)
      (run.init.map Rec.key) requests →
    run.init.length ≤ geo.keyCapacity ∧
    ∀ (words : Words) v, geo.cfg.seed geo.cfg.levels < v →
      v ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels →
      (prepInputsAt geo.cfg geo.shapes (OnlineBatch.traceOf g run) words v).aAll.length ≤
        geo.keyCapacity ∧
      (finishInputsAt geo.cfg geo.shapes (OnlineBatch.traceOf g run) words v).aAll.length ≤
        geo.keyCapacity ∧
      (finishInputsAt geo.cfg geo.shapes (OnlineBatch.traceOf g run) words v).live.length ≤
        geo.keyCapacity

end RebuildBound.Spec
