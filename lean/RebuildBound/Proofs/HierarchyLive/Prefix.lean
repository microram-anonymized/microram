import RebuildBound.Spec.HierarchyLive
import RebuildBound.Proofs.ApiCapacity
import RebuildBound.Proofs.RequesterCuts

/-! The exact logical prefix attached to each completed rebuild cut. These
lemmas connect independently counted API support to trace history; they never
identify an older physical snapshot with the current map. -/
namespace RebuildBound.HierarchyLiveProof
open Model Model.Hierarchy Model.Online Spec OnlineCorrectnessProof

/-- Decoded record lookup equality transfers through any payload codec. -/
theorem stateOf_congr (c : Api.Codec) {first second : List Rec}
    (h : ∀ key, Probe.latestValue key first = Probe.latestValue key second) :
    Api.stateOf c first = Api.stateOf c second := by
  funext key
  exact congrArg (Option.map c.payload) (h key)

/-- The top's consumed trace history represents the independent API state at
its saturated complete-unit cut, including the trace's empty tail. Initialization
is handled consistently in both start modes; a partial current unit is excluded. -/
theorem consumed_map (cfg : Config) (g : OnlineGeom) (run : OnlineBatch.BatchRun)
    (c : Api.Codec) (requests : List Api.Request)
    (hInit : cfg.initialized = false → run.init = [])
    (hE : 0 < g.unitEntries)
    (hfit : RequesterCuts.WidthsFit g.unitEntries 0 (OnlineBatch.widths run))
    (hlen : requests.length = (OnlineBatch.slots run).length)
    (hcorr : ApiPrefixCorrespondence c run requests) (v : Nat) :
    Api.stateOf c (consumedHistory cfg (OnlineBatch.traceOf g run) v) =
      Api.stateAt (Api.stateOf c run.init) requests
        (RequesterCuts.traceCutSlots g run (time cfg cfg.levels v - cfg.seed 1)) := by
  let n := time cfg cfg.levels v - cfg.seed 1
  have hcuts := RequesterTraceSaturatedCuts g run hE hfit n
  have ht : RequesterCuts.traceCutSlots g run n ≤ requests.length := by
    rw [hlen]
    exact hcuts.1
  rw [← hcorr _ ht]
  have hi : (if cfg.initialized then run.init else []) = run.init := by
    cases hh : cfg.initialized <;> simp [hh, hInit]
  funext key
  unfold Api.stateOf Api.historyAt
  change Api.value c (DirectPrefix.latest key
    ((if cfg.initialized then run.init else []) ++ _)) = _
  rw [hi, latest_append, latest_append,
    hcuts.2 key]

end RebuildBound.HierarchyLiveProof
