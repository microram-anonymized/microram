import RebuildBound.Spec.ApiLegal

/-! Bounded API correctness over arbitrary logical keys. Actual histories,
requests and selected results agree with the reference off its capacity-failure
event. This is an explicit adapter premise, not a native refinement proof.
The transfer needs neither live capacity nor a probability law. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online MeasureTheory

/-- Correctness of the adapter's actual request history and probe results.
The public slot count prevents truncated executions from making replies vacuous.
The address count distinguishes omitted zero addresses from actual probes and
requires blind operations to have no addresses. Every logical prefix and both
reply conventions are covered. -/
def ApiResultsCorrect (geo : HierarchyGeometry) (c : Api.Codec) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (n : Nat) (words : Words)
    (dummy : Nat → Nat → Nat) (requests : List Api.Request)
    (actual : Nat → Probe.Result) : Prop :=
  requests.length = n ∧ requests.length = (OnlineBatch.slots run).length ∧
  (∀ t, t ≤ requests.length →
    Api.stateOf c (Api.historyAt run t) = Api.stateAt (Api.stateOf c run.init) requests t) ∧
  ∀ t q s, requests[t]? = some q → (OnlineBatch.slots run)[t]? = some s →
    Api.reply q (Api.value c (actual t).found) =
        Api.reply q (Api.stateAt (Api.stateOf c run.init) requests t q.key) ∧
      Api.scalarReply q (Api.value c (actual t).found) =
        Api.scalarReply q (Api.stateAt (Api.stateOf c run.init) requests t q.key) ∧
      (actual t).addresses.length =
        (if s.probes then (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables.length
          else 0) ∧
      (s.probes = true → ∀ i, (actual t).addresses.getD i 0 =
        OnlineBatch.touched geo.cfg geo.shapes g run S words dummy t i)

/-- Adaptive adapters must preserve issued requests as well as physical history
and selected results before failure. Nothing is constrained on failure. -/
def ApiBoundedAgreement (geo : HierarchyGeometry) (c : Api.Codec) (g : OnlineGeom)
    (S : Schedule) (m width : Nat) (batches : List ApiAdaptive.Batch)
    (init : List Rec)
    (choose : ApiLegal.Chooser geo.cfg
      (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches)) S m)
    (words : Words) (dummy : Nat → Nat → Nat)
    (run : OnlineBatch.BatchRun) (requests : List Api.Request)
    (actual : Nat → Probe.Result) : Prop :=
  let fs := ApiAdaptive.frames width g.unitEntries batches
  let compiled := ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose
  let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled
  let n := Adaptive.slotCount (ApiAdaptive.shape fs)
  ¬ Fails geo.cfg geo.shapes
    (OnlineBatch.traceOf g (Adaptive.realized geo.cfg geo.shapes g S a words dummy)) words →
    run = Adaptive.realized geo.cfg geo.shapes g S a words dummy ∧
    requests = (ApiAdaptive.requestGroups compiled
      (Adaptive.rowsOf (Adaptive.transcript geo.cfg geo.shapes g S a n words dummy) n)
      fs).flatMap PublicApi.Group.lanes ∧
    ∀ t < requests.length,
      actual t = Probe.batch geo.cfg geo.shapes g run S words dummy t

/-- Generic deterministic transfer and error-event inclusion under any measure.
Actual initialization size suffices; no key dictionary, live-capacity bound,
numerical certificate or supplied correctness conclusion is assumed. -/
def ApiBoundedTransfer_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ (c : Api.Codec) g S init m width batches,
    let fs := ApiAdaptive.frames width g.unitEntries batches
    ∀ choose : ApiLegal.Chooser geo.cfg (ApiAdaptive.shape fs) S m,
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    (geo.cfg.initialized = false → init = []) →
    (init.map Rec.key).Nodup → init.length ≤ geo.init.C / 2 * geo.init.T →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs
      (ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose)
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      (words : Ω → Words) (dummy : Ω → Nat → Nat → Nat)
      (runs : Ω → OnlineBatch.BatchRun) (requests : Ω → List Api.Request)
      (actual : Ω → Nat → Probe.Result),
    (∀ ω, ApiBoundedAgreement geo c g S m width batches init choose
      (words ω) (dummy ω) (runs ω) (requests ω) (actual ω)) →
    (∀ ω, ¬ Fails geo.cfg geo.shapes
        (OnlineBatch.traceOf g (Adaptive.realized geo.cfg geo.shapes g S a (words ω) (dummy ω)))
        (words ω) →
      ApiResultsCorrect geo c g (runs ω) S n (words ω) (dummy ω) (requests ω) (actual ω)) ∧
    μ {ω | ¬ ApiResultsCorrect geo c g (runs ω) S n
        (words ω) (dummy ω) (requests ω) (actual ω)} ≤
      μ {ω | Fails geo.cfg geo.shapes
        (OnlineBatch.traceOf g (Adaptive.realized geo.cfg geo.shapes g S a (words ω) (dummy ω)))
        (words ω)}

end RebuildBound.Spec
