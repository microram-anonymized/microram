import RebuildBound.Spec.NativeMatch.Coded

/-! Additive semantic correctness for the actual native API execution.
This retains logical prefix maps, both reply conventions, public slot counts,
and actual address counts. It does not require each physical address to equal
the original logical-key reference on the same random tape. -/
namespace RebuildBound.Spec
open Model Model.Online

def ApiSemanticResultsCorrect (c : Api.Codec) (run : OnlineBatch.BatchRun)
    (S : Schedule) (n : Nat) (requests : List Api.Request)
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
          else 0)

end RebuildBound.Spec

namespace RebuildBound.Spec.NativeMatchSemantic
open Model NativeMatchProduction NativeMatchApi NativeMatchEndpoint

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def ResultsCorrect (ctx : Context member initialized h)
    (state : State ctx.transcriptWidth) : Prop :=
  ApiSemanticResultsCorrect ctx.codec
    ⟨state.ops,ctx.init,fun r=>ctx.codec.flag r.val⟩ ctx.schedule ctx.accesses state.requests
    (fun t=>state.selected.getD t ⟨none,[]⟩) ∧
      state.selected.length = ctx.accesses ∧ state.rows.length = ctx.accesses

/-- An actual producer stop, truncated public result, incorrect logical reply
or incorrect logical prefix is a failure. Physical observation is handled by a
separate distributional statement over NativeMatchCoded.observed. -/
def failure (ctx : Context member initialized h) (policy : Policy) (model : KeyModel)
    (p : NativeMatchCoded.Sample model) : Prop :=
  match production ctx policy (NativeMatchCoded.stored model p.1.2) (NativeMatchCoded.routing ctx model p) with
  | .error _ => True
  | .ok state => ¬ResultsCorrect ctx state

end RebuildBound.Spec.NativeMatchSemantic
