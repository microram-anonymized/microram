import RebuildBound.Spec.Model.Api

/-! Deterministic API correctness over the executable reference model. This
contract is independent of key universes, probability and native flags. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online

/-- Observable API correctness: every prefix represents the independent logical
map; every effective probing answer and address agrees. This includes the final
map by taking `t = requests.length`; other-key preservation is part of `Api.step`. -/
def ApiCorrect (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words)
    (dummy : Nat → Nat → Nat) (requests : List Api.Request) : Prop :=
  (∀ t, t ≤ requests.length →
    Api.stateOf c (Api.historyAt run t) = Api.stateAt (Api.stateOf c run.init) requests t) ∧
  ∀ t q s, requests[t]? = some q → (OnlineBatch.slots run)[t]? = some s →
    let result := Probe.batch cfg sh g run S words dummy t
    Api.reply q (Api.value c result.found) =
        Api.reply q (Api.stateAt (Api.stateOf c run.init) requests t q.key) ∧
      Api.scalarReply q (Api.value c result.found) =
        Api.scalarReply q (Api.stateAt (Api.stateOf c run.init) requests t q.key) ∧
      (s.probes = true → ∀ i, result.addresses.getD i 0 =
        OnlineBatch.touched cfg sh g run S words dummy t i)

end RebuildBound.Spec
