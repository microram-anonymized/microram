import RebuildBound.Spec.Model.DirectJobBridge

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Published lanes contain each original newest full record exactly once,
with the requested geometry, saturated homes, and exact total overflow. -/
def DirectJobOutputCorrect (g : Geometry) (word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (out : Output) : Prop :=
  (out.main.flatMap Bucket.recs ++ (Bucket.recs out.tier)).Perm inp.winners ∧
  ((out.main.flatMap Bucket.recs ++ (Bucket.recs out.tier)).map Rec.key).Nodup ∧
  out.main.length = g.outputHomes ∧
  (∀ bucket ∈ out.main, bucket.length = 64) ∧
  out.tier.length = g.outputCapacity ∧
  (∀ v < g.outputHomes, ∀ x ∈ (out.main.getD v []).recs, g.home (word x.key) = v) ∧
  (∀ v < g.outputHomes, (out.main.getD v []).recs.length =
    min (inp.winners.countP fun x => g.home (word x.key) == v) 64) ∧
  (Bucket.recs out.tier).length = inp.excess g word

/-- All supported digits. Successful publication itself entails valid original
inputs; no supplied phase-correctness hypothesis is hidden in the interface. -/
def DirectJobPublication_statement : Prop :=
  ∀ (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (out : Output),
    runJob g oldWord word inp = .published out →
    g.Valid ∧ inp.Valid g oldWord ∧ DirectJobOutputCorrect g word inp out

end RebuildBound.Spec
