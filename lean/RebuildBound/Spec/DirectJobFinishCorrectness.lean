import RebuildBound.Spec.Model.DirectJobBridge

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Original-input correctness of unlimited finish, even if a capacity check
would have failed. No internal phase correctness hypothesis is supplied. -/
def DirectJobFinishConservation_statement : Prop :=
  ∀ (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (b : Table),
    g.Valid → 2 ≤ g.digit → inp.Valid g oldWord → buildB g word inp = .ok b →
    let a := (analyticalA g word inp.aMain).state
    let f := analyticalFinish g word b a.main
      (distributeA g word (aOperational a inp.aTier b.tier)).leaves
    (f.state.main.flatMap Bucket.recs ++ f.tier.recs).Perm inp.winners ∧
    ((f.state.main.flatMap Bucket.recs ++ f.tier.recs).map Rec.key).Nodup

def DirectJobFinishPlacement_statement : Prop :=
  ∀ (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (b : Table),
    g.Valid → 2 ≤ g.digit → inp.Valid g oldWord → buildB g word inp = .ok b →
    let a := (analyticalA g word inp.aMain).state
    let f := analyticalFinish g word b a.main
      (distributeA g word (aOperational a inp.aTier b.tier)).leaves
    f.state.main.length = g.outputHomes ∧
    (∀ bucket ∈ f.state.main, bucket.length = 64) ∧
    (∀ v < g.outputHomes, ∀ x ∈ (f.state.main.getD v []).recs, g.home (word x.key) = v) ∧
    (∀ v < g.outputHomes, (f.state.main.getD v []).recs.length =
      min (inp.winners.countP fun x => g.home (word x.key) == v) 64) ∧
    (∀ x ∈ f.tier.recs, (f.state.main.getD (g.home (word x.key)) []).recs.length = 64)

def DirectJobFinishExactExcess_statement : Prop :=
  ∀ (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (b : Table),
    g.Valid → 2 ≤ g.digit → inp.Valid g oldWord → buildB g word inp = .ok b →
    let a := (analyticalA g word inp.aMain).state
    let f := analyticalFinish g word b a.main
      (distributeA g word (aOperational a inp.aTier b.tier)).leaves
    f.tier.recs.length = inp.excess g word

end RebuildBound.Spec
