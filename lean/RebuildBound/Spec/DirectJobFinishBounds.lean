import RebuildBound.Spec.Model.DirectJobBridge

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Every insertion and drain occupancy is bounded by the newest full union's
final excess. B production must succeed; A, distribution and finish checks
may overflow on this analytical continuation. -/
def DirectJobFinishBounds_statement : Prop :=
  ∀ (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (b : Table),
    g.Valid → 2 ≤ g.digit → inp.Valid g oldWord → buildB g word inp = .ok b →
    let a := (analyticalA g word inp.aMain).state
    let f := analyticalFinish g word b a.main
      (distributeA g word (aOperational a inp.aTier b.tier)).leaves
    ∀ e ∈ f.trace, e.occupancy ≤ inp.excess g word

/-- With insertion storage at least the output width, a failed finish implies
output-width excess. This does not suppress earlier A/B/distribution failures. -/
def DirectJobFinishFailureExcess_statement : Prop :=
  ∀ (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (b : Table)
    (e : CheckEvent),
    g.Valid → 2 ≤ g.digit → inp.Valid g oldWord → buildB g word inp = .ok b →
    let a := (analyticalA g word inp.aMain).state
    finishBounded g word b a.main
      (distributeA g word (aOperational a inp.aTier b.tier)).leaves = .error e →
    g.outputCapacity < inp.excess g word

end RebuildBound.Spec
