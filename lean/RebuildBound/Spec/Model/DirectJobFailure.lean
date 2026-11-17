import RebuildBound.Spec.Model.DirectJobBridge

/-! Unconditional analytical continuation and deterministic failure witnesses.
Overflowing storage is private analytical data, never a publishable Output. -/
namespace RebuildBound.Model.DirectJob

/-- Restore all B residuals, even when the standalone B capacity is exceeded. -/
def analyticalBTable (g : Geometry) (word : LogicalKey → Nat) (inp : Inputs) : Table :=
  let restored := DirectRecords.restore inp.bRecords
    (DirectB.main 64 (bHomes g word inp), (analyticalB g word inp).records)
  ⟨restored.1, restored.2⟩

structure AnalyticalJob where
  main : List Bucket
  tier : Bucket
  trace : List CheckEvent

/-- Continue every phase after failed checks, retaining their original capacities.
Geometry/input rejection is handled separately by runJob. -/
def analyticalJob (g : Geometry) (word : LogicalKey → Nat) (inp : Inputs) : AnalyticalJob :=
  let b := analyticalBTable g word inp
  if g.digit = 1 then
    ⟨b.bLanes, b.tier.map some, (analyticalB g word inp).trace⟩
  else
    let a := analyticalA g word inp.aMain
    let d := distributeA g word (aOperational a.state inp.aTier b.tier)
    let f := analyticalFinish g word b a.state.main d.leaves
    ⟨f.state.main, f.tier,
      a.trace ++ (analyticalB g word inp).trace ++ d.trace ++ f.trace⟩

/-- Completed A route storage checks, defined without any B input or success
condition. Stronger shadow/coarse-range probability comparisons are separate. -/
def aRouteWitness (g : Geometry) (word : LogicalKey → Nat) (inp : Inputs) : Prop :=
  ∃ e ∈ (analyticalA g word inp.aMain).trace, e.capacity < e.occupancy

/-- Unfiltered completed residuals supply the same DFS checks/capacities as the
operational pool. The direct branch has no distributor witness. -/
def aRangeWitness (g : Geometry) (word : LogicalKey → Nat) (inp : Inputs) : Prop :=
  ∃ e ∈ (distributeA g word (aResidual (analyticalA g word inp.aMain).state inp.aTier)).trace,
    e.capacity < e.occupancy

/-- All four events are defined on every assignment, including earlier failures.
No independence or conditioning on producer success is used. -/
def failureWitness (g : Geometry) (word : LogicalKey → Nat) (inp : Inputs) : Prop :=
  g.bCapacity < bExcess g word inp ∨
  aRouteWitness g word inp ∨ aRangeWitness g word inp ∨
  g.outputCapacity < inp.excess g word

end RebuildBound.Model.DirectJob
