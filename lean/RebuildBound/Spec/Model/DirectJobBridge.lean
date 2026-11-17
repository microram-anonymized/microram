import RebuildBound.Spec.Model.DirectJobFinish

/-! Core-only adapter to the separated proof library. Page metadata is used
only to state its input shape; operational capacities remain direct slot counts. -/
namespace RebuildBound.Model.DirectJob

def separatedInputs (inp : Inputs) (b : Table) : SInputs :=
  ⟨inp.aMain, inp.aTier, b.bLanes, [b.tier]⟩

/-- Newest complete records of the original chronological inputs. B wins over
A for every shared key, including tombstones. -/
def Inputs.winners (inp : Inputs) : List Rec :=
  let fresh := DirectPrefix.winners inp.bRecords
  fresh ++ inp.aRecords.filter fun x => !(fresh.map Rec.key).contains x.key

def Inputs.excess (inp : Inputs) (g : Geometry) (word : LogicalKey → Nat) : Nat :=
  ((List.range g.outputHomes).map fun v =>
    (inp.winners.countP fun x => g.home (word x.key) == v) - 64).sum

end RebuildBound.Model.DirectJob
