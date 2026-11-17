import RebuildBound.Spec.Model.DirectJobChain

/-! Total logical histories, including outcomes after capacity failure. This
reference table has an unrestricted tier and is never a publishable Output.
Successful jobs retain their exact lanes. Otherwise empty main buckets and the
complete newest union provide a shape-correct reference completion; this is
not the analytical phase continuation or a claim about native execution. -/
namespace RebuildBound.Model.DirectJob

structure ReferenceTable where
  main : List Bucket
  tier : List Rec

namespace ReferenceTable

def records (st : ReferenceTable) : List Rec :=
  st.main.flatMap Bucket.recs ++ st.tier

def inputs (st : ReferenceTable) (units : List Bucket) : Inputs :=
  ⟨st.main, st.tier, units⟩

def ofOutput (out : Output) : ReferenceTable :=
  ⟨out.main, Bucket.recs out.tier⟩

end ReferenceTable

/-- No tier truncation or capacity assertion is made after failure. -/
def referenceFallback (g : Geometry) (inp : Inputs) : ReferenceTable :=
  ⟨List.replicate g.outputHomes (List.replicate 64 none), inp.winners⟩

def referenceStep (oldWord : LogicalKey → Nat) (st : ReferenceTable) (job : ChainJob) :
    ReferenceTable :=
  let inp := st.inputs job.units
  match runJob job.geometry oldWord job.word inp with
  | .published out => ReferenceTable.ofOutput out
  | _ => referenceFallback job.geometry inp

def referenceChain (oldWord : LogicalKey → Nat) (st : ReferenceTable) :
    List ChainJob → ReferenceTable
  | [] => st
  | job :: rest => referenceChain job.word (referenceStep oldWord st job) rest

/-- One bounded result at each potential ordinal, on its total reference input.
Later entries remain defined even when the actual bounded chain has stopped. -/
def referenceResults (oldWord : LogicalKey → Nat) (st : ReferenceTable) :
    List ChainJob → List LaneResult
  | [] => []
  | job :: rest => runJob job.geometry oldWord job.word (st.inputs job.units) ::
      referenceResults job.word (referenceStep oldWord st job) rest

/-- Adapter for the shared probability input shape. The complete deduplicated
B population is placed in its single unrestricted reference tier. Actual B
production is still performed by runJob on the original chronological units. -/
def referenceSepInputs (s : SepGeom) (st : ReferenceTable) (units : List Bucket) : SInputs :=
  ⟨st.main, st.tier, List.replicate s.U (List.replicate s.C none),
    [DirectPrefix.winners (DirectMasks.records units)]⟩

end RebuildBound.Model.DirectJob
