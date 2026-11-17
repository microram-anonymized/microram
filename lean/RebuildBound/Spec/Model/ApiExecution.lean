import RebuildBound.Spec.Model.ApiLowering

/-!
# Constructing physical postrecords from grouped requests

Requests have already been chosen before this execution starts. Each probing
lane computes its selected record on a provisional run containing the completed
operations, earlier lanes of its group, and a placeholder with its own key.
All-zero tapes make this a deterministic construction from requests alone.
Selected-record causality relates these provisional probes to the completed
run; transfer to actual tapes is a separate theorem with the existing setting.

In particular, chronological reference records cannot replace these probes:
publication can discard a tombstone whose flag still matters to a later lane.
This executable construction imports only the Core/Std model.
-/
namespace RebuildBound.Model.ApiExecution
open Hierarchy Online OnlineBatch PublicApi

/-- Public grouping agrees with each primitive request's probe bit. -/
def Valid : Group Api.Request → Prop
  | .blind q => q.probes = false
  | .chunk qs => ∀ q ∈ qs, q.probes = true

/-- Number of occupied positions in the preceding operations. -/
def offset (ops : List OnlineBatch.Op) : Nat :=
  (ops.map fun op => op.lanes.length).sum

/-- A provisional lane has its final key; its value and tombstone are irrelevant
to the probe before that lane's insertion. -/
def provisional (c : Api.Codec) (init : List Rec) (pre : List OnlineBatch.Op)
    (earlier : List Rec) (q : Api.Request) : BatchRun :=
  ⟨pre ++ [.batch (earlier ++ [Api.postRecord c q none])], init,
    fun r => c.flag r.val⟩

/-- Construct lanes in order, so duplicate forwarding sees the newly computed
record, including its tombstone and inherited flag. -/
def chunkRecords (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) (init : List Rec) (pre : List OnlineBatch.Op) :
    List Rec → List Api.Request → List Rec
  | _, [] => []
  | earlier, q :: qs =>
      let selected := (Probe.batch cfg sh g (provisional c init pre earlier q)
        S (fun _ _ _ => 0) (fun _ _ => 0) (offset pre + earlier.length)).found
      let r := Api.postRecord c q selected
      r :: chunkRecords c cfg sh g S init pre (earlier ++ [r]) qs

/-- One physical operation; an output-free write requires no selected record. -/
def operation (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) (init : List Rec) (pre : List OnlineBatch.Op) :
    Group Api.Request → OnlineBatch.Op
  | .blind q => .blind (Api.postRecord c q none)
  | .chunk qs => .batch (chunkRecords c cfg sh g S init pre [] qs)

/-- Carry completed physical operations across every internal cut. -/
def operations (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) (init : List Rec) :
    List OnlineBatch.Op → List (Group Api.Request) → List OnlineBatch.Op
  | _, [] => []
  | pre, group :: rest =>
      let op := operation c cfg sh g S init pre group
      op :: operations c cfg sh g S init (pre ++ [op]) rest

def run (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) (init : List Rec) (groups : List (Group Api.Request)) : BatchRun :=
  ⟨operations c cfg sh g S init [] groups, init, fun r => c.flag r.val⟩

end RebuildBound.Model.ApiExecution
