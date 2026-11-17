import RebuildBound.Spec.Model.ApiExecution
import RebuildBound.Spec.Model.ApiGrouped
import RebuildBound.Spec.Model.Adaptive

/-!
# API request clients over public batches

Each external batch has one decision point. Its internal frames retain that
batch's start and lane indices, so replaying a later frame cannot expose newly
arrived rows to its chooser. Physical postrecords are reconstructed from the
whole preceding execution, rather than chosen before the batch executes.
-/
namespace RebuildBound.Model.ApiAdaptive
open Hierarchy Online PublicApi

structure Batch where
  found : Bool
  descriptors : List Descriptor
  deriving DecidableEq, Repr

structure Frame where
  batchIndex : Nat
  start : Nat
  found : Bool
  group : Group (Descriptor × Nat)
  deriving DecidableEq, Repr

def Frame.kind (frame : Frame) : Adaptive.Kind :=
  match frame.group with
  | .blind _ => .blind
  | .chunk ds => .chunk ds.length

/-- Empty public batches consume no slots, but keep their public indices. -/
def framesFrom (width entries : Nat) : Nat → Nat → List Batch → List Frame
  | _, _, [] => []
  | batchIndex, start, batch :: rest =>
      (indexedGroups width entries start batch.found batch.descriptors).map
        (fun group => ⟨batchIndex, start, batch.found, group⟩) ++
      framesFrom width entries (batchIndex + 1) (start + batch.descriptors.length) rest

def frames (width entries : Nat) (batches : List Batch) : List Frame :=
  framesFrom width entries 0 0 batches

/-- Public frame starts are causal and every internal operation advances the
observation count. Generated partitions discharge this predicate. -/
def Causal : Nat → List Frame → Prop
  | _, [] => True
  | offset, frame :: rest =>
      frame.start ≤ offset ∧ 0 < frame.kind.width ∧
      Causal (offset + frame.kind.width) rest

abbrev Chooser (m : Nat) := Nat → PublicApi.Chooser (Fin m → Nat)

def requests {m : Nat} (choose : Chooser m) (rows : List (Fin m → Nat))
    (frame : Frame) : Group Api.Request :=
  frame.group.map (fun indexed => request frame.found
    (chosenLane (choose frame.batchIndex) (rows.take frame.start) indexed))

def requestGroups {m : Nat} (choose : Chooser m) (rows : List (Fin m → Nat))
    (fs : List Frame) : List (Group Api.Request) := fs.map (requests choose rows)

def shape (fs : List Frame) : List Adaptive.Kind := fs.map Frame.kind

def records (ops : List OnlineBatch.Op) : List Rec :=
  ops.flatMap fun op => op.lanes.map Prod.fst

/-- All computation uses public parameters, chosen requests and zero tapes.
The unexecuted suffix cannot affect an earlier physical operation. -/
def client (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) (init : List Rec) {m : Nat} (fs : List Frame) (choose : Chooser m) :
    Adaptive.Client m := fun rows i =>
  (records (ApiExecution.run c cfg sh g S init (requestGroups choose rows fs)).ops).getD
    (rows.length + i) default

def run (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (S : Schedule) (init : List Rec) {m : Nat} (fs : List Frame) (choose : Chooser m) :
    Adaptive.AdaptiveRun m :=
  ⟨shape fs, init, fun r => c.flag r.val, client c cfg sh g S init fs choose⟩

end RebuildBound.Model.ApiAdaptive
