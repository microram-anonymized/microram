import RebuildBound.Spec.Model.ApiLowering

/-!
# Public batch choices across internal cuts

A public batch chooses keys and values from its pre-batch observations. Public
descriptors fix the internal partition. The adapter may be invoked again after
each internal operation, with additional observations, but gives the chooser
only the original prefix. This is a request adapter: selected records and flags
are computed subsequently, rather than fixed at the public decision point.

`position` is the occupied requester position at this batch's start. A nonzero
position describes continuation of an existing execution, not a fresh run.
-/
namespace RebuildBound.Model.PublicApi

/-- Private keys and values; descriptors and lane count belong to the public plan.
The caller may close over its public batch index and independent client state. -/
abbrev Chooser (Row : Type) := List Row → Nat → LogicalKey × Nat

def chosenLane {Row : Type} (choose : Chooser Row) (rows : List Row)
    (indexed : Descriptor × Nat) : Lane :=
  ⟨(choose rows indexed.2).1, (choose rows indexed.2).2, indexed.1⟩

def chosenLanes {Row : Type} (choose : Chooser Row) (rows : List Row)
    (descriptors : List Descriptor) : List Lane :=
  descriptors.zipIdx.map (chosenLane choose rows)

/-- Public lane indices survive every descriptor and requester-boundary split. -/
def indexedGroups (width entries position : Nat) (found : Bool)
    (descriptors : List Descriptor) : List (Group (Descriptor × Nat)) :=
  partition width entries position (fun d => probes found d.1) descriptors.zipIdx

/-- Re-enter at each internal group with that group's current observations.
Only the pre-public-batch prefix is supplied to the external chooser. -/
def dispatch {Row : Type} (choose : Chooser Row) (start : Nat)
    (observations : Nat → List Row) : Nat → List (Group (Descriptor × Nat)) → List (Group Lane)
  | _, [] => []
  | j, group :: rest =>
      group.map (chosenLane choose ((observations j).take start)) ::
        dispatch choose start observations (j + 1) rest

/-- The slot schedule induced by the emitted groups, using the same operation
start convention as `OnlineBatch`. -/
def groupSchedule (groups : List (Group Lane)) (schedule : Online.Schedule) : Online.Schedule :=
  OnlineBatch.slotSchedule (groups.map fun group => group.lanes.length) schedule

/-- Chronological reference execution carries the full history across cuts.
Records (including tombstone flags) are constructed at each lane, after earlier
lanes; internal splitting does not introduce another external request choice.
This reference is distinct from the physical hierarchy's selected-record rule. -/
def referenceGroups (c : Api.Codec) (found : Bool) : List Rec → List (Group Lane) → List Rec
  | _, [] => []
  | history, group :: rest =>
      let records := Api.referenceRecords c history (group.lanes.map (request found))
      records ++ referenceGroups c found (history ++ records) rest

end RebuildBound.Model.PublicApi
