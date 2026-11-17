import RebuildBound.Spec.Model.Basic

/-! The online stash's unit discipline, from
`src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp`,
`cpu_byteslice_level_arena_dense.hpp` and `cpu_byteslice_level_arena_batch.hpp`.

The requester appends entries to the current unit; a unit that fills freezes
and the next starts with cleared masks (`FreezeUnit`,
`SeedDirectInitialization`). Before its one insert, a serial access removes its
key from the current unit, by the probe (the current unit is the plan's only
removable run) or by `ClearFromCurrentUnit` for an unprobed write. A batch
removes every lane's key from the current unit (deferred removal applied once
after the cascade), then inserts its lanes in order; a lane whose key a later
lane repeats is superseded and inserted non-real. Frozen units are not changed.

Native premises outside this model: every public operation follows this
discipline, the removal and the batch duplicate detection compare stored keys
exactly, and `real = false` leaves the lane's occupancy bit clear.
-/
namespace RebuildBound.Model.Requester

inductive Op where
  /-- One access: remove `r.key` from the current unit, then insert `r`
  (non-real: an unoccupied lane). -/
  | access (r : Rec) (real : Bool)
  /-- One batch job's lanes in request order. -/
  | batch (lanes : List Rec)

structure State where
  /-- Frozen units, oldest first. -/
  frozen : List Bucket
  /-- The current unit's lanes so far. -/
  current : Bucket

/-- Remove every copy of `key` from a unit, keeping lane positions. -/
def clearKey (key : LogicalKey) (unit : Bucket) : Bucket :=
  unit.map (·.filter (·.key != key))

/-- Insert one lane; a unit of `entries` lanes freezes and an empty one begins. -/
def insert (entries : Nat) (st : State) (lane : Option Rec) : State :=
  if entries ≤ (st.current ++ [lane]).length then ⟨st.frozen ++ [st.current ++ [lane]], []⟩
  else ⟨st.frozen, st.current ++ [lane]⟩

/-- Lane `i` of a batch is superseded when a later lane repeats its key. -/
def superseded (lanes : List Rec) (i : Nat) (r : Rec) : Bool :=
  (lanes.drop (i + 1)).any (·.key == r.key)

def step (entries : Nat) (st : State) : Op → State
  | .access r real =>
    insert entries ⟨st.frozen, clearKey r.key st.current⟩ (if real then some r else none)
  | .batch lanes =>
    lanes.zipIdx.foldl
      (fun s ri => insert entries s (if superseded lanes ri.2 ri.1 then none else some ri.1))
      ⟨st.frozen, lanes.foldl (fun u r => clearKey r.key u) st.current⟩

def run (entries : Nat) (st : State) (ops : List Op) : State :=
  ops.foldl (step entries) st

/-- Every unit, frozen or current, has distinct keys. -/
def Unique (st : State) : Prop :=
  (∀ u ∈ st.frozen, (u.recs.map Rec.key).Nodup) ∧ (st.current.recs.map Rec.key).Nodup

end RebuildBound.Model.Requester
