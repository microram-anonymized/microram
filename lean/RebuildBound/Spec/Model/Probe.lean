import RebuildBound.Spec.Model.OnlineBatch
import RebuildBound.Spec.Model.DirectPrefix

/-!
# Exact-key probe results

The dense snapshot is chronological. Each table probe scans one main bucket
and its complete tier; it never consults table-wide membership. A tombstone
is a hit and suppresses every later value. Every table is still visited, using
a dummy bucket after a hit. Batch duplicates start with the latest earlier
lane's supplied record, modeling the effective answer after forwarding.
-/
namespace RebuildBound.Model.Probe

open Hierarchy Online

/-- Interpret a selected record only after the cascade has finished. -/
def decode : Option Rec → Option Nat
  | none => none
  | some r => if r.tomb then none else some r.val

/-- The logical value of the newest supplied record for an exact key. -/
def latestValue (key : LogicalKey) (history : List Rec) : Option Nat :=
  decode (DirectPrefix.latest key history)

/-- Search precisely the selected main bucket and the complete tier. -/
def scan (key : LogicalKey) (t : Output) (address : Nat) : Option Rec :=
  DirectPrefix.latest key ((t.main.getD address []).recs ++ Bucket.recs t.tier)

/-- The selected record (including tombstones) and one address per table. -/
structure Result where
  found : Option Rec
  addresses : List Nat
  deriving DecidableEq, Repr

/-- Shared cascade engine. The exact scanner and native dense-tier scanner
instantiate the same state/address transition. -/
def cascadeWith (scanAt : Nat × Nat → Nat → Option Rec)
    (real : Nat × Nat → Nat) (dummy : Nat → Nat × Nat → Nat) :
    List (Nat × Nat) → Option Rec → Nat → Result
  | [], found, _ => ⟨found, []⟩
  | c :: cs, found, offset =>
    let address := if found.isSome then dummy offset c else real c
    let hit := found.orElse (fun _ => scanAt c address)
    let rest := cascadeWith scanAt real dummy cs hit (offset + 1)
    ⟨rest.found, address :: rest.addresses⟩

/-- Exact-key cascade, freshest table first. `offset` indexes the dummy tape. -/
def cascade (key : LogicalKey) (tableAt : Nat × Nat → Output)
    (real : Nat × Nat → Nat) (dummy : Nat → Nat × Nat → Nat) :
    List (Nat × Nat) → Option Rec → Nat → Result :=
  cascadeWith (fun c address => scan key (tableAt c) address) real dummy

/-- Run a hierarchy plan from a dense or forwarded hit. -/
def hierarchy (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)
    (dummy : Nat → Nat) (key : LogicalKey) (cs : List (Nat × Nat)) (initial : Option Rec) : Result :=
  cascade key (fun c => table cfg sh tr words c.1 c.2)
    (fun c => bucket cfg c.1 c.2 (jobWord cfg words c.1 c.2 key))
    (fun i c => bucket cfg c.1 c.2 (dummy i)) cs initial 0

/-- A scalar probe before its own insertion. Blind operations select no addresses. -/
def scalar (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineRun)
    (S : Schedule) (words : Words) (dummy : Nat → Nat → Nat) (j : Nat) : Result :=
  match run.ops[j]? with
  | none => ⟨none, []⟩
  | some o => if o.probes then
      hierarchy cfg sh (Online.traceOf g run) words (dummy j) o.record.key (S j).tables
        (DirectPrefix.latest o.record.key (Online.denseRecords cfg g run S j))
    else ⟨none, []⟩

/-- Supplied records of earlier lanes in this operation, in lane order. -/
def earlier (run : OnlineBatch.BatchRun) (s : OnlineBatch.Slot) : List Rec :=
  ((((run.ops[s.op]?.map OnlineBatch.Op.lanes).getD []).take s.lane).map Prod.fst)

/-- The effective batch-lane answer after forwarding, before this lane's insertion. -/
def batch (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineBatch.BatchRun)
    (S : Schedule) (words : Words) (dummy : Nat → Nat → Nat) (t : Nat) : Result :=
  match (OnlineBatch.slots run)[t]? with
  | none => ⟨none, []⟩
  | some s => if s.probes then
      hierarchy cfg sh (OnlineBatch.traceOf g run) words (dummy t) s.record.key
        (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables
        ((DirectPrefix.latest s.record.key (earlier run s)).orElse (fun _ =>
          DirectPrefix.latest s.record.key (OnlineBatch.denseRecords cfg g run S t)))
    else ⟨none, []⟩

end RebuildBound.Model.Probe
