import RebuildBound.Spec.Model.Online

/-!
# The batch path and the adversary's view (trusted model)

The online layer of `Spec/Model/Online.lean` extended to runs that mix scalar
operations with chunks of `AccessBatch` (`ENGINE_ONLINE.md` section 7). On a run without chunks it is the
scalar model (`BatchScalar`).

**Operations.** A scalar operation is one lane, as before. A chunk (the
engine cuts a batch into chunks of `MaxCombinedBatchLanes()` lanes, a public
size) is a list of lanes in request order, each with the record the
forwarding chain gives it; every lane of a lowered chunk probes. The current
public batch API splits at output-free Write lanes, emitting scalar blind
operations between probed chunks. ReadThenWrite always remains probed.
The requester steps are
`Requester.Op.access` and `Requester.Op.batch`: a chunk removes every lane's
key from the current unit, then inserts its lanes in order, a lane whose key
a later lane repeats non-real.

**Slots.** Every lane is inserted at one access position, so the run's lanes
in insertion order are its slots, slot `t` at position `pos cfg t`. The view,
the schedule and the dummy tape are indexed by slot.

**Plans.** A chunk probes one plan: slot `t` reads the schedule at the first
slot of its operation (`chunkStart`). The schedule's premises are the scalar
ones (`Spec.SchedulePremises`, per slot); the model reads the schedule only at
operation starts. The synchronous mode's batch schedule is `syncSchedule`.

**Real or dummy.** A lane gets the real bucket when it probes, no earlier
lane of its chunk has its key (the engine's duplicate lanes start the cascade
with `found` set), and no earlier entry of the plan holds its key. The dense
prefix is the requester's state at the chunk's start: a chunk's inserts come
after its probes. The dummy word is one word per slot and plan entry (lane
`l` of a chunk uses the counters `base + l · size + i`).

**View.** For every slot and plan entry, the bucket touched; zero where there
is none. The public shape of a run is each operation's lane count (`widths`)
and which slots probe; the simulator reads it and the schedule only.
-/

namespace RebuildBound.Model.OnlineBatch

open Hierarchy Online

/-- An operation of a run with batch chunks. -/
inductive Op where
  /-- A scalar Read, ReadThenWrite, Erase or Exchange primitive: probe then insert. -/
  | probe (r : Rec)
  /-- A blind upsert (`Write` or its `WriteWithoutProbe` alias): insert alone. -/
  | blind (r : Rec)
  /-- One chunk: its lanes in request order, each with the record the
  forwarding chain gives it. Every lane probes. -/
  | batch (lanes : List Rec)

/-- The lanes of an operation, each its record and whether it probes. A
scalar operation is one lane. -/
def Op.lanes : Op → List (Rec × Bool)
  | .probe r => [(r, true)]
  | .blind r => [(r, false)]
  | .batch lanes => lanes.map fun r => (r, true)

/-- The operation's requester step. -/
def Op.requester : Op → Requester.Op
  | .probe r => .access r true
  | .blind r => .access r true
  | .batch lanes => .batch lanes

/-- The fixed logical input of a run. -/
structure BatchRun where
  ops : List Op
  init : List Rec
  unsh : Rec → Bool

/-- One slot: one lane, inserted at one access position. Inside
`namespace RebuildBound.Spec` the bare name `Slot` is `Spec.Slot`
(`Spec/Prob/Tests.lean`), not this structure; Spec statements write
`OnlineBatch.Slot` or use `slots`. -/
structure Slot where
  /-- The index of the lane's operation in the run. -/
  op : Nat
  /-- The lane's index in its operation. -/
  lane : Nat
  record : Rec
  probes : Bool

/-- The slots of a run in insertion order. -/
def slots (run : BatchRun) : List Slot :=
  run.ops.zipIdx.flatMap fun oj =>
    oj.1.lanes.zipIdx.map fun rl => ⟨oj.2, rl.2, rl.1.1, rl.1.2⟩

/-- The public shape of a run: each operation's lane count. -/
def widths (run : BatchRun) : List Nat := run.ops.map fun o => o.lanes.length

/-- The first slot of the operation that holds slot `t`, for operations of
widths `ws`; `t` itself past the last operation. -/
def chunkStart : List Nat → Nat → Nat
  | [], t => t
  | w :: ws, t => if t < w then 0 else w + chunkStart ws (t - w)

/-- The plan of every slot: the schedule at its operation's first slot. -/
def slotSchedule (ws : List Nat) (S : Schedule) : Schedule := fun t => S (chunkStart ws t)

/-- Whether a slot probes: the public operation kinds. -/
def probePattern (run : BatchRun) (t : Nat) : Bool := ((slots run)[t]?.map Slot.probes).getD false

/-- The requester state after the first `j` operations, from a fresh ring. -/
def stateAt (g : OnlineGeom) (run : BatchRun) (j : Nat) : Requester.State :=
  Requester.run g.unitEntries ⟨[], []⟩ ((run.ops.take j).map Op.requester)

/-- The logical trace of a run, as in the scalar model. -/
def traceOf (g : OnlineGeom) (run : BatchRun) : Trace :=
  ⟨fun i => ((stateAt g run run.ops.length).frozen.drop (i * g.unitsPerPrefix)).take
      g.unitsPerPrefix, run.init, run.unsh⟩

/-- The dense records, in chronological order, that slot `t` probes: the requester's state
at the start of its operation, every unit from the first unconsumed ordinal
of its plan on, and the current unit. -/
def denseRecords (cfg : Config) (g : OnlineGeom) (run : BatchRun) (S : Schedule) (t : Nat) : List Rec :=
  match (slots run)[t]? with
  | none => []
  | some s =>
    let st := stateAt g run s.op
    (st.frozen.drop (((slotSchedule (widths run) S t).consumed - cfg.seed 1) *
        g.unitsPerPrefix)).flatMap Bucket.recs ++ st.current.recs

/-- The keys of the chunk-start dense prefix, including tombstones. -/
def denseKeys (cfg : Config) (g : OnlineGeom) (run : BatchRun) (S : Schedule) (t : Nat) : List LogicalKey :=
  (denseRecords cfg g run S t).map Rec.key

/-- Whether a lane repeats the key of an earlier lane of its operation. -/
def duplicate (run : BatchRun) (s : Slot) : Bool :=
  (((run.ops[s.op]?.map Op.lanes).getD []).take s.lane).any fun rp => rp.1.key == s.record.key

/-- The keys of the table `(ℓ, v)` of the run (main and tier, tombstones
included). -/
def tableKeys (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun) (words : Words)
    (ℓ v : Nat) : List LogicalKey :=
  (table cfg sh (traceOf g run) words ℓ v).records.map Rec.key

/-- Whether entry `i` of slot `t`'s plan gets the real bucket: the lane
probes, is not a duplicate, and no earlier entry (the dense prefix, an earlier
table's main or tier) holds its key. -/
def isReal (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun) (S : Schedule)
    (words : Words) (t i : Nat) : Bool :=
  match (slots run)[t]? with
  | none => false
  | some s =>
    s.probes && !duplicate run s && !(denseKeys cfg g run S t).contains s.record.key &&
      ((slotSchedule (widths run) S t).tables.take i).all fun c =>
        !(tableKeys cfg sh g run words c.1 c.2).contains s.record.key

/-- The bucket touched in entry `i` of slot `t`'s plan, with `dummy t i` the
entry's dummy word; zero where nothing is touched (an unprobed write, or past
the plan's length). -/
def touched (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun) (S : Schedule)
    (words : Words) (dummy : Nat → Nat → Nat) (t i : Nat) : Nat :=
  match (slots run)[t]?, (slotSchedule (widths run) S t).tables[i]? with
  | some s, some c =>
    if s.probes then
      bucket cfg c.1 c.2
        (if isReal cfg sh g run S words t i then jobWord cfg words c.1 c.2 s.record.key
          else dummy t i)
    else 0
  | _, _ => 0

/-- The adversary's view of the first `n` slots with plans of at most `m`
hashed tables. -/
def view (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun) (S : Schedule) (n m : Nat)
    (words : Words) (dummy : Nat → Nat → Nat) : Fin n → Fin m → Nat :=
  fun t i => touched cfg sh g run S words dummy t i

/-- A scalar operation as an operation of a run with batch chunks. -/
def Op.ofScalar : Online.Op → Op
  | .probe r => .probe r
  | .blind r => .blind r

/-- A scalar run as a run without chunks. -/
def ofScalar (run : OnlineRun) : BatchRun := ⟨run.ops.map Op.ofScalar, run.init, run.unsh⟩

end RebuildBound.Model.OnlineBatch
