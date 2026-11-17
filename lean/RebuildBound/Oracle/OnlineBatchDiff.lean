import Std.Data.HashMap
import Std.Data.HashSet
import RebuildBound.Oracle.OnlineDiff
import RebuildBound.Spec.Model.OnlineBatch

/-!
# Replay of the adversary's view on the batch path (`--hierarchy`, `--online`)

The view replay of `OnlineDiff.lean` for runs that mix scalar operations with
`AccessBatch` chunks, against the trusted model `RebuildBound.Model.OnlineBatch`
(`Spec/Model/OnlineBatch.lean`; the engine facts `ENGINE_ONLINE.md` 7). The
dumper (`oracle/hierarchy_dump.cpp --view` with `--batch`) records, per slot (one
lane, inserted at one access position), the bucket the engine touched in every
hashed main of the plan its chunk probed, the real/dummy flag and the dummy
word, and per engine chunk its first slot, its lane count and its plan
(`view.chunks`, `oracle/HIERARCHY_REPLAY_SCHEMA.md` "The batch path").

From the fixture it builds the model's inputs:

* the run `BatchRun`: walking the recorded slots, a slot that starts a recorded
  chunk opens `.batch lanes` over the chunk's slots, any other slot is a scalar
  `.probe` (`.blind` for `write_np`); every lane's record is the engine's unit
  lane at its position (`OnlineDiff.opRecord`: a superseded lane, which the
  engine inserts non-real, and a lane a later operation cleared get the
  operation's key with a placeholder value, which no compared quantity reads);
  init and the unshadowed flag as in the hierarchy replay;
* `OnlineGeom` `⟨64 s, r0⟩`;
* the schedule `S`, indexed by slot: a lane reads its chunk's recorded plan, a
  scalar operation its own (an unprobed write the previous probing slot's);
  the model reads it at operations' first slots (`slotSchedule`);
* the words and the recorded dummy words (one per slot and plan entry).

Over the recorded slots of each engine it evaluates the model's `isReal` and
`touched` and compares them with the engine's real flag and bucket. It also
checks `units` (`traceOf` reproduces every captured prefix complete within the
recorded slots), `schedule` (the conjuncts of `Spec.SchedulePremises` at every
slot, `OnlineDiff.Prem*`), `plans` (families and, in the arena, table ids),
`fresh` (`BatchFresh` on this run: no `(familyOf c, key)` real-probed twice),
`sync_schedule` (the synchronous engine's plan of an operation is `syncSchedule`
at the operation's first slot), `chunks` (the recorded chunks tile the slots
the fixture's operations hand to `AccessBatch`, each chunk's lanes record the
chunk's plan, no `write_np` lane, no requester-unit crossing, and the two
engines cut the same chunks),
and `audit` (the engine's probe audit counted no violation). As in
`OnlineDiff`: the completeness checks (`recorded`, `counters` with each chunk's
lanes at `dummy_base + g · size`, the record agreement in `units`, the view
objects `viewObjects` requires: chunks and `ops[].batch` exactly when
`config.batch` is nonzero), and at a selected configuration the top's
contents are not evaluated (`top_order`).

**Efficient evaluation, equal to the trusted definitions.** The requester
state is advanced one operation at a time (`stateAt_succ`) and read at the
operation of each slot (`denseKeysWith_eq`); the duplicate test reads the
slot's operation's lanes (`duplicateWith_eq`); table membership is read from
the memoised tables' key sets on `traceWith`, which is `traceOf` by `rfl`
(`keySet_table`); `isRealWith_eq` and `touchedWith_eq` lift these to `isReal`
and `touched`. `slots`, `widths`, `slotSchedule` and `chunkStart` are the
trusted definitions, evaluated as they stand. The loops are argued, as in
`OnlineDiff`.

Core `Lean` and `Std` and the core-only model only, as every oracle module.
-/

open Lean Std

namespace RebuildBound.Oracle.OnlineBatchDiff

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online
open RebuildBound.Model.OnlineBatch
open RebuildBound.Oracle (P natField strField boolField arrField objField)
open RebuildBound.Oracle.HierarchyDiff (Replay Env Memo NativeTable coordOf period)
open RebuildBound.Oracle.OnlineDiff (NPlan NAccess NView FOp natOf arrOf pairOf parseView parseOps
  opRecord recordAgrees expectedRecorded viewObjects counterBreaks denseKeysWith isRealWith keySet
  evaluateKeys limit tilesB inCoordinates PremConsumed PremLength PremCoords PremOneTop PremTile)

abbrev MRec := RebuildBound.Model.Rec
abbrev BOp := RebuildBound.Model.OnlineBatch.Op

/-! ### The trusted definitions, evaluated efficiently -/

theorem stateAt_zero (g : OnlineGeom) (run : BatchRun) :
    OnlineBatch.stateAt g run 0 = ⟨[], []⟩ := by
  simp [OnlineBatch.stateAt, Requester.run]

/-- One more operation is one more requester step. -/
theorem stateAt_succ (g : OnlineGeom) (run : BatchRun) (j : Nat) (o : BOp)
    (h : run.ops[j]? = some o) :
    OnlineBatch.stateAt g run (j + 1) =
      Requester.step g.unitEntries (OnlineBatch.stateAt g run j) o.requester := by
  simp only [OnlineBatch.stateAt, Requester.run, List.take_add_one, h, Option.toList,
    List.map_append, List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- `traceOf` with the final requester state computed once. -/
def traceWith (g : OnlineGeom) (fin : Requester.State) (run : BatchRun) : Trace :=
  ⟨fun i => (fin.frozen.drop (i * g.unitsPerPrefix)).take g.unitsPerPrefix, run.init, run.unsh⟩

theorem traceWith_eq (g : OnlineGeom) (run : BatchRun) :
    traceWith g (OnlineBatch.stateAt g run run.ops.length) run = OnlineBatch.traceOf g run := rfl

/-- The prefix units of `traceOf` (the units check compares these). -/
theorem traceOf_units (g : OnlineGeom) (run : BatchRun) (i : Nat) :
    (OnlineBatch.traceOf g run).units i =
      ((OnlineBatch.stateAt g run run.ops.length).frozen.drop (i * g.unitsPerPrefix)).take
        g.unitsPerPrefix := rfl

/-- The dense keys a slot probes, from the requester state at its operation. -/
theorem denseKeysWith_eq (cfg : Config) (g : OnlineGeom) (run : BatchRun) (S : Schedule) {t : Nat}
    {s : Slot} (hs : (slots run)[t]? = some s) :
    denseKeysWith cfg g (slotSchedule (widths run) S t).consumed (OnlineBatch.stateAt g run s.op) =
      OnlineBatch.denseKeys cfg g run S t := by
  simp only [OnlineBatch.denseKeys, OnlineBatch.denseRecords, hs, denseKeysWith]

/-- `duplicate` on the lanes of the slot's operation. -/
def duplicateWith (lanes : List (MRec × Bool)) (lane : Nat) (key : LogicalKey) : Bool :=
  (lanes.take lane).any fun rp => rp.1.key == key

theorem duplicateWith_eq {run : BatchRun} {s : Slot} {o : BOp} (h : run.ops[s.op]? = some o) :
    duplicateWith o.lanes s.lane s.record.key = duplicate run s := by
  simp only [duplicate, h, Option.map_some, Option.getD_some, duplicateWith]

/-- `isReal` with the slot's probe bit, duplicate bit, dense membership and the
tables' membership supplied. -/
def isRealB (probes dup inDense : Bool) (tables : List (Nat × Nat)) (tk : Nat × Nat → LogicalKey → Bool)
    (key : LogicalKey) (i : Nat) : Bool :=
  probes && !dup && !inDense && (tables.take i).all fun c => !tk c key

theorem isRealB_eq {cfg : Config} {sh : Shapes} {g : OnlineGeom} {run : BatchRun} {S : Schedule}
    {words : Words} {t i : Nat} {s : Slot} {tk : Nat × Nat → LogicalKey → Bool}
    (hs : (slots run)[t]? = some s)
    (htk : ∀ c ∈ (slotSchedule (widths run) S t).tables,
      tk c s.record.key = (OnlineBatch.tableKeys cfg sh g run words c.1 c.2).contains s.record.key) :
    isRealB s.probes (duplicate run s)
        ((denseKeysWith cfg g (slotSchedule (widths run) S t).consumed
          (OnlineBatch.stateAt g run s.op)).contains s.record.key)
        (slotSchedule (widths run) S t).tables tk s.record.key i =
      OnlineBatch.isReal cfg sh g run S words t i := by
  rw [denseKeysWith_eq cfg g run S hs]
  simp only [OnlineBatch.isReal, hs, isRealB]
  congr 1
  exact OnlineDiff.all_congr_mem fun c hc => by rw [htk c (List.mem_of_mem_take hc)]

/-- `touched` with the slot's probe bit, the coordinate, the real flag and the
dummy word supplied. -/
def touchedB (cfg : Config) (words : Words) (probes : Bool) (key : LogicalKey) (c : Nat × Nat) (real : Bool)
    (dw : Nat) : Nat :=
  if probes then bucket cfg c.1 c.2 (if real then jobWord cfg words c.1 c.2 key else dw) else 0

theorem touchedB_eq {cfg : Config} {sh : Shapes} {g : OnlineGeom} {run : BatchRun} {S : Schedule}
    {words : Words} {dummy : Nat → Nat → Nat} {t i : Nat} {s : Slot} {c : Nat × Nat}
    (hs : (slots run)[t]? = some s) (hc : (slotSchedule (widths run) S t).tables[i]? = some c) :
    touchedB cfg words s.probes s.record.key c (OnlineBatch.isReal cfg sh g run S words t i)
        (dummy t i) =
      OnlineBatch.touched cfg sh g run S words dummy t i := by
  simp only [OnlineBatch.touched, hs, hc, touchedB]

/-- A key set of a memo table (`Env.evalTable_sound`) on the trace `traceOf`
answers `tableKeys`' membership. -/
theorem keySet_table {e : Env} {g : OnlineGeom} {run : BatchRun}
    (htr : e.tr = OnlineBatch.traceOf g run) {ℓ v : Nat} {o : Output}
    (ho : o = table e.cfg e.sh e.tr e.words ℓ v) (k : LogicalKey) :
    (keySet o).contains k = (OnlineBatch.tableKeys e.cfg e.sh g run e.words ℓ v).contains k := by
  subst ho
  rw [keySet, HashSet.contains_ofList, htr]
  rfl

/-! ### The fixture's chunks -/

/-- A recorded engine chunk: slots `[first, first + lanes)`, its plan, its
first dummy counter and the harness's `AccessBatch` number. -/
structure NChunk where
  first : Nat
  lanes : Nat
  plan : Nat
  base : Nat
  call : Nat
  deriving BEq

def parseChunks (eng : String) (j : Json) : P (Array NChunk) := do
  match j.getObjVal? "chunks" with
  | .error _ => return #[]
  | .ok Json.null => return #[]
  | .ok a =>
    (← arrOf s!"view.{eng}.chunks" a).mapM fun x => do
      let ctx := s!"view.{eng}.chunks"
      match (← arrOf ctx x).toList with
      | [f, m, p, b, c] =>
        return { first := ← natOf ctx f, lanes := ← natOf ctx m, plan := ← natOf ctx p,
                 base := ← natOf ctx b, call := ← natOf ctx c }
      | _ => throw s!"{ctx}: expected [first, lanes, plan, dummy_base, call]"

/-- The fixture's `AccessBatch` number of every operation (`ops[].batch`). -/
def parseCalls (fixture : Json) : P (Array (Option Nat)) := do
  (← arrField fixture "fixture" "ops").mapM fun x =>
    return (x.getObjValAs? Nat "batch").toOption

/-- The recorded chunks are sorted, disjoint, nonempty and within `n` slots. -/
def chunksWellFormed (cs : Array NChunk) (n : Nat) : Bool := Id.run do
  let mut at_ := 0
  for c in cs do
    if c.first < at_ || c.lanes == 0 || c.first + c.lanes > n then return false
    at_ := c.first + c.lanes
  return true

/-- The run of `n` slots: a recorded chunk is one `.batch` operation over its
slots, any other slot a scalar operation. Also the number of lanes whose record
was not observed, and of observed lanes holding another key. -/
def buildRun (rp : Replay) (fops : Array FOp) (cs : Array NChunk) (n : Nat) :
    Array BOp × Nat × Nat := Id.run do
  let E := 64 * rp.stashBuckets
  let r0 := rp.prefixFlushes
  let seed1 := rp.cfg.seed 1
  let starts : HashMap Nat Nat := cs.foldl (fun m c => m.insert c.first c.lanes) {}
  let mut ops : Array BOp := #[]
  let mut unobserved := 0
  let mut keyBad := 0
  let mut t := 0
  while t < n do
    match starts[t]? with
    | some m =>
      let mut lanes : Array MRec := #[]
      for l in [0:m] do
        let fo := fops[t + l]!
        let (r, seen) := opRecord rp E r0 seed1 (t + l) fo
        if !seen then unobserved := unobserved + 1
        if seen && !recordAgrees rp.valueBytes fo r then keyBad := keyBad + 1
        lanes := lanes.push r
      ops := ops.push (.batch lanes.toList)
      t := t + m
    | none =>
      let fo := fops[t]!
      let (r, seen) := opRecord rp E r0 seed1 t fo
      if !seen then unobserved := unobserved + 1
      if seen && !recordAgrees rp.valueBytes fo r then keyBad := keyBad + 1
      ops := ops.push (if fo.kind == "write_np" then .blind r else .probe r)
      t := t + 1
  return (ops, unobserved, keyBad)

/-! ### The comparison -/

/-- The schedule by slot: slot `t` reads plan `idx[t]`. -/
def scheduleOf (plans : Array NPlan) (idx : Array Nat) : Schedule := fun t =>
  match idx[t]? with
  | some p => match plans[p]? with
    | some q => ⟨q.consumed, q.tables⟩
    | none => ⟨0, []⟩
  | none => ⟨0, []⟩

/-- Each slot's plan index: its own record's; an unprobed write the previous
probing slot's (leading ones: the first probing slot's). -/
def planIndex (v : NView) : Array Nat := OnlineDiff.planIndex v

structure Acc where
  probing : Nat := 0
  entries : Nat := 0
  real : Nat := 0
  engineReal : Nat := 0
  bucketMismatches : Nat := 0
  realMismatches : Nat := 0
  kindMismatches : Nat := 0
  shown : Array Json := #[]
  freshDup : Nat := 0
  freshShown : Array Json := #[]
  outsideCoords : Nat := 0
  keysPastN : Nat := 0
  wordsMissing : Nat := 0
  duplicates : Nat := 0
  chunkLanes : Nat := 0
  topEntries : Nat := 0
  topNotLast : Nat := 0

def Acc.show (a : Acc) (j : Json) : Acc :=
  if a.shown.size < limit then { a with shown := a.shown.push j } else a

/-- The checks of one engine's view on the run. -/
def checkView (rp : Replay) (e : Env) (g : OnlineGeom) (run : BatchRun) (opsArr : Array BOp)
    (slotsArr : Array Slot) (ks : HashMap (Nat × Nat) (HashSet LogicalKey)) (v : NView)
    (cs : Array NChunk) (chunkProblems : List Json) (N : Nat) (sync : Bool) (skipTop : Bool) :
    List String × Json := Id.run do
  let cfg := e.cfg
  let n := v.accesses.size
  let idx := planIndex v
  let S := scheduleOf v.plans idx
  let ws := widths run
  let tk : Nat × Nat → LogicalKey → Bool := fun c k => match ks[c]? with
    | some s => s.contains k
    | none => false
  let mut acc : Acc := {}
  let mut seen : HashSet ((Nat × Nat) × LogicalKey) := {}
  let mut st : Requester.State := ⟨[], []⟩  -- `stateAt g run 0` (`stateAt_zero`)
  let mut cur := 0                          -- `st = stateAt g run cur`
  for h : t in [0:n] do
    let some s := slotsArr[t]? | break      -- `(slots run)[t]?`
    -- `stateAt g run s.op` (`stateAt_succ`)
    while cur < s.op do
      match opsArr[cur]? with
      | some o => st := Requester.step g.unitEntries st o.requester
      | none => pure ()
      cur := cur + 1
    let q := slotSchedule ws S t
    let key := s.record.key
    -- `duplicateWith_eq`, `denseKeysWith_eq`
    let dup := duplicateWith ((opsArr[s.op]?.map Op.lanes).getD []) s.lane key
    let inDense := (denseKeysWith cfg g q.consumed st).contains key
    if dup then acc := { acc with duplicates := acc.duplicates + 1 }
    match v.accesses[t] with
    | none =>
      if s.probes then
        acc := { acc with kindMismatches := acc.kindMismatches + 1 }
        acc := acc.show (Json.mkObj [("slot", toJson t), ("problem", "probing slot without a record")])
    | some a =>
      if !s.probes then
        acc := { acc with kindMismatches := acc.kindMismatches + 1 }
        acc := acc.show (Json.mkObj [("slot", toJson t), ("problem", "unprobed write with a record")])
      acc := { acc with probing := acc.probing + 1 }
      if q.tables.length != a.touched.size then
        acc := { acc with bucketMismatches := acc.bucketMismatches + 1 }
        acc := acc.show (Json.mkObj [("slot", toJson t), ("problem", "the record's length is not its plan's"),
          ("plan_tables", toJson q.tables.length), ("recorded", toJson a.touched.size)])
      let mut i := 0
      for c in q.tables do
        -- the top's contents are not evaluated at a selected configuration:
        -- the entries after a top entry would read them (`tables.take i`)
        if c.1 == cfg.levels then
          acc := { acc with topEntries := acc.topEntries + 1 }
          if skipTop && i + 1 != q.tables.length then acc := { acc with topNotLast := acc.topNotLast + 1 }
        -- `isRealB_eq`, `touchedB_eq`: these are `isReal` and `touched`
        let real := isRealB s.probes dup inDense q.tables tk key i
        let b := touchedB cfg e.words s.probes key c real (a.dummy.getD i 0)
        let nb := a.touched.getD i 0
        let nr := a.real.getD i false
        acc := { acc with entries := acc.entries + 1, real := acc.real + (if real then 1 else 0),
                          engineReal := acc.engineReal + (if nr then 1 else 0) }
        if b != nb || real != nr then
          acc := { acc with bucketMismatches := acc.bucketMismatches + (if b != nb then 1 else 0),
                            realMismatches := acc.realMismatches + (if real != nr then 1 else 0) }
          acc := acc.show (Json.mkObj [("slot", toJson t), ("op", toJson s.op), ("lane", toJson s.lane),
            ("entry", toJson i), ("table", toJson [c.1, c.2]), ("key", toJson (LogicalKey.toNat key)),
            ("model", Json.mkObj [("bucket", toJson b), ("real", toJson real)]),
            ("engine", Json.mkObj [("bucket", toJson nb), ("real", toJson nr)]),
            ("duplicate", toJson dup), ("in_dense", toJson inDense), ("consumed", toJson q.consumed)])
        if real then
          let f := familyOf cfg c.1 c.2
          if !((rp.words.get? f).map (·.contains (LogicalKey.toNat key))).getD false then
            acc := { acc with wordsMissing := acc.wordsMissing + 1 }
          if !inCoordinates cfg f then acc := { acc with outsideCoords := acc.outsideCoords + 1 }
          if LogicalKey.toNat key ≥ N then acc := { acc with keysPastN := acc.keysPastN + 1 }
          if seen.contains (f, key) then
            acc := { acc with freshDup := acc.freshDup + 1 }
            if acc.freshShown.size < limit then
              acc := { acc with freshShown := acc.freshShown.push (Json.mkObj [("slot", toJson t),
                ("entry", toJson i), ("family", toJson [f.1, f.2]), ("key", toJson (LogicalKey.toNat key))]) }
          seen := seen.insert (f, key)
        i := i + 1
  -- the schedule's premises over the recorded slots (`S` indexed by slot)
  let m := v.plans.foldl (fun x p => max x p.tables.length) 0
  let pc := decide (PremConsumed cfg S n)
  let pl := decide (PremLength S n m)
  let pco := decide (PremCoords cfg S n)
  let pt := decide (PremOneTop cfg S n)
  let pti := decide (PremTile cfg S n)
  let mut firstBad : Option Json := none
  for h : t in [0:n] do
    let q := S t
    let bad : List String :=
      (if decide (cfg.seed 1 ≤ q.consumed ∧ q.consumed * cfg.carryPositions 1 ≤ pos cfg t) then []
        else ["consumed"]) ++
      (if decide (∀ c ∈ q.tables, 1 ≤ c.1 ∧ c.1 ≤ cfg.levels ∧ (c.1 < cfg.levels → cfg.seed c.1 < c.2) ∧
          (c.1 = cfg.levels → cfg.seed c.1 ≤ c.2)) then [] else ["coords"]) ++
      (if (q.tables.filter (·.1 == cfg.levels)).length ≤ 1 then [] else ["one_top"]) ++
      (if tilesB cfg q.tables 0 (q.consumed * cfg.carryPositions 1) then [] else ["tile"])
    if !bad.isEmpty then
      firstBad := some (Json.mkObj [("slot", toJson t), ("failed", toJson bad), ("consumed", toJson q.consumed),
        ("tables", toJson (q.tables.map fun c => [c.1, c.2])),
        ("windows", toJson (q.tables.map fun c => [(window cfg c.1 c.2).1, (window cfg c.1 c.2).2]))])
      break
  let schedOk := pc && pl && pco && pt && pti
  -- plan identities
  let byId : HashMap Nat NativeTable := rp.tables.foldl (fun mp t => mp.insert t.id t) {}
  let mut famBad := 0
  let mut idBad := 0
  let mut identShown : Array Json := #[]
  for p in v.plans do
    for ((c, f), id) in (p.tables.zip p.families).zip p.ids do
      if familyOf cfg c.1 c.2 != f then
        famBad := famBad + 1
        if identShown.size < limit then
          identShown := identShown.push (Json.mkObj [("table", toJson [c.1, c.2]),
            ("engine_family", toJson [f.1, f.2]),
            ("model_family", toJson [(familyOf cfg c.1 c.2).1, (familyOf cfg c.1 c.2).2])])
      if !sync then
        match byId[id]? with
        | some t =>
          if coordOf cfg t != c then
            idBad := idBad + 1
            if identShown.size < limit then
              identShown := identShown.push (Json.mkObj [("id", toJson id), ("plan", toJson [c.1, c.2]),
                ("recorded", toJson [(coordOf cfg t).1, (coordOf cfg t).2])])
        | none => idBad := idBad + 1
  -- the synchronous mode's schedule, at every probing operation's first slot
  let mut syncCmp := 0
  let mut syncDiff := 0
  let mut syncShown : Array Json := #[]
  if sync then
    for h : t in [0:n] do
      if v.accesses[t].isNone then continue
      let t0 := chunkStart ws t
      if t0 != t then continue
      syncCmp := syncCmp + 1
      let q := slotSchedule ws S t
      let s := syncSchedule cfg t0
      if q.consumed != s.consumed || q.tables != s.tables then
        syncDiff := syncDiff + 1
        if syncShown.size < limit then
          syncShown := syncShown.push (Json.mkObj [("slot", toJson t),
            ("engine", Json.mkObj [("consumed", toJson q.consumed),
              ("tables", toJson (q.tables.map fun c => [c.1, c.2]))]),
            ("sync_schedule", Json.mkObj [("consumed", toJson s.consumed),
              ("tables", toJson (s.tables.map fun c => [c.1, c.2]))])])
  -- one plan per chunk: every lane records its chunk's plan
  let mut chunkBad : Array Json := chunkProblems.toArray
  let mut lanes := 0
  for c in cs do
    if c.first + c.lanes > n then break
    lanes := lanes + c.lanes
    for l in [0:c.lanes] do
      match v.accesses[c.first + l]? with
      | some (some a) =>
        if a.plan != c.plan then
          chunkBad := chunkBad.push (Json.mkObj [("slot", toJson (c.first + l)),
            ("problem", "a lane records another plan than its chunk")])
      | _ =>
        chunkBad := chunkBad.push (Json.mkObj [("slot", toJson (c.first + l)),
          ("problem", "a chunk lane without a record")])
  -- completeness: every completed operation recorded, the counters one chain
  let expected := expectedRecorded rp sync
  let recordedOk := n == expected && v.recorded == n
  let breaks := counterBreaks v (cs.map fun c => (c.first, c.lanes, c.plan, c.base))
  let pfx := if sync then "online.sync." else "online.arena."
  let failures :=
    (if recordedOk then [] else [pfx ++ "recorded"]) ++
    (if breaks == 0 then [] else [pfx ++ "counters"]) ++
    (if acc.topNotLast == 0 then [] else [pfx ++ "top_order"]) ++
    (if acc.bucketMismatches == 0 then [] else [pfx ++ "view"]) ++
    (if acc.realMismatches == 0 then [] else [pfx ++ "real"]) ++
    (if acc.kindMismatches == 0 then [] else [pfx ++ "kinds"]) ++
    (if schedOk then [] else [pfx ++ "schedule"]) ++
    (if famBad == 0 && idBad == 0 then [] else [pfx ++ "plans"]) ++
    (if acc.freshDup == 0 then [] else [pfx ++ "fresh"]) ++
    (if acc.wordsMissing == 0 then [] else [pfx ++ "words"]) ++
    (if syncDiff == 0 then [] else [pfx ++ "sync_schedule"]) ++
    (if chunkBad.isEmpty then [] else [pfx ++ "chunks"]) ++
    (if v.auditViolations == 0 then [] else [pfx ++ "audit"])
  let pf (b : Bool) : Json := toJson (if b then "pass" else "fail")
  let json := Json.mkObj ([
    ("engine", toJson v.engine), ("drive", toJson v.drive),
    ("recorded", Json.mkObj [("result", pf recordedOk), ("records", toJson n), ("expected", toJson expected),
      ("dumper_recorded", toJson v.recorded)]),
    ("counters", Json.mkObj [("result", pf (breaks == 0)), ("breaks", toJson breaks)]),
    ("top_entries", toJson acc.topEntries),
    ("top_contents", toJson (if skipTop then "not evaluated: every top entry is its plan's last, so no compared quantity reads it"
      else "evaluated")),
    ("accesses", toJson n), ("probing", toJson acc.probing), ("entries", toJson acc.entries),
    ("chunks", toJson (cs.filter (fun c => c.first + c.lanes ≤ n)).size), ("chunk_lanes", toJson lanes),
    ("duplicate_lanes", toJson acc.duplicates),
    ("plans", toJson v.plans.size), ("max_tables", toJson m),
    ("real", toJson acc.real), ("dummy", toJson (acc.entries - acc.real)), ("engine_real", toJson acc.engineReal),
    ("bucket_mismatches", toJson acc.bucketMismatches), ("real_mismatches", toJson acc.realMismatches),
    ("kind_mismatches", toJson acc.kindMismatches), ("first_mismatches", toJson acc.shown),
    ("schedule_premises", Json.mkObj [("consumed", pf pc), ("length", pf pl), ("coords", pf pco),
      ("one_top", pf pt), ("tile", pf pti), ("m", toJson m), ("first", toJson firstBad),
      ("result", pf schedOk)]),
    ("plan_ident", Json.mkObj [("family_mismatches", toJson famBad), ("id_mismatches", toJson idBad),
      ("ids_checked", toJson (!sync)), ("first", toJson identShown)]),
    ("fresh", Json.mkObj [("real_probes", toJson acc.real), ("distinct", toJson seen.size),
      ("duplicates", toJson acc.freshDup), ("first", toJson acc.freshShown),
      ("outside_coordinates", toJson acc.outsideCoords), ("keys_past_N", toJson acc.keysPastN),
      ("result", pf (acc.freshDup == 0))]),
    ("chunk_check", Json.mkObj [("problems", toJson chunkBad.size),
      ("first", toJson (chunkBad.extract 0 limit)), ("result", pf chunkBad.isEmpty)]),
    ("words_missing", toJson acc.wordsMissing),
    ("audit_violations", toJson v.auditViolations)] ++
    (if sync then [("sync_schedule", Json.mkObj [("compared", toJson syncCmp), ("differ", toJson syncDiff),
      ("first", toJson syncShown), ("result", pf (syncDiff == 0))])] else []))
  return (failures, json)

/-- The chunks against the fixture's operations: a slot is in a recorded chunk
iff its operation went to `AccessBatch` (`ops[].batch`), a chunk's operations
are one call's, no chunk lane is a `write_np`, and every chunk fits the
remaining requester-unit positions. The seeded prefix count is unit-aligned. -/
def chunkProblemsOf (unitEntries : Nat) (fops : Array FOp) (calls : Array (Option Nat))
    (cs : Array NChunk) (n : Nat) : List Json := Id.run do
  let mut inChunk : Array (Option Nat) := Array.replicate n none
  let mut out : Array Json := #[]
  for c in cs do
    if c.first % unitEntries + c.lanes > unitEntries then
      out := out.push (Json.mkObj [("slot", toJson c.first),
        ("problem", "a chunk crosses a requester-unit boundary")])
    for l in [0:c.lanes] do
      let t := c.first + l
      if t < n then inChunk := inChunk.set! t (some c.call)
  for t in [0:n] do
    let call := (calls[t]?).getD none
    match inChunk[t]!, call with
    | some c, some c' =>
      if c != c' then out := out.push (Json.mkObj [("slot", toJson t), ("problem", "chunk call differs")])
      if (fops[t]?.map (·.kind)) == some "write_np" then
        out := out.push (Json.mkObj [("slot", toJson t), ("problem", "a write_np lane")])
    | some _, none => out := out.push (Json.mkObj [("slot", toJson t), ("problem", "a scalar op in a chunk")])
    | none, some _ => out := out.push (Json.mkObj [("slot", toJson t), ("problem", "a batch op outside the chunks")])
    | none, none => pure ()
  return out.toList

/-- Whether a fixture's view is a batch view (the dumper ran with `--batch`). -/
def isBatchView (fixture : Json) : Bool :=
  match fixture.getObjVal? "config" with
  | .ok c => ((c.getObjValAs? Nat "batch").toOption.getD 0) != 0
  | .error _ => false

/-- The batch checks of a parsed fixture with a `view`; `none` without one.
On a scalar view (no chunks) this is the scalar replay through the batch
model (`BatchScalar`). -/
def check (rp : Replay) (fixture : Json) : P (Option (List String × Json)) := do
  let some (arenaJ, syncJ) ← viewObjects rp fixture | return none
  let parseOne (eng : String) (x : Json) : P (NView × Array NChunk) := do
    return (← parseView x, ← parseChunks eng x)
  let arenaV ← some <$> parseOne "arena" arenaJ
  let syncV ← syncJ.mapM (parseOne "sync")
  -- at a selected configuration the top is not evaluated (`skipTop`)
  let skipTop := rp.selected.isSome
  let fops ← parseOps fixture
  let calls ← parseCalls fixture
  let cfg := rp.cfg
  let g : OnlineGeom := ⟨64 * rp.stashBuckets, rp.prefixFlushes⟩
  let seed1 := cfg.seed 1
  let views := (arenaV.toList.map (·, false)) ++ (syncV.toList.map (·, true))
  for ((v, cs), _) in views do
    if !chunksWellFormed cs v.accesses.size then throw "view.chunks: not sorted, disjoint and within the record"
  -- the run: the slots every recorded view covers, cut by the longest record's chunks
  let n := views.foldl (fun x ((v, _), _) => max x v.accesses.size) 0
  if n > rp.accesses || n > fops.size then throw "view: more recorded slots than completed operations"
  let primary := (views.find? fun ((v, _), _) => v.accesses.size == n).map (·.1.2) |>.getD #[]
  let (opsArr, unobserved, keyBad) := buildRun rp fops primary n
  let run : BatchRun := ⟨opsArr.toList, rp.init, HierarchyDiff.unshOf rp.valueBytes⟩
  let slotsArr := (slots run).toArray
  if slotsArr.size != n then throw s!"internal: {slotsArr.size} slots for {n} recorded"
  let fin := OnlineBatch.stateAt g run run.ops.length
  let e : Env := { rp.env with tr := traceWith g fin run }  -- `traceOf g run` (`traceWith_eq`)
  -- units: `traceOf` reproduces every captured prefix complete within the run
  let P1 := cfg.carryPositions 1
  let mut unitOrds := 0
  let mut unitBad := 0
  let mut unitShown : Array Json := #[]
  for (o, us) in rp.units.toList do
    if o ≤ seed1 then continue
    if (o - seed1) * P1 > n then continue
    unitOrds := unitOrds + 1
    if e.tr.units (o - seed1 - 1) != us then
      unitBad := unitBad + 1
      if unitShown.size < limit then unitShown := unitShown.push (toJson o)
  if keyBad > 0 then unitBad := unitBad + keyBad
  -- the key sets of every planned coordinate
  let mut need : HashSet (Nat × Nat) := {}
  for ((v, _), _) in views do
    for p in v.plans do
      for c in p.tables do
        if c.1 < 1 || c.1 > cfg.levels then throw s!"view: plan coordinate {c} is not a level's"
        if !(skipTop && c.1 == cfg.levels) then need := need.insert c
  let needL := need.toList
  let tEnd := needL.foldl (fun t c => if e.IsBase c.1 c.2 then t else max t (c.2 * period cfg c.1)) seed1
  let ks ← match evaluateKeys e needL tEnd (if skipTop then cfg.levels - 1 else cfg.levels) with
    | .ok ks => pure ks
    | .error err => throw err
  for c in needL do
    if !ks.contains c then throw s!"internal: no key set for {c}"
  let N ← match rp.keyBound <|> rp.addressSpace with
    | some n => pure n
    | none => throw "config.key_bound / config.address_space: missing"
  let mut failures : List String := if unitBad == 0 then [] else ["online.units"]
  let mut parts : List (String × Json) := []
  for ((v, cs), sync) in views do
    let nv := v.accesses.size
    -- the engines cut the same chunks: this view's are the run's within its record
    -- (plan indices and dummy bases are per engine)
    let cut (a : Array NChunk) := a.map fun c => (c.first, c.lanes, c.call)
    let mine := primary.filter fun c => c.first + c.lanes ≤ nv
    let probs := chunkProblemsOf g.unitEntries fops calls cs nv ++
      (if cut cs == cut mine then [] else [Json.mkObj [("problem", "the engines' chunks differ")]])
    let (f, j) := checkView rp e g run opsArr slotsArr ks v cs probs N sync skipTop
    failures := failures ++ f
    parts := parts ++ [(if sync then "sync" else "arena", j)]
  let nChunks := opsArr.foldl (fun x o => match o with | .batch _ => x + 1 | _ => x) 0
  let json := Json.mkObj ([
    ("model", toJson "OnlineBatch"),
    ("operations", toJson opsArr.size), ("slots", toJson n), ("chunks", toJson nChunks),
    ("records_unobserved", toJson unobserved),
    ("units", Json.mkObj [("ordinals", toJson unitOrds), ("mismatches", toJson unitBad),
      ("first", toJson unitShown), ("result", toJson (if unitBad == 0 then "pass" else "fail"))]),
    ("tables_evaluated_to", toJson tEnd), ("coordinates", toJson needL.length),
    ("top_evaluated", toJson !skipTop)] ++ parts ++
    [("failures", toJson failures), ("result", toJson (if failures.isEmpty then "pass" else "fail"))])
  return some (failures, json)

/-- `--hierarchy` on a fixture with a view: the hierarchy replay's line with an
`online` object (the batch model's on a batch view, the scalar model's
otherwise) and, on a scalar view, an `online_batch` object (the same view
through the batch model, `BatchScalar`; its failures named `online_batch.*`),
their failures added to `failures`. -/
def runCombined (path text : String) : P (Json × UInt32) := do
  let fixture ← Json.parse text
  let (out, code) ← HierarchyDiff.runJson path fixture
  let rp ← HierarchyDiff.parseReplayJson fixture
  let batch := isBatchView fixture
  let primary ← if batch then check rp fixture else OnlineDiff.check rp fixture
  match primary with
  | none => return (out, code)
  | some (failures, oj) =>
    let prev := match out.getObjValAs? (List String) "failures" with
      | .ok l => l
      | .error _ => []
    let mut all := prev ++ failures
    let mut out := out.setObjVal! "online" oj
    if !batch then
      if let some (bf, bj) ← check rp fixture then
        let bf := bf.map fun r => "online_batch." ++ (r.drop "online.".length).toString
        all := all ++ bf
        out := out.setObjVal! "online_batch" bj
    out := out.setObjVal! "failures" (toJson all)
      |>.setObjVal! "result" (toJson (if all.isEmpty then "pass" else "fail"))
    return (out, if all.isEmpty then 0 else 1)

/-- `--online`: the view checks alone (the batch model on a batch view). -/
def runOnline (path text : String) : P (Json × UInt32) := do
  let fixture ← Json.parse text
  let rp ← HierarchyDiff.parseReplayJson fixture
  let r ← if isBatchView fixture then check rp fixture else OnlineDiff.check rp fixture
  match r with
  | none => throw "view: the fixture has no view (hierarchy_dump --view)"
  | some (failures, oj) =>
    let out := Json.mkObj [("file", toJson path), ("mode", "online"), ("online", oj),
      ("failures", toJson failures), ("result", toJson (if failures.isEmpty then "pass" else "fail"))]
    return (out, if failures.isEmpty then 0 else 1)

end RebuildBound.Oracle.OnlineBatchDiff
