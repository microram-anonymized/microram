import Std.Data.HashMap
import Std.Data.HashSet
import RebuildBound.Oracle.HierarchyDiff
import RebuildBound.Spec.Model.Online

/-!
# Replay of the adversary's view (`--hierarchy` with a `view`, `--online`)

Reads the `view` object of a `hierarchy-replay/0` fixture
(`oracle/HIERARCHY_REPLAY_SCHEMA.md`, "The adversary's view", written by
`oracle/hierarchy_dump.cpp --view`): for every scalar access of the real engine,
the probe plan's hashed tables in cascade order (coordinates, table ids,
families, the consumed-prefix count), the bucket the engine touched in each,
whether that probe was real, and the dummy word (the AES tag of the engine's
dummy counter under the family's dummy nonce), for the arena engine and, with
`--sync-check`, for the synchronous engine. It rebuilds from the fixture the
inputs of the trusted online model `RebuildBound.Model.Online`:

* the run `OnlineRun`: operation `j` is `.blind` for `write_np` and `.probe`
  otherwise, inserting the record the engine stored at its position (unit
  `j / 64 s`, lane `j mod 64 s` of the captured units); a position whose lane is
  empty (a later operation of the unit cleared it) or whose prefix was not
  captured gets a record with the operation's key and a placeholder value, which
  no compared quantity reads (it is cleared from its unit, or lies in a prefix
  no evaluated table consumes); the initialization's input and the unshadowed
  flag (meta bit `0x20`) as in the hierarchy replay;
* `OnlineGeom` `⟨64 s, r0⟩`;
* the schedule: the engine's recorded plans (an unprobed write, which composes no
  plan, gets the previous probing access's plan; leading ones the next one's);
* the words: the fixture's word matrix; the dummy words: the recorded ones;

and compares the model's `touched` and `isReal` with the engine's bucket and
real flag at every access and plan entry. It also checks:

* `units`: `traceOf` of the reconstructed run reproduces every captured
  prefix exactly (the Requester model's unit discipline against the engine's
  units; `traceOf_units`);
* `schedule`: the conjuncts of `Spec.SchedulePremises` on the recorded plans
  (literal copies below: `Spec/Oblivious.lean` imports Mathlib);
* `plans`: every plan entry's family (the engine's nonce) is the model's
  `familyOf` of its coordinate, and in the arena every entry's table id is a
  recorded table with that coordinate (`HierarchyDiff.coordOf`);
* `fresh`: the theorem's lemma `OnlineFresh` on this run: no
  `(familyOf c, key)` is real-probed twice (and each lies in the horizon's
  coordinates with its key below `N`, reported);
* for the synchronous engine, `sync_schedule`: its recorded plan equals
  `syncSchedule cfg j` at every probing access;
* completeness (fail closed): the view object is present exactly when
  `config.view` (its `sync` view exactly when `config.sync_check`), each view
  records every completed operation (`recorded`: `outcome.accesses`, the
  synchronous engine's up to its own failure), its dummy counters form one
  chain (`counters`: a removed or nulled probing access breaks it), and every
  observed unit lane agrees with its operation (part of `units`).

**At a selected configuration** the top (`T = 2^22`) is not evaluated, and
needs not be: `isReal` of entry `i` reads the tables before it only, every
plan's top entry is its last (checked: `top_order`), and `touched` of the top
entry reads the words and its real flag. So every entry is compared, the
top's included; the top's key set is never computed (`evaluateKeys` stops at
level `L - 1`).

**Efficient evaluation, equal to the trusted definitions.** `touched` and
`isReal` read `stateAt` (a fold over every earlier operation) and `tableKeys`
(the unshared recursion `table`). The oracle advances the requester state one
operation at a time (`stateAt_succ`), reads the dense keys of that state
(`denseKeysWith_eq`, by `rfl`), and reads table membership from hash sets of
the memoised tables (`HierarchyDiff.Env.evalTable`, sound by
`Env.evalTable_sound`, on the trace `traceWith`, which is `traceOf` by `rfl`):
`keySet_table`. `isRealWith_eq` and `touchedWith_eq` lift these to `isReal`
and `touched`. The loops themselves (one step per operation, one memo entry per
job) are argued, as in `HierarchyDiff`.

Core `Lean` and `Std` and the core-only model only, as every oracle module.
-/

open Lean Std

namespace RebuildBound.Oracle.OnlineDiff

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online
open RebuildBound.Oracle (P natField strField boolField arrField objField)
open RebuildBound.Oracle.HierarchyDiff (Replay Env Memo NativeTable coordOf period)

abbrev MRec := RebuildBound.Model.Rec
abbrev OOp := RebuildBound.Model.Online.Op

/-! ### The trusted definitions, evaluated efficiently -/

theorem stateAt_zero (g : OnlineGeom) (run : OnlineRun) : stateAt g run 0 = ⟨[], []⟩ := by
  simp [stateAt, Requester.run]

/-- One more operation is one more requester step. -/
theorem stateAt_succ (g : OnlineGeom) (run : OnlineRun) (j : Nat) (o : OOp)
    (h : run.ops[j]? = some o) :
    stateAt g run (j + 1) = Requester.step g.unitEntries (stateAt g run j) (.access o.record true) := by
  simp only [stateAt, Requester.run, List.take_add_one, h, Option.toList, List.map_append, List.map_cons,
    List.map_nil, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `traceOf` with the final requester state computed once. -/
def traceWith (g : OnlineGeom) (fin : Requester.State) (run : OnlineRun) : Trace :=
  ⟨fun i => (fin.frozen.drop (i * g.unitsPerPrefix)).take g.unitsPerPrefix, run.init, run.unsh⟩

theorem traceWith_eq (g : OnlineGeom) (run : OnlineRun) :
    traceWith g (stateAt g run run.ops.length) run = traceOf g run := rfl

/-- The prefix units of `traceOf` (the units check compares these). -/
theorem traceOf_units (g : OnlineGeom) (run : OnlineRun) (i : Nat) :
    (traceOf g run).units i =
      ((stateAt g run run.ops.length).frozen.drop (i * g.unitsPerPrefix)).take g.unitsPerPrefix := rfl

/-- `denseKeys` on a supplied requester state and consumption mark. -/
def denseKeysWith (cfg : Config) (g : OnlineGeom) (consumed : Nat) (st : Requester.State) : List LogicalKey :=
  ((st.frozen.drop ((consumed - cfg.seed 1) * g.unitsPerPrefix)).flatMap Bucket.recs ++
    st.current.recs).map RebuildBound.Model.Rec.key

theorem denseKeysWith_eq (cfg : Config) (g : OnlineGeom) (run : OnlineRun) (S : Schedule) (j : Nat) :
    denseKeysWith cfg g (S j).consumed (stateAt g run j) = denseKeys cfg g run S j := rfl

/-- `isReal` with the operation, the dense prefix's membership and the tables'
membership supplied. -/
def isRealWith (o : OOp) (inDense : Bool) (tables : List (Nat × Nat)) (tk : Nat × Nat → LogicalKey → Bool)
    (i : Nat) : Bool :=
  o.probes && !inDense && (tables.take i).all fun c => !tk c o.record.key

theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem isRealWith_eq {cfg : Config} {sh : Shapes} {g : OnlineGeom} {run : OnlineRun} {S : Schedule}
    {words : Words} {j i : Nat} {o : OOp} {tk : Nat × Nat → LogicalKey → Bool}
    (ho : run.ops[j]? = some o)
    (htk : ∀ c ∈ (S j).tables,
      tk c o.record.key = (tableKeys cfg sh g run words c.1 c.2).contains o.record.key) :
    isRealWith o ((denseKeysWith cfg g (S j).consumed (stateAt g run j)).contains o.record.key)
        (S j).tables tk i =
      isReal cfg sh g run S words j i := by
  simp only [isReal, ho, isRealWith, denseKeysWith_eq]
  congr 1
  exact all_congr_mem fun c hc => by rw [htk c (List.mem_of_mem_take hc)]

/-- `touched` with the operation, the coordinate, the real flag and the dummy
word supplied. -/
def touchedWith (cfg : Config) (words : Words) (o : OOp) (c : Nat × Nat) (real : Bool) (dw : Nat) :
    Nat :=
  if o.probes then bucket cfg c.1 c.2 (if real then jobWord cfg words c.1 c.2 o.record.key else dw)
  else 0

theorem touchedWith_eq {cfg : Config} {sh : Shapes} {g : OnlineGeom} {run : OnlineRun} {S : Schedule}
    {words : Words} {dummy : Nat → Nat → Nat} {j i : Nat} {o : OOp} {c : Nat × Nat}
    (ho : run.ops[j]? = some o) (hc : (S j).tables[i]? = some c) :
    touchedWith cfg words o c (isReal cfg sh g run S words j i) (dummy j i) =
      touched cfg sh g run S words dummy j i := by
  simp only [touched, ho, hc, touchedWith]

/-- A table's key set as a hash set. -/
def keySet (o : Output) : HashSet LogicalKey := HashSet.ofList (o.records.map RebuildBound.Model.Rec.key)

/-- A key set of a memo table (`Env.evalTable_sound`) on the trace `traceOf`
answers `tableKeys`' membership. -/
theorem keySet_table {e : Env} {g : OnlineGeom} {run : OnlineRun} (htr : e.tr = traceOf g run)
    {ℓ v : Nat} {o : Output} (ho : o = table e.cfg e.sh e.tr e.words ℓ v) (k : LogicalKey) :
    (keySet o).contains k = (tableKeys e.cfg e.sh g run e.words ℓ v).contains k := by
  subst ho
  rw [keySet, HashSet.contains_ofList, htr]
  rfl

/-! ### The schedule's premises (`Spec.SchedulePremises`, decided)

The five fields of `Spec.SchedulePremises cfg S n m` (`Spec/Oblivious.lean`,
which imports Mathlib), copied literally; each is decided by the standard
instances, `Tiles` by `tilesB_iff`. -/

def tilesB (cfg : Config) : List (Nat × Nat) → Nat → Nat → Bool
  | [], lo, hi => lo == hi
  | c :: cs, lo, hi => (window cfg c.1 c.2).2 == hi && decide ((window cfg c.1 c.2).1 ≤ hi) &&
      tilesB cfg cs lo (window cfg c.1 c.2).1

theorem tilesB_iff (cfg : Config) : ∀ (cs : List (Nat × Nat)) (lo hi : Nat),
    tilesB cfg cs lo hi = true ↔ Tiles cfg cs lo hi
  | [], lo, hi => by simp [tilesB, Tiles]
  | c :: cs, lo, hi => by simp [tilesB, Tiles, tilesB_iff cfg cs, and_assoc]

instance (cfg : Config) (cs : List (Nat × Nat)) (lo hi : Nat) : Decidable (Tiles cfg cs lo hi) :=
  decidable_of_iff _ (tilesB_iff cfg cs lo hi)

def PremConsumed (cfg : Config) (S : Schedule) (n : Nat) : Prop :=
  ∀ j < n, cfg.seed 1 ≤ (S j).consumed ∧ (S j).consumed * cfg.carryPositions 1 ≤ pos cfg j
def PremLength (S : Schedule) (n m : Nat) : Prop := ∀ j < n, (S j).tables.length ≤ m
def PremCoords (cfg : Config) (S : Schedule) (n : Nat) : Prop :=
  ∀ j < n, ∀ c ∈ (S j).tables, 1 ≤ c.1 ∧ c.1 ≤ cfg.levels ∧
    (c.1 < cfg.levels → cfg.seed c.1 < c.2) ∧ (c.1 = cfg.levels → cfg.seed c.1 ≤ c.2)
def PremOneTop (cfg : Config) (S : Schedule) (n : Nat) : Prop :=
  ∀ j < n, ((S j).tables.filter (·.1 == cfg.levels)).length ≤ 1
def PremTile (cfg : Config) (S : Schedule) (n : Nat) : Prop :=
  ∀ j < n, Tiles cfg (S j).tables 0 ((S j).consumed * cfg.carryPositions 1)

instance (cfg : Config) (S : Schedule) (n : Nat) : Decidable (PremConsumed cfg S n) := by
  unfold PremConsumed; infer_instance
instance (S : Schedule) (n m : Nat) : Decidable (PremLength S n m) := by
  unfold PremLength; infer_instance
instance (cfg : Config) (S : Schedule) (n : Nat) : Decidable (PremCoords cfg S n) := by
  unfold PremCoords; infer_instance
instance (cfg : Config) (S : Schedule) (n : Nat) : Decidable (PremOneTop cfg S n) := by
  unfold PremOneTop; infer_instance
instance (cfg : Config) (S : Schedule) (n : Nat) : Decidable (PremTile cfg S n) := by
  unfold PremTile; infer_instance

/-- `Config.coordinates` (`Spec/Hierarchy.lean`, which imports Mathlib), copied
literally, as a membership test. -/
def inCoordinates (cfg : Config) (c : Nat × Nat) : Bool :=
  (cfg.ordinaryLevels ++ [cfg.levels]).contains c.1 &&
    decide (cfg.seed c.1 ≤ c.2) && decide (c.2 ≤ cfg.seed c.1 + cfg.ordinals c.1)

/-! ### The fixture's view -/

/-- A recorded plan: the consumption mark and the hashed tables in cascade order;
`size` is `plan.tables.size()` (dense entries included), the dummy counters an
access of the plan claims. -/
structure NPlan where
  consumed : Nat
  tables : List (Nat × Nat)
  ids : List Nat
  families : List (Nat × Nat)
  size : Nat

/-- A recorded probing access; `counter` its first dummy counter. -/
structure NAccess where
  plan : Nat
  touched : Array Nat
  real : Array Bool
  dummy : Array Nat
  counter : Nat

structure NView where
  engine : String
  drive : String
  plans : Array NPlan
  /-- Per recorded operation: `none` for an unprobed write. -/
  accesses : Array (Option NAccess)
  auditViolations : Nat
  /-- The dumper's `recorded` count (must be `accesses.size`). -/
  recorded : Nat

def natOf (ctx : String) (j : Json) : P Nat :=
  match j.getNat? with
  | .ok n => pure n
  | .error _ => throw s!"{ctx}: expected a natural number"

def arrOf (ctx : String) (j : Json) : P (Array Json) :=
  match j.getArr? with
  | .ok a => pure a
  | .error _ => throw s!"{ctx}: expected an array"

def pairOf (ctx : String) (j : Json) : P (Nat × Nat) := do
  match (← arrOf ctx j).toList with
  | [x, y] => return (← natOf ctx x, ← natOf ctx y)
  | _ => throw s!"{ctx}: expected a pair"

def parsePlan (i : Nat) (j : Json) : P NPlan := do
  let ctx := s!"view.plans[{i}]"
  let tables ← (← arrField j ctx "tables").toList.mapM (pairOf s!"{ctx}.tables")
  let ids ← (← arrField j ctx "ids").toList.mapM (natOf s!"{ctx}.ids")
  let families ← (← arrField j ctx "families").toList.mapM (pairOf s!"{ctx}.families")
  if ids.length != tables.length || families.length != tables.length then
    throw s!"{ctx}: tables, ids and families differ in length"
  return { consumed := ← natField j ctx "consumed", tables, ids, families, size := ← natField j ctx "size" }

def parseAccess (i : Nat) (j : Json) : P (Option NAccess) := do
  if j == Json.null then return none
  let ctx := s!"view.accesses[{i}]"
  match (← arrOf ctx j).toList with
  | [p, b, r, d, c] =>
    let touched ← (← arrOf ctx b).mapM (natOf ctx)
    let real ← (← arrOf ctx r).mapM fun x => (· != 0) <$> natOf ctx x
    let dummy ← (← arrOf ctx d).mapM (natOf ctx)
    if real.size != touched.size || dummy.size != touched.size then
      throw s!"{ctx}: touched, real and dummy differ in length"
    return some { plan := ← natOf ctx p, touched, real, dummy, counter := ← natOf ctx c }
  | _ => throw s!"{ctx}: expected [plan, touched, real, dummy, counter]"

def parseView (j : Json) : P NView := do
  let ctx := "view"
  let plans ← (← arrField j ctx "plans").mapIdxM fun i x => parsePlan i x
  let accesses ← (← arrField j ctx "accesses").mapIdxM fun i x => parseAccess i x
  for a in accesses do
    if let some a := a then
      if h : a.plan < plans.size then
        if plans[a.plan].tables.length != a.touched.size then
          throw s!"view.accesses: an access's entries do not match its plan's length"
      else throw s!"view.accesses: plan index {a.plan} out of range"
  return { engine := ← strField j ctx "engine", drive := ← strField j ctx "drive", plans, accesses
           auditViolations := ← natField j ctx "audit_violations", recorded := ← natField j ctx "recorded" }

/-- One issued operation as the fixture lists it. -/
structure FOp where
  kind : String
  key : Nat
  value : Nat
  deriving Inhabited

def parseOps (fixture : Json) : P (Array FOp) := do
  (← arrField fixture "fixture" "ops").mapM fun x => do
    return { kind := ← strField x "ops" "op", key := ← natField x "ops" "key"
             value := ← natField x "ops" "value" }

/-! ### The model's inputs from the fixture -/

/-- The record operation `j` inserted: the engine's unit lane at its position,
else (cleared in its unit, or in an uncaptured prefix) its key with a
placeholder value. The flag says whether the lane was observed. -/
def opRecord (rp : Replay) (E r0 seed1 j : Nat) (op : FOp) : MRec × Bool :=
  let u := j / E
  match (rp.units.get? (seed1 + 1 + u / r0)).bind (·[u % r0]?) |>.bind (·[j % E]?) with
  | some (some r) => (r, true)
  | _ =>
    if op.kind == "write" || op.kind == "write_np" then (⟨LogicalKey.ofNat op.key, op.value, false⟩, false)
    else (⟨LogicalKey.ofNat op.key, 0, true⟩, false)

def opOf (op : FOp) (r : MRec) : OOp := if op.kind == "write_np" then .blind r else .probe r

/-- An observed unit lane agrees with the operation at its position: its key; an
erase inserts a tombstone; a write (probed or not) inserts its value (the user
bytes below the meta byte). A read inserts the value it found or a tombstone. -/
def recordAgrees (valueBytes : Nat) (op : FOp) (r : MRec) : Bool :=
  LogicalKey.toNat r.key == op.key &&
    (if op.kind == "erase" then r.tomb
     else if op.kind == "write" || op.kind == "write_np" then
       !r.tomb && r.val % 2 ^ (8 * (valueBytes - 1)) == op.value
     else true)

/-- The expected number of recorded operations of each engine's view: every
completed operation (`outcome.accesses`; the synchronous engine's record ends
at its own failure, `checks.sync.sync_failure.access`), up to
`config.view_limit`. -/
def expectedRecorded (rp : Replay) (sync : Bool) : Nat :=
  let n := if sync then min rp.accesses (rp.syncFailureAccess.getD rp.accesses) else rp.accesses
  match rp.viewLimit with
  | some l => min l n
  | none => n

/-- The view object of a fixture, checked against the configuration: `none`
without `--view`; with it, the `arena` view, and the `sync` view exactly when
`config.sync_check`. A view the configuration does not announce, or an
announced one that is missing, is malformed. Also: operations tagged as
`AccessBatch` lanes (`ops[].batch`) or recorded chunks only when
`config.batch` is nonzero. -/
def viewObjects (rp : Replay) (fixture : Json) : P (Option (Json × Option Json)) := do
  let viewJ := match fixture.getObjVal? "view" with
    | .ok Json.null => none
    | .ok v => some v
    | .error _ => none
  let some viewJ := viewJ
    | if rp.viewRequested then throw "view: missing, but config.view is true" else return none
  if !rp.viewRequested then throw "view: present, but config.view is false"
  let obj (k : String) : Option Json := match viewJ.getObjVal? k with
    | .ok Json.null => none
    | .ok v => some v
    | .error _ => none
  let some arena := obj "arena" | throw "view.arena: missing"
  let sync := obj "sync"
  if rp.syncCheck && sync.isNone then throw "view.sync: missing, but config.sync_check is true"
  if !rp.syncCheck && sync.isSome then throw "view.sync: present, but config.sync_check is false"
  if rp.batch == 0 then
    for x in ← arrField fixture "fixture" "ops" do
      if (x.getObjVal? "batch").toOption.isSome then
        throw "ops: an AccessBatch lane (ops[].batch) in a fixture with config.batch = 0"
    for v in arena :: sync.toList do
      match v.getObjVal? "chunks" with
      | .ok (Json.arr a) => if !a.isEmpty then throw "view.chunks: chunks in a fixture with config.batch = 0"
      | _ => pure ()
  else
    for v in arena :: sync.toList do
      match v.getObjVal? "chunks" with
      | .ok (Json.arr _) => pure ()
      | _ => throw "view.chunks: missing in a fixture with config.batch nonzero"
    -- a batch run hands operations to AccessBatch (`ops[].batch`)
    let tagged := (← arrField fixture "fixture" "ops").any fun x => (x.getObjVal? "batch").toOption.isSome
    if !tagged && rp.accesses > 0 then
      throw "ops: no AccessBatch lane (ops[].batch) in a fixture with config.batch nonzero"
  return some (arena, sync)

/-- The dummy counters of a view form one chain: the first probing access's
first counter is 1 and each probing access (each chunk) starts where the
previous one's `size` (`lanes · size`) counters end; a lane of a chunk starts at
the chunk's base plus its index times the plan's size. A recorded access that
was removed (or nulled) breaks the chain. Returns the number of breaks. -/
def counterBreaks (v : NView) (chunks : Array (Nat × Nat × Nat × Nat)) : Nat := Id.run do
  let starts : HashMap Nat (Nat × Nat × Nat) := chunks.foldl (fun m (f, l, p, b) => m.insert f (l, p, b)) {}
  let n := v.accesses.size
  let mut next := 1
  let mut breaks := 0
  let mut t := 0
  let mut fuel := n + 1
  while t < n && fuel > 0 do
    fuel := fuel - 1
    match starts[t]? with
    | some (m, p, base) =>
      let size := (v.plans[p]?.map (·.size)).getD 0
      if base != next then breaks := breaks + 1
      for l in [0:m] do
        match v.accesses[t + l]? with
        | some (some a) => if a.counter != base + l * size then breaks := breaks + 1
        | _ => breaks := breaks + 1
      next := base + m * size
      t := t + max m 1
    | none =>
      match v.accesses[t]? with
      | some (some a) =>
        if a.counter != next then breaks := breaks + 1
        next := a.counter + ((v.plans[a.plan]?.map (·.size)).getD 0)
      | _ => pure ()
      t := t + 1
  return breaks

/-- The schedule of recorded plans: operation `j` reads plan `idx[j]`. -/
def scheduleOf (plans : Array NPlan) (idx : Array Nat) : Schedule := fun j =>
  match idx[j]? with
  | some p => match plans[p]? with
    | some q => ⟨q.consumed, q.tables⟩
    | none => ⟨0, []⟩
  | none => ⟨0, []⟩

/-- Each operation's plan index: its own; an unprobed write the previous probing
access's (leading ones: the first probing access's). -/
def planIndex (v : NView) : Array Nat := Id.run do
  let first := (v.accesses.findSome? fun a => a.map (·.plan)).getD 0
  let mut cur := first
  let mut out := #[]
  for a in v.accesses do
    if let some a := a then cur := a.plan
    out := out.push cur
  return out

/-- Evaluate the serialised order up to level-one ordinal `tEnd` on the memo,
keeping the key sets of the `need`ed coordinates (base coordinates from
`base`). Each memo entry is the model's table (`Env.evalTable_sound`,
`Sound.insert`, `Sound.erase`), so each key set answers `tableKeys` when
`e.tr = traceOf g run` (`keySet_table`). Levels above `top` are not evaluated
(`top = L - 1` at a selected configuration: `table ℓ v` for `ℓ < L` does not
read the top). -/
def evaluateKeys (e : Env) (need : List (Nat × Nat)) (tEnd : Nat) (top : Nat) :
    Except String (HashMap (Nat × Nat) (HashSet LogicalKey)) := do
  let cfg := e.cfg
  let L := top
  let needSet : HashSet (Nat × Nat) := HashSet.ofList need
  let mut ks : HashMap (Nat × Nat) (HashSet LogicalKey) := {}
  for (ℓ, v) in need do
    if e.IsBase ℓ v then ks := ks.insert (ℓ, v) (keySet (base cfg e.sh e.tr e.words ℓ))
  let mut memo : Memo := {}
  for t in [cfg.seed 1 + 1 : tEnd + 1] do
    for ℓ in [1 : L + 1] do
      let p := period cfg ℓ
      if t % p != 0 then continue
      let v := t / p
      let some o := e.evalTable memo ℓ v | throw s!"internal: table ({ℓ}, {v}) not evaluable"
      if needSet.contains (ℓ, v) then ks := ks.insert (ℓ, v) (keySet o)
      memo := (memo.insert (ℓ, v) o).erase (ℓ, v - 1)
  return ks

/-! ### The comparison -/

def limit : Nat := 5

structure ViewAcc where
  probing : Nat := 0
  entries : Nat := 0
  real : Nat := 0
  bucketMismatches : Nat := 0
  realMismatches : Nat := 0
  kindMismatches : Nat := 0
  shown : Array Json := #[]
  freshDup : Nat := 0
  freshShown : Array Json := #[]
  outsideCoords : Nat := 0
  keysPastN : Nat := 0
  wordsMissing : Nat := 0
  engineReal : Nat := 0
  topEntries : Nat := 0
  topNotLast : Nat := 0

def ViewAcc.show (a : ViewAcc) (j : Json) : ViewAcc :=
  if a.shown.size < limit then { a with shown := a.shown.push j } else a

/-- The checks of one engine's view. -/
def checkView (rp : Replay) (e : Env) (g : OnlineGeom) (opsArr : Array OOp)
    (ks : HashMap (Nat × Nat) (HashSet LogicalKey)) (v : NView) (N : Nat) (sync : Bool) (skipTop : Bool) :
    List String × Json := Id.run do
  let cfg := e.cfg
  let n := v.accesses.size
  let idx := planIndex v
  let S := scheduleOf v.plans idx
  let tk : Nat × Nat → LogicalKey → Bool := fun c k => match ks[c]? with
    | some s => s.contains k
    | none => false
  let dummy : Nat → Nat → Nat := fun j i => match v.accesses[j]? with
    | some (some a) => a.dummy.getD i 0
    | _ => 0
  let mut acc : ViewAcc := {}
  let mut seen : HashSet ((Nat × Nat) × LogicalKey) := {}
  let mut st : Requester.State := ⟨[], []⟩  -- `stateAt g run 0` (`stateAt_zero`)
  for h : j in [0:n] do
    let some o := opsArr[j]? | break
    match v.accesses[j] with
    | none =>
      if o.probes then
        acc := { acc with kindMismatches := acc.kindMismatches + 1 }
        acc := acc.show (Json.mkObj [("op", toJson j), ("problem", "probing op without an access")])
    | some a =>
      if !o.probes then
        acc := { acc with kindMismatches := acc.kindMismatches + 1 }
        acc := acc.show (Json.mkObj [("op", toJson j), ("problem", "unprobed write with an access")])
      let key := o.record.key
      let tables := (S j).tables
      -- `denseKeysWith … (stateAt g run j)` is `denseKeys … j` (`denseKeysWith_eq`)
      let inDense := (denseKeysWith cfg g (S j).consumed st).contains key
      acc := { acc with probing := acc.probing + 1 }
      let mut i := 0
      for c in tables do
        -- the top's contents are not evaluated at a selected configuration:
        -- the entries after a top entry would read them (`tables.take i`)
        if c.1 == cfg.levels then
          acc := { acc with topEntries := acc.topEntries + 1 }
          if skipTop && i + 1 != tables.length then acc := { acc with topNotLast := acc.topNotLast + 1 }
        -- `isRealWith_eq`, `touchedWith_eq`: these are `isReal` and `touched`
        let real := isRealWith o inDense tables tk i
        let b := touchedWith cfg e.words o c real (dummy j i)
        let nb := a.touched.getD i 0
        let nr := a.real.getD i false
        acc := { acc with entries := acc.entries + 1, real := acc.real + (if real then 1 else 0),
                          engineReal := acc.engineReal + (if nr then 1 else 0) }
        if b != nb || real != nr then
          acc := { acc with bucketMismatches := acc.bucketMismatches + (if b != nb then 1 else 0),
                            realMismatches := acc.realMismatches + (if real != nr then 1 else 0) }
          acc := acc.show (Json.mkObj [("op", toJson j), ("entry", toJson i), ("table", toJson [c.1, c.2]),
            ("key", toJson (LogicalKey.toNat key)), ("model", Json.mkObj [("bucket", toJson b), ("real", toJson real)]),
            ("engine", Json.mkObj [("bucket", toJson nb), ("real", toJson nr)]),
            ("in_dense", toJson inDense), ("consumed", toJson (S j).consumed)])
        if real then
          let f := familyOf cfg c.1 c.2
          if !((rp.words.get? f).map (·.contains (LogicalKey.toNat key))).getD false then
            acc := { acc with wordsMissing := acc.wordsMissing + 1 }
          if !inCoordinates cfg f then acc := { acc with outsideCoords := acc.outsideCoords + 1 }
          if LogicalKey.toNat key ≥ N then acc := { acc with keysPastN := acc.keysPastN + 1 }
          if seen.contains (f, key) then
            acc := { acc with freshDup := acc.freshDup + 1 }
            if acc.freshShown.size < limit then
              acc := { acc with freshShown := acc.freshShown.push (Json.mkObj [("op", toJson j),
                ("entry", toJson i), ("family", toJson [f.1, f.2]), ("key", toJson (LogicalKey.toNat key))]) }
          seen := seen.insert (f, key)
        i := i + 1
    -- `stateAt g run (j + 1)` (`stateAt_succ`)
    st := Requester.step g.unitEntries st (.access o.record true)
  -- the schedule's premises over the recorded accesses
  let m := v.plans.foldl (fun x p => max x p.tables.length) 0
  let pc := decide (PremConsumed cfg S n)
  let pl := decide (PremLength S n m)
  let pco := decide (PremCoords cfg S n)
  let pt := decide (PremOneTop cfg S n)
  let pti := decide (PremTile cfg S n)
  let mut firstBad : Option Json := none
  for h : j in [0:n] do
    let q := S j
    let bad : List String :=
      (if decide (cfg.seed 1 ≤ q.consumed ∧ q.consumed * cfg.carryPositions 1 ≤ pos cfg j) then [] else ["consumed"]) ++
      (if decide (∀ c ∈ q.tables, 1 ≤ c.1 ∧ c.1 ≤ cfg.levels ∧ (c.1 < cfg.levels → cfg.seed c.1 < c.2) ∧
          (c.1 = cfg.levels → cfg.seed c.1 ≤ c.2)) then [] else ["coords"]) ++
      (if (q.tables.filter (·.1 == cfg.levels)).length ≤ 1 then [] else ["one_top"]) ++
      (if tilesB cfg q.tables 0 (q.consumed * cfg.carryPositions 1) then [] else ["tile"])
    if !bad.isEmpty then
      firstBad := some (Json.mkObj [("op", toJson j), ("failed", toJson bad), ("consumed", toJson q.consumed),
        ("tables", toJson (q.tables.map fun c => [c.1, c.2])),
        ("windows", toJson (q.tables.map fun c => [(window cfg c.1 c.2).1, (window cfg c.1 c.2).2]))])
      break
  let schedOk := pc && pl && pco && pt && pti
  -- plan identities: the engine's family is the model's, the arena's ids the recorded tables'
  let byId : HashMap Nat NativeTable := rp.tables.foldl (fun mp t => mp.insert t.id t) {}
  let mut famBad := 0
  let mut idBad := 0
  let mut identShown : Array Json := #[]
  for p in v.plans do
    for ((c, f), id) in (p.tables.zip p.families).zip p.ids do
      if familyOf cfg c.1 c.2 != f then
        famBad := famBad + 1
        if identShown.size < limit then
          identShown := identShown.push (Json.mkObj [("table", toJson [c.1, c.2]), ("engine_family", toJson [f.1, f.2]),
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
  -- the synchronous mode's schedule
  let mut syncCmp := 0
  let mut syncDiff := 0
  let mut syncShown : Array Json := #[]
  if sync then
    for h : j in [0:n] do
      if v.accesses[j].isNone then continue
      syncCmp := syncCmp + 1
      let q := S j
      let s := syncSchedule cfg j
      if q.consumed != s.consumed || q.tables != s.tables then
        syncDiff := syncDiff + 1
        if syncShown.size < limit then
          syncShown := syncShown.push (Json.mkObj [("op", toJson j),
            ("engine", Json.mkObj [("consumed", toJson q.consumed), ("tables", toJson (q.tables.map fun c => [c.1, c.2]))]),
            ("sync_schedule", Json.mkObj [("consumed", toJson s.consumed), ("tables", toJson (s.tables.map fun c => [c.1, c.2]))])])
  -- completeness: every completed operation recorded, the counters one chain
  let expected := expectedRecorded rp sync
  let recordedOk := n == expected && v.recorded == n
  let breaks := counterBreaks v #[]
  let pfx := if sync then "online.sync." else "online.arena."
  let failures :=
    (if acc.bucketMismatches == 0 then [] else [pfx ++ "view"]) ++
    (if acc.realMismatches == 0 then [] else [pfx ++ "real"]) ++
    (if acc.kindMismatches == 0 then [] else [pfx ++ "kinds"]) ++
    (if schedOk then [] else [pfx ++ "schedule"]) ++
    (if famBad == 0 && idBad == 0 then [] else [pfx ++ "plans"]) ++
    (if acc.freshDup == 0 then [] else [pfx ++ "fresh"]) ++
    (if acc.wordsMissing == 0 then [] else [pfx ++ "words"]) ++
    (if syncDiff == 0 then [] else [pfx ++ "sync_schedule"]) ++
    (if v.auditViolations == 0 then [] else [pfx ++ "audit"]) ++
    (if recordedOk then [] else [pfx ++ "recorded"]) ++
    (if breaks == 0 then [] else [pfx ++ "counters"]) ++
    (if acc.topNotLast == 0 then [] else [pfx ++ "top_order"])
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
    ("words_missing", toJson acc.wordsMissing),
    ("audit_violations", toJson v.auditViolations)] ++
    (if sync then [("sync_schedule", Json.mkObj [("compared", toJson syncCmp), ("differ", toJson syncDiff),
      ("first", toJson syncShown), ("result", pf (syncDiff == 0))])] else []))
  return (failures, json)

/-- The online checks of a parsed fixture with a `view`; `none` without one. -/
def check (rp : Replay) (fixture : Json) : P (Option (List String × Json)) := do
  let some (arenaJ, syncJ) ← viewObjects rp fixture | return none
  let arenaV ← some <$> parseView arenaJ
  let syncV ← syncJ.mapM parseView
  -- at a selected configuration the top is not evaluated (`skipTop`)
  let skipTop := rp.selected.isSome
  let fops ← parseOps fixture
  let cfg := rp.cfg
  let E := 64 * rp.stashBuckets
  let r0 := rp.prefixFlushes
  let g : OnlineGeom := ⟨E, r0⟩
  let seed1 := cfg.seed 1
  -- the run: the operations every recorded view covers
  let n := max (arenaV.map (·.accesses.size) |>.getD 0) (syncV.map (·.accesses.size) |>.getD 0)
  if n > rp.accesses || n > fops.size then throw "view: more recorded accesses than completed operations"
  let mut opsArr : Array OOp := #[]
  let mut unobserved := 0
  let mut keyBad := 0
  for j in [0:n] do
    let fo := fops[j]!
    let (r, seenLane) := opRecord rp E r0 seed1 j fo
    if !seenLane then unobserved := unobserved + 1
    if seenLane && !recordAgrees rp.valueBytes fo r then keyBad := keyBad + 1
    opsArr := opsArr.push (opOf fo r)
  let run : OnlineRun := ⟨opsArr.toList, rp.init, HierarchyDiff.unshOf rp.valueBytes⟩
  let fin := stateAt g run run.ops.length
  let base := rp.env
  let e : Env := { base with tr := traceWith g fin run }  -- `traceOf g run` (`traceWith_eq`)
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
  let views := (arenaV.toList.map (·, false)) ++ (syncV.toList.map (·, true))
  let mut need : HashSet (Nat × Nat) := {}
  for (v, _) in views do
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
  for (v, sync) in views do
    let (f, j) := checkView rp e g opsArr ks v N sync skipTop
    failures := failures ++ f
    parts := parts ++ [(if sync then "sync" else "arena", j)]
  let json := Json.mkObj ([
    ("operations", toJson n), ("records_unobserved", toJson unobserved),
    ("units", Json.mkObj [("ordinals", toJson unitOrds), ("mismatches", toJson unitBad),
      ("first", toJson unitShown), ("result", toJson (if unitBad == 0 then "pass" else "fail"))]),
    ("tables_evaluated_to", toJson tEnd), ("coordinates", toJson needL.length),
    ("top_evaluated", toJson !skipTop)] ++ parts ++
    [("failures", toJson failures), ("result", toJson (if failures.isEmpty then "pass" else "fail"))])
  return some (failures, json)

/-- `--hierarchy` on a fixture with a view: the hierarchy replay's line with an
`online` object, its failures added to `failures`. -/
def runCombined (path text : String) : P (Json × UInt32) := do
  let fixture ← Json.parse text
  let (out, code) ← HierarchyDiff.runJson path fixture
  let rp ← HierarchyDiff.parseReplayJson fixture
  match ← check rp fixture with
  | none => return (out, code)
  | some (failures, oj) =>
    let prev := match out.getObjValAs? (List String) "failures" with
      | .ok l => l
      | .error _ => []
    let all := prev ++ failures
    let out := out.setObjVal! "online" oj |>.setObjVal! "failures" (toJson all)
      |>.setObjVal! "result" (toJson (if all.isEmpty then "pass" else "fail"))
    return (out, if all.isEmpty then 0 else 1)

/-- `--online`: the view checks alone. -/
def runOnline (path text : String) : P (Json × UInt32) := do
  let fixture ← Json.parse text
  let rp ← HierarchyDiff.parseReplayJson fixture
  match ← check rp fixture with
  | none => throw "view: the fixture has no view (hierarchy_dump --view)"
  | some (failures, oj) =>
    let out := Json.mkObj [("file", toJson path), ("mode", "online"), ("online", oj),
      ("failures", toJson failures), ("result", toJson (if failures.isEmpty then "pass" else "fail"))]
    return (out, if failures.isEmpty then 0 else 1)

end RebuildBound.Oracle.OnlineDiff
