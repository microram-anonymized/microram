import RebuildBound.Spec.Model.TopPrepContract

/-!
Executable test of the top preparation's deterministic statements
(`Spec/TopPrepT.lean`) on random small geometries and inputs that meet
`TPShape`:

    lake env lean --run spec_tests/TPStatements.lean [trials]

Checks TPEngine (the engine's schedule is valid), TP12, TP4a, TP4b and TP6 for
the engine's schedule and the stage-by-stage one, a random valid schedule
included, and TP5_route on a pair of words agreeing below a random bit; also
the initialization (`initMain`, `unsh = false`). Negative controls: a schedule
that breaks stage order must fail the validity check, and TP4b's bound with
the drain target one record larger than the excess must sometimes fail.
Core Lean only.
-/

open RebuildBound.Model

structure Rng where
  s : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let x := g.s
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  (x, ⟨x⟩)

def Rng.below (g : Rng) (n : Nat) : Nat × Rng :=
  let (x, g) := g.next
  (if n = 0 then 0 else x.toNat % n, g)

abbrev R := StateM Rng

def rand (n : Nat) : R Nat := modifyGet fun g => g.below n

def pick {α} [Inhabited α] (l : List α) : R α := do return l[(← rand l.length)]!

/-- `TPValidSchedule`, decidably. -/
def validSched (g : TPGeom) (ops : List (Nat × Nat)) : Bool :=
  let can := g.canonicalOps
  let perm := ops.length == can.length && can.all (fun o => ops.count o == 1) &&
    ops.all (fun o => can.contains o)
  let byBucket := ops.foldl (fun (m : Array (List Nat)) o =>
      let m := if o.2 < m.size then m.modify o.2 (· ++ [o.1]) else m
      if o.2 + 2 ^ o.1 < m.size then m.modify (o.2 + 2 ^ o.1) (· ++ [o.1]) else m)
    (Array.replicate g.T [])
  perm && byBucket.all fun l => (l.zip (l.drop 1)).all fun p => p.1 < p.2

def permRecs (a b : List Rec) : Bool :=
  a.length == b.length && a.all (fun x => a.count x == b.count x)

/-- A random valid schedule: repeatedly run a random ready operation (all
earlier-stage operations on its two buckets done). -/
def randSchedule (g : TPGeom) : R (List (Nat × Nat)) := do
  let mut left := g.canonicalOps
  let mut out : List (Nat × Nat) := []
  let mut fuel := left.length + 1
  while !left.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let ready := left.filter fun o =>
      !left.any fun p => p.1 < o.1 &&
        (p.2 == o.2 || p.2 == o.2 + 2 ^ o.1 || p.2 + 2 ^ p.1 == o.2 || p.2 + 2 ^ p.1 == o.2 + 2 ^ o.1)
    let o ← pick ready
    out := out ++ [o]
    left := left.erase o
  return out

/-- A random geometry in the model's domain. -/
def randGeom : R TPGeom := do
  let C ← pick [1, 2, 3, 4]
  let k ← pick [1, 2, 3, 4, 5, 6]
  let dfs ← pick [true, true, true, false]
  let I ← if dfs then rand (k + 1) else pure k
  return { C, k, stashPages := ← pick [0, 1, 1, 2, 3], aTierPages := ← pick [0, 1, 2],
           drainPages := ← pick [0, 1, 2, 4], rangeBits := k - I, I, dfs }

/-- Random inputs meeting `TPShape`: A's keys at their starting buckets, some
overflow in the old tier; random plain and flagged tombstones. Returns
`(pos, w, unsh, inputs)`. -/
def randInputs (g : TPGeom) : R ((LogicalKey → Nat) × (LogicalKey → Nat) × (Rec → Bool) × TPInputs) := do
  let W := 16
  let fa ← pick [3, 6, 8, 10, 12, 16]
  let n ← rand (g.C * g.T * fa / 10 + 2)
  let mut pos : Array Nat := Array.replicate (n + 1) 0
  let mut w : Array Nat := Array.replicate (n + 1) 0
  for x in [0:n + 1] do
    pos := pos.set! x (← rand g.T)
    w := w.set! x (← rand (2 ^ W))
  let posF := fun key : LogicalKey => pos.getD (LogicalKey.toNat key) 0
  let wF := fun key : LogicalKey => w.getD (LogicalKey.toNat key) 0
  -- the unshadowed flag: val bit 0
  let unsh := fun (r : Rec) => r.val % 2 == 1
  let mut aMain : Array (List Rec) := Array.replicate g.T []
  let mut aTier : List Rec := []
  for x in [0:n] do
    let rc : Rec := { key := LogicalKey.ofNat x, val := ← rand 1000, tomb := (← rand 4) == 0 }
    let h := posF (LogicalKey.ofNat x)
    if (aMain.getD h []).length < g.C && (← rand 5) != 0 then aMain := aMain.modify h (· ++ [rc])
    else aTier := aTier ++ [rc]
  let scatter (recs : List Rec) : R Bucket := do
    let mut lanes : Array (Option Rec) := Array.replicate g.C none
    for rc in recs do
      let free := (List.range g.C).filter fun l => (lanes.getD l none).isNone
      let l ← pick free
      lanes := lanes.set! l (some rc)
    return lanes.toList
  let mut aB : List Bucket := []
  for b in aMain.toList do aB := aB ++ [← scatter b]
  return (posF, wF, unsh, { aMain := aB, aTier := aTier })

def kindName (g : TPGeom) : TPTest → String
  | .stash j => if j + 1 < g.k then "butterfly" else "butterfly-offers"
  | .dfs _ _ => "dfs" | .drain => "drain"

def bump (l : List (String × Nat)) (k : String) : List (String × Nat) :=
  if l.any (·.1 == k) then l.map (fun p => if p.1 == k then (p.1, p.2 + 1) else p) else l ++ [(k, 1)]

/-- Check TP12, TP4a, TP4b on one case and schedule; returns the violated ones,
the first failure, and whether the negative control of TP4b fired. -/
def checkCase (g : TPGeom) (pos w : LogicalKey → Nat) (unsh : Rec → Bool) (inp : TPInputs)
    (ops : List (Nat × Nat)) : List String × Option TPTest × Bool := Id.run do
  let run := tpReferenceWith engineRule g unsh w inp ops
  let out := run.output
  let surv := inp.survivors unsh
  let mut bad : List String := []
  -- TP12
  if !permRecs (out.main.flatMap Bucket.recs ++ out.tier.filterMap id) surv then bad := bad ++ ["TP1"]
  if out.main.length != g.T || !out.main.all (·.length == g.C) then bad := bad ++ ["TP2-shape"]
  for v in [0:g.T] do
    let B := out.main.getD v []
    if !B.recs.all (fun r => tpHome g w r == v) then bad := bad ++ [s!"TP2-home {v}"]
    if B.recs.length != min (tpHomeCount g w surv v) g.C then bad := bad ++ [s!"TP2-count {v}"]
  if !(out.tier.filterMap id).all (fun r => (out.main.getD (tpHome g w r) []).recs.length == g.C) then
    bad := bad ++ ["TP2-full"]
  -- TP4
  let ff := tpFirstFailure g run.trace
  match ff with
  | some (.stash j) =>
    if !(g.stashPages * g.C < tpRawStageExcess g unsh pos w inp j) then bad := bad ++ [s!"TP4a-stash {j}"]
  | some (.dfs _ _) =>
    if inp.aTier.length ≤ g.aTierPages * g.C then
      let ok := (List.range g.ranges).any fun R => g.C < tpRefCoarse g unsh w run inp g.earlyCap R
      if !ok then bad := bad ++ ["TP4a-dfs"]
  | some .drain =>
    if !(g.drainPages * g.C < tpHomeExcess g unsh w inp) then bad := bad ++ ["TP4b"]
  | none => pure ()
  -- negative control: with the drain target exactly the excess, the drain never fails;
  -- with one record less it fails whenever the excess is positive and earlier tests pass.
  let ex := tpHomeExcess g unsh w inp
  let ctl := ex > 0 && g.drainPages * g.C == ex - 1 && ff == some .drain
  return (bad, ff, ctl)

def main (args : List String) : IO UInt32 := do
  let trials := (args.headD "3000").toNat!
  let mut rng : Rng := ⟨0x9E3779B97F4A7C15⟩
  let mut failures : Array String := #[]
  let mut kinds : List (String × Nat) := []
  let mut successes := 0
  let mut controls := 0
  let mut badSched := 0
  let mut inits := 0
  for t in [0:trials] do
    let ((g, (pos, w, unsh, inp), ops, w', n, input, initW), rng') := (do
        let g ← randGeom
        let i ← randInputs g
        let ops ← randSchedule g
        -- TP5: words agreeing below bit n on every key
        let n ← rand g.k
        let mut w2 : Array Nat := Array.replicate 200000 0
        let wF := i.2.1
        let w' := fun key : LogicalKey => wF key % 2 ^ n +
          2 ^ n * ((wF key / 2 ^ n + LogicalKey.toNat key * 7 + 3) % 1024)
        -- initialization input: distinct keys, at most C/2 per bucket
        let cnt ← rand (g.C / 2 * g.T + 1)
        let input := (List.range cnt).map fun x => ({ key := LogicalKey.ofNat (x + 1), val := x, tomb := false } : Rec)
        let _ := w2
        return (g, i, ops, w', n, input, wF)).run rng
    rng := rng'
    let ctx := s!"trial {t}: k={g.k} C={g.C} S={g.stashPages} TA={g.aTierPages} R={g.drainPages} I={g.I} dfs={g.dfs}"
    if !g.Valid then failures := failures.push s!"{ctx}: invalid geometry"; continue
    -- TPEngine
    if !validSched g (tpEngineOps g) then failures := failures.push s!"{ctx}: TPEngine"
    if !validSched g ops then failures := failures.push s!"{ctx}: random schedule invalid (test bug)"
    -- negative control of the validity check: reverse a stage-sorted schedule
    if g.k ≥ 3 && validSched g g.canonicalOps.reverse then failures := failures.push s!"{ctx}: reversed schedule accepted"
    if g.k ≥ 3 then badSched := badSched + 1
    let mut verdicts : List Bool := []
    for sch in [tpEngineOps g, g.canonicalOps, ops] do
      let (bad, ff, ctl) := checkCase g pos w unsh inp sch
      for b in bad do failures := failures.push s!"{ctx}: {b}"
      if ctl then controls := controls + 1
      match ff with
      | none => successes := successes + 1
      | some f => kinds := bump kinds (kindName g f)
      verdicts := verdicts ++ [(tpJobWith engineRule g unsh w inp sch).toBool]
    -- TP6
    let rc := tpReferenceWith engineRule g unsh w inp g.canonicalOps
    for sch in [tpEngineOps g, ops] do
      let rs := tpReferenceWith engineRule g unsh w inp sch
      if rs.route.main != rc.route.main then failures := failures.push s!"{ctx}: TP6-main"
      if !(List.range g.k).all (fun j => permRecs (rs.route.stash.getD j []) (rc.route.stash.getD j [])) then
        failures := failures.push s!"{ctx}: TP6-stash"
    if !(verdicts.all (· == verdicts.headD true)) then failures := failures.push s!"{ctx}: TP6-verdict"
    -- TP5_route
    if n ≤ g.k - 1 then
      let r1 := tpRouteUpTo engineRule g unsh w inp.aMain n
      let r2 := tpRouteUpTo engineRule g unsh w' inp.aMain n
      if r1.main != r2.main || r1.stash != r2.stash || r1.trace != r2.trace then
        failures := failures.push s!"{ctx}: TP5 n={n}"
    -- the initialization: scatter + no drop, every schedule
    let iinp : TPInputs := ⟨initMain g input, []⟩
    let ipos := fun key : LogicalKey => (LogicalKey.toNat key - 1) / (g.C / 2)
    if g.C ≥ 2 then
      inits := inits + 1
      for sch in [tpEngineOps g, g.canonicalOps] do
        let (bad, _, _) := checkCase g ipos initW (fun _ => false) iinp sch
        for b in bad do failures := failures.push s!"{ctx}: init {b}"
  IO.println s!"trials {trials}: schedules checked {3 * trials}, successes {successes}, failures by kind {kinds}"
  IO.println s!"initializations {inits}; TP4b negative controls fired {controls}; reversed-schedule controls {badSched}"
  IO.println s!"violations: {failures.size}"
  for f in failures.toList.take 30 do IO.println s!"  {f}"
  return if failures.isEmpty then 0 else 1
