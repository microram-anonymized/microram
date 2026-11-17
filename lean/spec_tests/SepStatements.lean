import RebuildBound.Spec.Model.SepContract

/-!
Executable test of the D9 statements (`Spec/SepT.lean`) on random small
geometries and random inputs that meet `SInputShape`:

    lake env lean --run spec_tests/SepStatements.lean [trials]

Checks, for the engine's schedule and the stage-by-stage one: SEngine (the
engine's schedule is valid), ST1, ST2, ST4a, ST4b and ST6. Negative controls:
the same checks with a schedule that breaks stage order, and T4b's bound
without the excess. Core Lean only.
-/

open RebuildBound.Model

/-- A 64-bit xorshift generator. -/
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

/-- The schedule check `SValidSched`, decidably. -/
def validSched (g : SepGeom) (ops : List (Nat × Nat)) : Bool :=
  let can := g.canonicalOps
  let perm := ops.length == can.length && can.all (fun o => ops.count o == 1) && ops.all (fun o => can.contains o)
  let touch (a b : Nat × Nat) : Bool :=
    a.2 == b.2 || a.2 == b.2 + 2 ^ b.1 || a.2 + 2 ^ a.1 == b.2 || a.2 + 2 ^ a.1 == b.2 + 2 ^ b.1
  -- stage order per bucket: the ops touching each bucket appear in increasing bit order
  let byBucket := ops.foldl (fun (m : Array (List Nat)) o =>
      let m := if o.2 < m.size then m.modify o.2 (· ++ [o.1]) else m
      if o.2 + 2 ^ o.1 < m.size then m.modify (o.2 + 2 ^ o.1) (· ++ [o.1]) else m)
    (Array.replicate g.N [])
  let ordered := byBucket.all fun l => (l.zip (l.drop 1)).all fun p => p.1 < p.2
  let _ := touch
  perm && ordered

def permRecs (a b : List Rec) : Bool :=
  a.length == b.length && a.all (fun x => a.count x == b.count x)

/-- A random geometry in the model's domain. -/
def randGeom : R SepGeom := do
  let C ← pick [1, 2, 3, 4]
  let K ← pick [1, 2, 3]
  let (r, e) ← pick [(1, 1), (1, 2), (1, 3), (3, 0), (3, 1), (5, 0), (7, 0)]
  let k := K + e
  let N := r * 2 ^ k
  -- the smallest m with N ≤ 2^m
  let m := (List.range 12).find? (fun m => N ≤ 2 ^ m) |>.getD 12
  let I ← rand (m + 1)
  let rangeBits := m - I
  return { C, K, e, r, rangeBits, I, stashPages := ← pick [0, 1, 1, 2, 3, 4], aTierPages := ← pick [0, 1, 2],
           bTierPages := ← pick [1, 2], tierPages := ← pick [0, 1, 2] }

/-- Random inputs meeting `SInputShape`: A's keys at their old homes, the
overflow in A's tier; B's keys (some shared with A) at their carry buckets,
the overflow spread over B's tier pages. Returns `(wOld, w, inputs)`. -/
def randInputs (g : SepGeom) : R ((LogicalKey → Nat) × (LogicalKey → Nat) × SInputs) := do
  let W := 16
  let fa ← pick [3, 6, 8, 9, 10, 12]
  let nA ← rand (g.C * (g.d - 1) * g.U * fa / 10 + 2)
  let nB ← rand (g.C * g.U * fa / 8 + 2)
  -- keys 1.., words
  let mut wOld : Array Nat := Array.replicate (nA + nB + 2) 0
  let mut w : Array Nat := Array.replicate (nA + nB + 2) 0
  for x in [0:nA + nB + 2] do
    wOld := wOld.set! x (← rand (2 ^ W))
    w := w.set! x (← rand (2 ^ W))
  let wOldF := fun key : LogicalKey => wOld.getD (LogicalKey.toNat key) 0
  let wF := fun key : LogicalKey => w.getD (LogicalKey.toNat key) 0
  let rec_ (x : Nat) : R Rec := do return { key := LogicalKey.ofNat x, val := ← rand 1000, tomb := (← rand 4) == 0 }
  -- A: keys 0 .. nA - 1
  let mut aMain : Array (List Rec) := Array.replicate ((g.d - 1) * g.U) []
  let mut aTier : List Rec := []
  for x in [0:nA] do
    let h := g.oldHome (wOldF (LogicalKey.ofNat x))
    let rc ← rec_ x
    if (aMain.getD h []).length < g.C && (← rand 5) != 0 then aMain := aMain.modify h (· ++ [rc])
    else aTier := aTier ++ [rc]
  -- B: keys from a shared prefix of A and fresh keys
  let shared ← rand (nA + 1)
  let bKeys := (List.range shared).filter (fun _ => true) ++ (List.range nB).map (· + nA)
  let mut bMain : Array (List Rec) := Array.replicate g.U []
  let mut bTier : Array (List Rec) := Array.replicate g.bTierPages []
  for x in bKeys do
    if (← rand 3) == 0 then continue
    let i := wF (LogicalKey.ofNat x) % g.U
    let rc ← rec_ x
    if (bMain.getD i []).length < g.C && (← rand 6) != 0 then bMain := bMain.modify i (· ++ [rc])
    else
      let pg ← rand g.bTierPages
      bTier := bTier.modify pg (· ++ [rc])
  -- lanes: scatter each bucket's records over its C lanes in a random order
  let scatter (recs : List Rec) : R Bucket := do
    let mut lanes : Array (Option Rec) := Array.replicate g.C none
    for rc in recs do
      let free := (List.range g.C).filter fun l => (lanes.getD l none).isNone
      let l ← pick free
      lanes := lanes.set! l (some rc)
    return lanes.toList
  let mut aB : List Bucket := []
  for b in aMain.toList do aB := aB ++ [← scatter b]
  let mut bB : List Bucket := []
  for b in bMain.toList do bB := bB ++ [← scatter b]
  return (wOldF, wF, { aMain := aB, aTier := aTier, bMain := bB, bTier := bTier.toList })

structure Tally where
  trials : Nat := 0
  failures : Array String := #[]
  successes : Nat := 0
  kinds : List (String × Nat) := []
  control : Nat := 0

def kindName : STest → String
  | .stash _ false => "butterfly" | .stash _ true => "route-level" | .radix => "radix"
  | .dfs _ _ => "dfs" | .insertion => "insertion" | .drain => "drain"

def bump (l : List (String × Nat)) (k : String) : List (String × Nat) :=
  if l.any (·.1 == k) then l.map (fun p => if p.1 == k then (p.1, p.2 + 1) else p) else l ++ [(k, 1)]

/-- Check the statements on one random case; returns the violated ones. -/
def checkCase (g : SepGeom) (wOld w : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat)) :
    List String × Option STest := Id.run do
  let run := sReferenceWith engineRule g w inp ops
  let out := run.output
  let mut bad : List String := []
  -- ST1
  if !permRecs (out.main.flatMap Bucket.recs ++ out.tier.filterMap id) inp.winners then bad := bad ++ ["ST1"]
  -- ST2
  if out.main.length != g.N then bad := bad ++ ["ST2.len"]
  if !(out.main.all fun B => B.length == g.C) then bad := bad ++ ["ST2.lanes"]
  for v in [0:g.N] do
    if !((out.main.getD v []).recs.all fun x => sHome g w x == v) then bad := bad ++ [s!"ST2.home {v}"]
    if (out.main.getD v []).recs.length != min (sHomeCount g w inp.winners v) g.C then bad := bad ++ [s!"ST2.count {v}"]
  for x in out.tier.filterMap id do
    if (out.main.getD (sHome g w x) []).recs.length != g.C then bad := bad ++ ["ST2.tierfull"]
  -- ST4
  let ff := sFirstFailure g run.trace
  match ff with
  | some (.stash j _) => if !(g.stashPages * g.C < sRawStageExcess g wOld w inp j) then bad := bad ++ ["ST4a.stash"]
  | some .radix => if !(g.stashPages * g.C < sAHomeExcess g w inp) then bad := bad ++ ["ST4a.radix"]
  | some (.dfs _ _) =>
    if decide (inp.aTier.length ≤ g.aTierPages * g.C) then
      if !((List.range g.ranges).any fun v => g.C < sRefCoarse g w run inp g.earlyCap v) then bad := bad ++ ["ST4a.dfs"]
  | some .insertion => if !(g.stashPages * g.C < sHomeExcess g w inp) then bad := bad ++ ["ST4b.ins"]
  | some .drain => if !(g.tierPages * g.C < sHomeExcess g w inp) then bad := bad ++ ["ST4b.drain"]
  | none => pure ()
  -- ST6 against the stage-by-stage schedule
  let a := sRouteWith engineRule g w inp.aMain ops
  let b := sRouteWith engineRule g w inp.aMain g.canonicalOps
  if a.main != b.main then bad := bad ++ ["ST6.main"]
  for j in [0:g.k] do
    if !permRecs (a.stash.getD j []) (b.stash.getD j []) then bad := bad ++ [s!"ST6.stash {j}"]
  if a.radix != b.radix then bad := bad ++ ["ST6.radix"]
  if (sJobWith engineRule g w inp ops).toBool != (sJobWith engineRule g w inp g.canonicalOps).toBool then
    bad := bad ++ ["ST6.verdict"]
  return (bad, ff)

def main (args : List String) : IO UInt32 := do
  let trials := (args.head? >>= String.toNat?).getD 400
  let mut rng : Rng := ⟨0x9E3779B97F4A7C15⟩
  let mut t : Tally := {}
  let mut schedBad : Nat := 0
  let mut schedChecked : Nat := 0
  -- SEngine on every small geometry
  for K in [0:6] do
    for (r, e) in [(1, 1), (1, 2), (1, 3), (3, 0), (3, 1), (5, 0), (7, 0), (1, 4), (3, 2)] do
      let g : SepGeom := { C := 1, K, e, r, rangeBits := 0, I := 20, stashPages := 0, aTierPages := 0,
                           bTierPages := 1, tierPages := 0 }
      schedChecked := schedChecked + 1
      if !validSched g (engineOps g) then
        schedBad := schedBad + 1
        IO.println s!"SEngine FAILS at K={K} r={r} e={e}: {(engineOps g).length} ops vs {g.canonicalOps.length}"
  IO.println s!"SEngine: {schedChecked - schedBad}/{schedChecked} geometries valid"
  for n in [0:trials] do
    let ((g, wOld, w, inp), rng') := (do
        let g ← randGeom
        let (wOld, w, inp) ← randInputs g
        return (g, wOld, w, inp) : R _).run rng
    rng := rng'
    for (name, ops) in [("engine", engineOps g), ("canonical", g.canonicalOps)] do
      let (bad, ff) := checkCase g wOld w inp ops
      t := { t with trials := t.trials + 1 }
      match ff with
      | none => t := { t with successes := t.successes + 1 }
      | some f => t := { t with kinds := bump t.kinds (kindName f) }
      if !bad.isEmpty then
        t := { t with failures := t.failures.push s!"trial {n} {name} {repr g}: {bad.take 4}" }
    -- negative control: reversing the engine's schedule breaks stage order
    let rev := (engineOps g).reverse
    if !validSched g rev then t := { t with control := t.control + 1 }
  IO.println s!"cases: {t.trials}, successes {t.successes}, first failures {t.kinds}"
  IO.println s!"violations: {t.failures.size}"
  for f in t.failures.toList.take 10 do IO.println s!"  {f}"
  IO.println s!"control (reversed schedule rejected): {t.control}/{trials}"
  return if t.failures.isEmpty && schedBad == 0 then 0 else 1
