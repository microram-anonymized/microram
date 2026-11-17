import RebuildBound.Oracle.Check
import RebuildBound.Spec.Model.Top

/-!
# Differential test of the top finish

Reads a `top-finish-fixture/0` file written by the top dumper
(`oracle/fixtures-top/fdtop.cpp`), runs the Lean model
`RebuildBound.Model.topJob` on its inputs and compares it with the engine:

* **O1**, on the engine's output and on the model's: main and tier hold the
  resolved live set `W` exactly once (B beats A; a winning tombstone deletes
  its key), with identical value bytes and no tombstone; every main record sits
  at its home `word mod T`; home `v` holds `min(X_v, C)` records and the tier
  `Σ_v (X_v - C)₊`.
* **O2**: the verdict, and on failure the failing test kind against the
  engine's.
* **O3**: lane-exact main (bucket, lane) and tier (index `page · C + lane`).

The engine's unshadowed flag is bit `0x20` of the meta byte, the value's last
byte, so the model runs with `unsh r = r.val.testBit 5`. Core `Lean` and
`Std` only.
-/

open Lean Std

namespace RebuildBound.Oracle.Top

open RebuildBound.Oracle (P Rec parseHex natField strField boolField arrField hexField objField
  isHexString hex16)

structure Geometry where
  C : Nat
  T : Nat
  D : Nat
  U : Nat
  K : Nat
  e : Nat
  rho : Nat
  I : Nat
  dfs : Bool
  rPages : Nat
  bPages : Nat
  mergePages : Nat
  tierPages : Nat
  deriving Repr

structure Fixture where
  geometry : Geometry
  cMain : Array Rec
  carry : Array Rec
  bMain : Array Rec
  bTier : Array Rec
  words : Array (Nat × Nat)
  verdict : String
  kind : String
  message : String
  main : Array Rec
  tier : Array Rec

/-- A record whose position field is `pos` (`bucket` or `page`). -/
def parseRecAt (pos : String) (ctx : String) (j : Json) : P Rec := do
  let value := (← strField j ctx "value").toLower
  if !(isHexString value) || value.length % 2 != 0 || value.isEmpty then
    throw s!"{ctx}.value: expected a non-empty even-length hex string"
  return {
    bucket := ← natField j ctx pos
    lane := ← natField j ctx "lane"
    key := ← hexField j ctx "key"
    value := value
    tombstone := ← boolField j ctx "tombstone" }

def parseRecsAt (pos ctx : String) (j : Json) (k : String) : P (Array Rec) := do
  let arr ← arrField j ctx k
  let mut out := #[]
  for h : i in [0:arr.size] do
    out := out.push (← parseRecAt pos s!"{ctx}.{k}[{i}]" arr[i])
  return out

def parseGeometry (j : Json) : P Geometry := do
  let ctx := "geometry"
  return {
    C := ← natField j ctx "bucket_capacity"
    T := ← natField j ctx "T"
    D := ← natField j ctx "D"
    U := ← natField j ctx "U"
    K := ← natField j ctx "K"
    e := ← natField j ctx "e"
    rho := ← natField j ctx "range_bits"
    I := ← natField j ctx "range_index_bits"
    dfs := (← natField j ctx "dfs") != 0
    rPages := ← natField j ctx "r_pages"
    bPages := ← natField j ctx "b_tier_pages"
    mergePages := ← natField j ctx "merge_stash_pages"
    tierPages := ← natField j ctx "out_tier_pages" }

def parseFixture (text : String) : P Fixture := do
  let j ← Json.parse text
  let format ← strField j "fixture" "format"
  if format != "top-finish-fixture/0" then
    throw s!"unsupported fixture format \"{format}\" (want \"top-finish-fixture/0\")"
  let inp ← objField j "fixture" "inputs"
  let out ← objField j "fixture" "outputs"
  let ws ← arrField j "fixture" "words"
  let mut words := #[]
  for h : i in [0:ws.size] do
    words := words.push (← hexField ws[i] s!"words[{i}]" "key", ← hexField ws[i] s!"words[{i}]" "word")
  let verdict ← strField out "outputs" "verdict"
  if verdict != "success" && verdict != "failure" then
    throw s!"outputs.verdict: expected \"success\" or \"failure\", got \"{verdict}\""
  return {
    geometry := ← parseGeometry (← objField j "fixture" "geometry")
    cMain := ← parseRecsAt "bucket" "inputs" inp "C_main"
    carry := ← parseRecsAt "page" "inputs" inp "R"
    bMain := ← parseRecsAt "bucket" "inputs" inp "B_main"
    bTier := ← parseRecsAt "page" "inputs" inp "B_tier"
    words := words
    verdict := verdict
    kind := ← strField out "outputs" "kind"
    message := ← strField out "outputs" "message"
    main := ← parseRecsAt "bucket" "outputs" out "main"
    tier := ← parseRecsAt "page" "outputs" out "tier" }

/-! ### The model on a fixture -/

def toModelRec (r : Rec) : Model.Rec :=
  { key := Model.LogicalKey.ofNat r.key, val := (parseHex r.value).toOption.getD 0, tomb := r.tombstone }

/-- Lane arrays of `n` buckets of `c` lanes; `none` if a record is out of range
or two records share a position. -/
def toBuckets (n c : Nat) (recs : Array Rec) : Option (List Model.Bucket) := do
  let mut arr : Array (Array (Option Model.Rec)) := Array.replicate n (Array.replicate c none)
  for r in recs do
    if r.bucket ≥ n || r.lane ≥ c then failure
    if (arr[r.bucket]!)[r.lane]!.isSome then failure
    arr := arr.modify r.bucket fun b => b.set! r.lane (some (toModelRec r))
  return arr.toList.map (·.toList)

/-- Records in storage order (page or bucket, then lane). -/
def sortedRecs (recs : Array Rec) : List Model.Rec :=
  (recs.qsort fun a b => a.bucket < b.bucket || (a.bucket == b.bucket && a.lane < b.lane)).toList.map
    toModelRec

/-- `log2` of a power of two, or `none`. -/
def log2? (n : Nat) : Option Nat :=
  let l := n.log2
  if 2 ^ l == n then some l else none

def modelGeom (fx : Fixture) : Option Model.TopGeom := do
  let g := fx.geometry
  let k ← log2? g.U
  let e ← log2? g.D
  if g.T != g.D * g.U || k != g.K || e != g.e then failure
  return { C := g.C, k := k, e := e, rho := g.rho, I := g.I, dfs := g.dfs, rPages := g.rPages,
           bPages := g.bPages, mergePages := g.mergePages, tierPages := g.tierPages }

/-- Position faults of a store of `n` buckets (or pages) of `c` lanes: a record
outside the store, or two records in one position. A fixture's coordinates are
checked before anything is flattened or keyed by them. -/
def positionFaults (name : String) (n c : Nat) (recs : Array Rec) : Array String := Id.run do
  let mut seen : HashSet (Nat × Nat) := {}
  let mut out := #[]
  for r in recs do
    if r.bucket ≥ n || r.lane ≥ c then
      out := out.push s!"{name}: key {hex16 r.key} at ({r.bucket}, {r.lane}) is outside {n} x {c}"
    else if seen.contains (r.bucket, r.lane) then
      out := out.push s!"{name}: position ({r.bucket}, {r.lane}) is occupied twice"
    seen := seen.insert (r.bucket, r.lane)
  return out

/-- Position faults of the four input stores. -/
def inputFaults (fx : Fixture) : Array String :=
  let g := fx.geometry
  positionFaults "C_main" g.T g.C fx.cMain ++ positionFaults "R" g.rPages g.C fx.carry ++
    positionFaults "B_main" g.U g.C fx.bMain ++ positionFaults "B_tier" g.bPages g.C fx.bTier

/-- Position faults of an output: main buckets and output-tier pages. -/
def outputFaults (fx : Fixture) (main tier : Array Rec) : Array String :=
  let g := fx.geometry
  positionFaults "main" g.T g.C main ++ positionFaults "tier" g.tierPages g.C tier

def modelInputs (fx : Fixture) : Option Model.TopInputs := do
  let g := fx.geometry
  if !(inputFaults fx).isEmpty then failure
  return { cMain := ← toBuckets g.T g.C fx.cMain
           carry := sortedRecs fx.carry
           bMain := ← toBuckets g.U g.C fx.bMain
           bTier := sortedRecs fx.bTier }

def wordMap (fx : Fixture) : HashMap Nat Nat := Id.run do
  let mut m : HashMap Nat Nat := {}
  for (k, w) in fx.words do m := m.insert k w
  return m

/-- The engine's unshadowed flag: bit `0x20` of the value's last (meta) byte. -/
def engineUnsh (r : Model.Rec) : Bool := r.val.testBit 5

inductive ModelResult where
  | ok (out : Model.Output)
  | fail (t : Model.Test)
  | badInput

def runModel (fx : Fixture) : ModelResult :=
  match modelGeom fx, modelInputs fx with
  | some g, some inp =>
    let ws := wordMap fx
    match Model.topJob g engineUnsh (fun k => ws.getD (Model.LogicalKey.toNat k) 0) inp with
    | .ok o => .ok o
    | .error t => .fail t
  | _, _ => .badInput

def testKind : Model.Test → String
  | .stash _ => "butterfly"
  | .dfs _ _ => "residual-dfs-partition"
  | .insertion => "fixed-merge-offers"
  | .drain => "residual-drain"

def testDetail : Model.Test → String
  | .stash j => s!"stash(bit {j})"
  | .dfs d p => s!"dfs(depth {d}, pre {p})"
  | .insertion => "merge-stash"
  | .drain => "drain"

/-- Model output as fixture records; the tier as (page, lane). -/
def outRecs (valueBytes c : Nat) (o : Model.Output) : Array Rec × Array Rec := Id.run do
  let mk (b l : Nat) (r : Model.Rec) : Rec :=
    let s := String.ofList (Nat.toDigits 16 r.val)
    { bucket := b, lane := l, key := Model.LogicalKey.toNat r.key, tombstone := r.tomb
      value := "".pushn '0' (2 * valueBytes - s.length) ++ s }
  let mut main := #[]
  for b in o.main, bi in [0:o.main.length] do
    for s in b, li in [0:b.length] do
      if let some r := s then main := main.push (mk bi li r)
  let mut tier := #[]
  for s in o.tier, ti in [0:o.tier.length] do
    if let some r := s then tier := tier.push (mk (ti / c) (ti % c) r)
  return (main, tier)

/-! ### O1: the resolved live set -/

/-- The resolved live winners of the fixture's inputs, by key: B beats A, and
a winning tombstone deletes its key. Returns `(key ↦ (value, tombstone))` of
the winners and the set of live keys. -/
def liveSet (fx : Fixture) : HashMap Nat Rec := Id.run do
  let mut win : HashMap Nat Rec := {}
  for r in fx.cMain ++ fx.carry do win := win.insert r.key r
  for r in fx.bMain ++ fx.bTier do win := win.insert r.key r
  let mut live : HashMap Nat Rec := {}
  for (k, r) in win.toList do
    if !r.tombstone then live := live.insert k r
  return live

/-- O1 violations of an output (`main` by bucket, `tier` records). -/
def checkO1 (fx : Fixture) (main tier : Array Rec) (limit : Nat := 8) : Nat × Array String := Id.run do
  let g := fx.geometry
  let ws := wordMap fx
  let live := liveSet fx
  let mut n := 0
  let mut out : Array String := #[]
  let note (n : Nat) (out : Array String) (s : String) : Nat × Array String :=
    (n + 1, if out.size < limit then out.push s else out)
  for f in outputFaults fx main tier do
    (n, out) := note n out f
  let mut seen : HashMap Nat Nat := {}
  let mut mainCount : HashMap Nat Nat := {}
  for r in main do
    if r.bucket != (ws.getD r.key 0) % g.T then
      (n, out) := note n out s!"main record {hex16 r.key} in bucket {r.bucket}, home {(ws.getD r.key 0) % g.T}"
    mainCount := mainCount.insert r.bucket (mainCount.getD r.bucket 0 + 1)
  for r in main ++ tier do
    seen := seen.insert r.key (seen.getD r.key 0 + 1)
    match live.get? r.key with
    | none => (n, out) := note n out s!"output record {hex16 r.key} is not a live winner"
    | some w =>
      if w.value != r.value || r.tombstone then
        (n, out) := note n out s!"output record {hex16 r.key} differs from its winner"
  for (k, _) in live.toList do
    let c := seen.getD k 0
    if c != 1 then (n, out) := note n out s!"live key {hex16 k} appears {c} times"
  -- counts: home v keeps min(X_v, C); the tier holds the excess
  let mut X : HashMap Nat Nat := {}
  for (k, _) in live.toList do
    let v := (ws.getD k 0) % g.T
    X := X.insert v (X.getD v 0 + 1)
  let mut excess := 0
  for (v, x) in X.toList do
    excess := excess + (x - g.C)
    if mainCount.getD v 0 != min x g.C then
      (n, out) := note n out s!"home {v}: {mainCount.getD v 0} main records, X_v = {x}"
  if tier.size != excess then
    (n, out) := note n out s!"tier holds {tier.size} records, excess {excess}"
  return (n, out)

/-! ### O3: lane-exact comparison -/

def compareOutputs (fx : Fixture) (mm mt : Array Rec) (limit : Nat := 8) : Nat × Array String := Id.run do
  let show_ (r : Rec) := s!"key {hex16 r.key} val {r.value}{if r.tombstone then " tomb" else ""}"
  let mut n := 0
  let mut out : Array String := #[]
  let note (n : Nat) (out : Array String) (s : String) : Nat × Array String :=
    (n + 1, if out.size < limit then out.push s else out)
  -- The engine's coordinates must be valid before they are compared.
  for f in outputFaults fx fx.main fx.tier do
    (n, out) := note n out s!"engine {f}"
  let mut em : HashMap (Nat × Nat) Rec := {}
  for r in fx.main do em := em.insert (r.bucket, r.lane) r
  let mut mo : HashMap (Nat × Nat) Rec := {}
  for r in mm do mo := mo.insert (r.bucket, r.lane) r
  for r in fx.main do
    match mo.get? (r.bucket, r.lane) with
    | none => (n, out) := note n out s!"main (b{r.bucket},l{r.lane}): engine {show_ r}, model empty"
    | some q =>
      if q.key != r.key || q.value != r.value || q.tombstone != r.tombstone then
        (n, out) := note n out s!"main (b{r.bucket},l{r.lane}): engine {show_ r}, model {show_ q}"
  for q in mm do
    if !(em.contains (q.bucket, q.lane)) then
      (n, out) := note n out s!"main (b{q.bucket},l{q.lane}): engine empty, model {show_ q}"
  -- The tier by (page, lane); `outRecs` gives the model's tier in the same form.
  let mut et : HashMap (Nat × Nat) Rec := {}
  for r in fx.tier do et := et.insert (r.bucket, r.lane) r
  let mut mot : HashMap (Nat × Nat) Rec := {}
  for r in mt do mot := mot.insert (r.bucket, r.lane) r
  for r in fx.tier do
    match mot.get? (r.bucket, r.lane) with
    | none => (n, out) := note n out s!"tier (p{r.bucket},l{r.lane}): engine {show_ r}, model empty"
    | some q =>
      if q.key != r.key || q.value != r.value || q.tombstone != r.tombstone then
        (n, out) := note n out s!"tier (p{r.bucket},l{r.lane}): engine {show_ r}, model {show_ q}"
  for q in mt do
    if !(et.contains (q.bucket, q.lane)) then
      (n, out) := note n out s!"tier (p{q.bucket},l{q.lane}): engine empty, model {show_ q}"
  return (n, out)

/-! ### The input contract -/

/-- The clauses of `TopShape` that the fixture's inputs break (empty when the
inputs meet the contract). Lane counts hold by construction of `toBuckets`. -/
def shapeViolations (g : Model.TopGeom) (w : Model.LogicalKey → Nat) (inp : Model.TopInputs) : List String :=
  Id.run do
  let mut bad : List String := []
  let nodup (l : List Model.LogicalKey) : Bool := Id.run do
    let mut seen : HashSet Model.LogicalKey := {}
    for x in l do
      if seen.contains x then return false
      seen := seen.insert x
    return true
  let home := fun (r : Model.Rec) => w r.key % g.T
  if inp.cMain.length != g.T || inp.bMain.length != g.U then bad := bad ++ ["lengths"]
  if !nodup (inp.aAll.map (·.key)) then bad := bad ++ ["aNodup"]
  if !nodup (inp.bAll.map (·.key)) then bad := bad ++ ["bNodup"]
  if !((List.range g.T).all fun v => (Model.Bucket.recs (inp.cMain.getD v [])).all (home · == v)) then
    bad := bad ++ ["cHome"]
  if !((List.range g.U).all fun i =>
      (Model.Bucket.recs (inp.bMain.getD i [])).all fun r => w r.key % g.U == i) then
    bad := bad ++ ["bHome"]
  if !(inp.carry.all fun r => (Model.Bucket.recs (inp.cMain.getD (home r) [])).length == g.C) then
    bad := bad ++ ["carryFull"]
  let liveC := ((inp.cMain.flatMap Model.Bucket.recs).filter (!·.tomb)).map (·.key)
  if !(inp.bTier.all fun r => !(Model.earlyDrop engineUnsh r && liveC.contains r.key)) then
    bad := bad ++ ["tierUnsh"]
  return bad

/-- The value width in bytes, read off the fixture's records. -/
def valueBytes (fx : Fixture) : Nat :=
  match (fx.cMain ++ fx.carry ++ fx.bMain ++ fx.bTier).toList.head? with
  | some r => r.value.length / 2
  | none => 8

/-- Run the differential test on a parsed fixture: the JSON fields of its
report line and whether everything passed. -/
def run (fx : Fixture) : List (String × Json) × Bool :=
  match runModel fx with
  | .badInput => ([("o2", "fail"), ("model", "bad-input"),
      ("input_faults", toJson ((inputFaults fx).toList.take 8))], false)
  | .fail t =>
    if fx.verdict == "failure" then
      let km := testKind t == fx.kind
      ([("o1", "skipped"), ("o2", "pass"), ("engine_kind", toJson fx.kind),
        ("model_kind", toJson (testKind t)), ("model_test", toJson (testDetail t)),
        ("kind", if km then "match" else "mismatch"), ("o3", "skipped")], km)
    else
      ([("o2", "fail"), ("engine", "success"), ("model", "failure"),
        ("model_kind", toJson (testKind t)), ("model_test", toJson (testDetail t))], false)
  | .ok o =>
    if fx.verdict == "failure" then
      ([("o2", "fail"), ("engine", "failure"), ("engine_kind", toJson fx.kind),
        ("model", "success")], false)
    else
      let (mm, mt) := outRecs (valueBytes fx) fx.geometry.C o
      let (ne, ve) := checkO1 fx fx.main fx.tier
      let (nm, vm) := checkO1 fx mm mt
      let (nd, diffs) := compareOutputs fx mm mt
      let ws := wordMap fx
      let premise := match modelGeom fx, modelInputs fx with
        | some g, some inp => shapeViolations g (fun k => ws.getD (Model.LogicalKey.toNat k) 0) inp
        | _, _ => ["geometry"]
      -- O1 is the contract's conclusion: it applies only to inputs meeting `TopShape`.
      let (ne, nm) := if premise.isEmpty then (ne, nm) else (0, 0)
      let o1 : List (String × Json) :=
        if !premise.isEmpty then [("o1", "premise"), ("premise_broken", toJson premise)]
        else if ne == 0 then [("o1", "pass")] else [("o1", "fail"), ("o1_violations", toJson ve)]
      let o1m : List (String × Json) :=
        if !premise.isEmpty then [("o1_model", "premise")]
        else if nm == 0 then [("o1_model", "pass")]
        else [("o1_model", "fail"), ("o1_model_violations", toJson vm)]
      let o3 : List (String × Json) :=
        if nd == 0 then [("o3", "pass")] else [("o3", "fail"), ("diff_count", toJson nd), ("diff", toJson diffs)]
      let sizes : List (String × Json) :=
        [("o2", "pass"), ("tier", toJson fx.tier.size), ("main", toJson fx.main.size)]
      (o1 ++ o1m ++ sizes ++ o3,
        ne == 0 && nm == 0 && nd == 0)

end RebuildBound.Oracle.Top
