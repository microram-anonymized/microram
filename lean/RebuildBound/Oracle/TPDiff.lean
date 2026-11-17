import RebuildBound.Oracle.Fixture
import RebuildBound.Spec.Model.TopPrep

/-!
# Differential test of the top preparation and the initialization route (`--tp`)

Reads a `top-prep-fixture/0` or `top-init-fixture/0` file (written by the
`fdtp` / `fdtp_engine` dumpers, see `oracle/fixtures-tp/`), runs the Lean
model `RebuildBound.Model.tpJob` (preparation) or `initJob` (initialization),
both under `engineRule`, and compares it with the engine:

* **O2**: the verdict, and on failure the failing test's kind (`.stash j` with
  `j < k - 1` is `butterfly`, `.stash (k - 1)` is `butterfly-offers`, `.dfs _ _`
  is `residual-dfs-partition`, `.drain` is `residual-drain`; the DFS node itself
  is not compared).
* **O3** on success: lane-exact main (bucket, lane, record) and drain target
  (the preparation's `R` or the initialization's published tier, by
  `page * C + lane`); for an initialization also the scatter `initMain` when
  recorded. Public-engine fixtures omit that intermediate observation and
  report `scatter: skipped`.
* **O1** (light), on the engine's output and on the model's: the output is a
  permutation of the input records minus the flagged tombstones, and every main
  record sits at bucket `w key % T`.

The engine's unshadowed flag is bit `0x20` of the value's last (meta) byte, so
the model runs with `unsh r = r.val.testBit 5`; the fixture's `unshadowed`
fields must agree. A record's `val` is the whole value hex read as a number.
Core `Lean` and `Std` only.
-/

open Lean Std

namespace RebuildBound.Oracle.TP

open RebuildBound.Oracle (P parseHex natField strField boolField arrField hexField objField
  isHexString)

/-- One fixture record: position, lane, key, value (as a number), flags. -/
structure XRec where
  pos : Nat
  lane : Nat
  key : Nat
  val : Nat
  tomb : Bool
  unsh : Bool

def XRec.toModel (r : XRec) : Model.Rec := { key := Model.LogicalKey.ofNat r.key, val := r.val, tomb := r.tomb }

/-- The engine's unshadowed flag: bit `0x20` of the meta byte (the last byte). -/
def engineUnsh (r : Model.Rec) : Bool := r.val.testBit 5

def parseVal (ctx : String) (s : String) : P Nat := do
  let s := s.toLower
  if !(isHexString s) || s.length % 2 != 0 || s.isEmpty then
    throw s!"{ctx}.value: expected a non-empty even-length hex string"
  parseHex s

/-- A record whose position field is `pos` (`bucket` or `page`). -/
def parseX (pos ctx : String) (j : Json) : P XRec := do
  let val ← parseVal ctx (← strField j ctx "value")
  let tomb ← boolField j ctx "tombstone"
  let unsh ← boolField j ctx "unshadowed"
  return { pos := ← natField j ctx pos, lane := ← natField j ctx "lane",
           key := ← hexField j ctx "key", val, tomb, unsh }

def parseXs (pos ctx : String) (j : Json) (k : String) : P (Array XRec) := do
  let arr ← arrField j ctx k
  let mut out := #[]
  for h : i in [0:arr.size] do
    out := out.push (← parseX pos s!"{ctx}.{k}[{i}]" arr[i])
  return out

structure Geom where
  C : Nat
  T : Nat
  k : Nat
  stash : Nat
  aTier : Nat
  drain : Nat
  rho : Nat
  I : Nat
  dfs : Bool
  swept : Nat

def parseGeom (fmt : String) (j : Json) : P Geom := do
  let ctx := "geometry"
  return { C := ← natField j ctx "bucket_capacity", T := ← natField j ctx "T",
           k := ← natField j ctx "block_bits", stash := ← natField j ctx "stage_stash_buckets",
           aTier := ← natField j ctx "a_tier_pages",
           drain := ← natField j ctx (if fmt == "top-prep-fixture/0" then "r_pages" else "out_tier_pages"),
           rho := ← natField j ctx "range_bits", I := ← natField j ctx "range_index_bits",
           dfs := (← natField j ctx "dfs") == 1, swept := ← natField j ctx "pool_swept_buckets" }

def toTPGeom (g : Geom) : Model.TPGeom :=
  { C := g.C, k := g.k, stashPages := g.stash, aTierPages := g.aTier, drainPages := g.drain,
    rangeBits := g.rho, I := g.I, dfs := g.dfs }

/-- Position faults of a store of `n` buckets (or pages) of `c` lanes. -/
def positionFaults (name : String) (n c : Nat) (recs : Array XRec) : Array String := Id.run do
  let mut seen : HashSet (Nat × Nat) := {}
  let mut out := #[]
  for r in recs do
    if r.pos ≥ n || r.lane ≥ c then
      out := out.push s!"{name}: key {r.key} at ({r.pos}, {r.lane}) is outside {n} x {c}"
    else if seen.contains (r.pos, r.lane) then
      out := out.push s!"{name}: position ({r.pos}, {r.lane}) is occupied twice"
    seen := seen.insert (r.pos, r.lane)
  return out

def toBuckets (n c : Nat) (recs : Array XRec) : List Model.Bucket :=
  let arr := recs.foldl (init := Array.replicate n (Array.replicate c (none : Option Model.Rec)))
    fun a r => a.modify r.pos fun b => b.set! r.lane (some r.toModel)
  arr.toList.map (·.toList)

def sortX (recs : Array XRec) : Array XRec :=
  recs.qsort fun a b => a.pos < b.pos || (a.pos == b.pos && a.lane < b.lane)

/-- A record as a comparable tuple. -/
abbrev Tup := Nat × Nat × Nat × Nat × Bool

def Tup.lt (a b : Tup) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 &&
    (a.2.2.1 < b.2.2.1 || (a.2.2.1 == b.2.2.1 && (a.2.2.2.1 < b.2.2.2.1 ||
      (a.2.2.2.1 == b.2.2.2.1 && !a.2.2.2.2 && b.2.2.2.2)))))))

def xTup (r : XRec) : Tup := (r.pos, r.lane, r.key, r.val, r.tomb)

/-- The model's lanes as tuples (position, lane, key, val, tomb), ascending. -/
def laneTups (buckets : List (List (Option Model.Rec))) : List Tup :=
  buckets.zipIdx.flatMap fun (B, b) =>
    B.zipIdx.filterMap fun (o, l) => o.map fun r => (b, l, Model.LogicalKey.toNat r.key, r.val, r.tomb)

/-- The model's drain target (index `page * C + lane`) as tuples. -/
def tierTups (C : Nat) (tier : List (Option Model.Rec)) : List Tup :=
  tier.zipIdx.filterMap fun (o, i) => o.map fun r => (i / C, i % C, Model.LogicalKey.toNat r.key, r.val, r.tomb)

def describe (t : Tup) : String :=
  s!"({t.1},{t.2.1}):key={t.2.2.1},val={t.2.2.2.1},tomb={t.2.2.2.2}"

/-- Number of differences and the first few, between the engine's and the model's tuples. -/
def compareTups (eng mod : Array Tup) (limit : Nat := 6) : Nat × Array String := Id.run do
  let mut n := 0
  let mut shown := #[]
  let mut i := 0
  let mut j := 0
  while i < eng.size || j < mod.size do
    let diff (s : String) : Nat × Array String → Nat × Array String := fun (n, sh) =>
      (n + 1, if sh.size < limit then sh.push s else sh)
    if i < eng.size && j < mod.size then
      let e := eng[i]!
      let m := mod[j]!
      if e == m then i := i + 1; j := j + 1
      else if Tup.lt e m then
        (n, shown) := diff s!"engine-only {describe e}" (n, shown); i := i + 1
      else
        (n, shown) := diff s!"model-only {describe m}" (n, shown); j := j + 1
    else if i < eng.size then
      (n, shown) := diff s!"engine-only {describe eng[i]!}" (n, shown); i := i + 1
    else
      (n, shown) := diff s!"model-only {describe mod[j]!}" (n, shown); j := j + 1
  return (n, shown)

/-- Kind of a failing test, as the engine names it. -/
def testKind (g : Model.TPGeom) : Model.TPTest → String
  | .stash j => if j + 1 < g.k then "butterfly" else "butterfly-offers"
  | .dfs _ _ => "residual-dfs-partition"
  | .drain => "residual-drain"

def testDetail : Model.TPTest → String
  | .stash j => s!"stash {j}"
  | .dfs d p => s!"dfs {d} {p}"
  | .drain => "drain"

/-- Light O1 over a list of output records `(bucket-or-none, key, val, tomb)`: the
records (main then drain) are a permutation of `expected`, and every main record
sits at bucket `w key % T`. Returns the faults. -/
def checkO1 (T : Nat) (w : Nat → Nat) (expected : Array (Nat × Nat × Bool))
    (mainRecs : Array (Nat × Nat × Nat × Bool)) (tierRecs : Array (Nat × Nat × Bool)) :
    Array String := Id.run do
  let mut out := #[]
  for (b, key, _, _) in mainRecs do
    if w key % T != b then
      out := out.push s!"key {key} sits at bucket {b}, its home is {w key % T}"
  let lt (a b : Nat × Nat × Bool) : Bool :=
    a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && !a.2.2 && b.2.2)))
  let got := (mainRecs.map fun (_, k, v, t) => (k, v, t)) ++ tierRecs
  if got.size != expected.size then
    out := out.push s!"{got.size} output records, {expected.size} expected"
  else if (got.qsort lt) != (expected.qsort lt) then
    out := out.push "output is not a permutation of the input minus the flagged tombstones"
  return out

def F (l : List (String × Json)) : List (String × Json) := l

/-- Run one fixture: the JSON fields of the report line and the pass flag, or a
malformed-fixture message. -/
def run (path text : String) : Except String (List (String × Json) × Bool) := do
  let j ← Json.parse text
  let fmt ← strField j "fixture" "format"
  let isPrep := fmt == "top-prep-fixture/0"
  if !isPrep && fmt != "top-init-fixture/0" then
    throw s!"unsupported fixture format \"{fmt}\""
  let g ← parseGeom fmt (← objField j "fixture" "geometry")
  let tg := toTPGeom g
  if !decide tg.Valid then throw "geometry: the model's TPGeom.Valid fails"
  if g.T != 2 ^ g.k then throw s!"geometry: T = {g.T} is not 2^{g.k}"
  if g.swept != tg.poolPages then
    throw s!"geometry: pool_swept_buckets = {g.swept}, the model's pool has {tg.poolPages} pages"
  if g.C == 0 then throw "geometry: bucket_capacity is 0"
  -- words
  let ws ← arrField j "fixture" "words"
  let mut words : HashMap Nat Nat := {}
  for h : i in [0:ws.size] do
    words := words.insert (← hexField ws[i] s!"words[{i}]" "key") (← hexField ws[i] s!"words[{i}]" "word")
  let rawWord : Nat → Nat := fun x => words.getD x 0
  let w : Model.LogicalKey → Nat := fun key => rawWord (Model.LogicalKey.toNat key)
  let out ← objField j "fixture" "outputs"
  let verdict ← strField out "outputs" "verdict"
  if verdict != "success" && verdict != "failure" then
    throw s!"outputs.verdict: expected \"success\" or \"failure\", got \"{verdict}\""
  let engKind ← strField out "outputs" "kind"
  -- inputs
  let mut scatterFaults : Array String := #[]
  let mut scatterChecked := false
  let inputRecs : Array XRec ←
    if isPrep then do
      let inp ← objField j "fixture" "inputs"
      let aMain ← parseXs "bucket" "inputs" inp "A_main"
      let aTier ← parseXs "page" "inputs" inp "A_tier"
      let f := positionFaults "A_main" g.T g.C aMain ++ positionFaults "A_tier" g.aTier g.C aTier
      if !f.isEmpty then throw f[0]!
      pure (aMain ++ aTier)
    else do
      let arr ← arrField j "fixture" "input"
      let mut recs := #[]
      for h : i in [0:arr.size] do
        let ctx := s!"input[{i}]"
        let val ← parseVal ctx ((← strField arr[i] ctx "value") ++ "00")
        recs := recs.push { pos := i, lane := 0, key := ← hexField arr[i] ctx "key", val,
                            tomb := false, unsh := false }
      if recs.size > g.T * (g.C / 2) then throw s!"input has {recs.size} records, more than T * C/2"
      pure recs
  for r in inputRecs do
    if r.unsh != engineUnsh r.toModel then
      throw s!"record key {r.key}: unshadowed flag disagrees with the meta byte"
    if !words.contains r.key then throw s!"key {r.key} has no word"
  -- the model
  let unsh := engineUnsh
  let res : Except Model.TPTest Model.Output ←
    if isPrep then do
      let inp ← objField j "fixture" "inputs"
      let aMain ← parseXs "bucket" "inputs" inp "A_main"
      let aTier ← parseXs "page" "inputs" inp "A_tier"
      pure (Model.tpJob Model.engineRule tg unsh w
        ⟨toBuckets g.T g.C aMain, (sortX aTier).toList.map XRec.toModel⟩)
    else
      pure (Model.initJob Model.engineRule tg w (inputRecs.toList.map XRec.toModel))
  -- scatter check of an initialization
  if !isPrep then
    match j.getObjVal? "scattered" with
    | .error _ => pure ()
    | .ok sc =>
      let sm ← parseXs "bucket" "scattered" sc "main"
      scatterChecked := true
      let mt := laneTups (Model.initMain tg (inputRecs.toList.map XRec.toModel))
      let (n, shown) := compareTups ((sortX sm).map xTup) mt.toArray
      if n != 0 then scatterFaults := shown.push s!"{n} scatter differences"
  let base := F [("file", toJson path), ("job", if isPrep then "top_prepare" else "top_init"),
                 ("engine", toJson verdict), ("engine_kind", toJson engKind)]
  let scat : List (String × Json) :=
    if isPrep then [] else if !scatterChecked then [("scatter", "skipped")]
    else if scatterFaults.isEmpty then [("scatter", "pass")]
    else [("scatter", "fail"), ("scatter_diff", toJson scatterFaults)]
  let scatOk := scatterFaults.isEmpty
  let expected : Array (Nat × Nat × Bool) :=
    (inputRecs.filter fun r => !(r.tomb && engineUnsh r.toModel)).map fun r => (r.key, r.val, r.tomb)
  match verdict, res with
  | "failure", .error t =>
    let km := testKind tg t == engKind
    return (base ++ scat ++ F [("o1", "skipped"), ("o2", "pass"), ("model", "failure"),
      ("model_kind", toJson (testKind tg t)), ("model_test", toJson (testDetail t)),
      ("kind", if km then "match" else "mismatch"), ("o3", "skipped")], km && scatOk)
  | "failure", .ok _ =>
    return (base ++ scat ++ F [("o1", "skipped"), ("o2", "fail"), ("model", "success"),
      ("o3", "skipped")], false)
  | _, .error t =>
    return (base ++ scat ++ F [("o1", "skipped"), ("o2", "fail"), ("model", "failure"),
      ("model_kind", toJson (testKind tg t)), ("model_test", toJson (testDetail t)),
      ("o3", "skipped")], false)
  | _, .ok o =>
    let tierName := if isPrep then "R" else "tier"
    let engMain ← parseXs "bucket" "outputs" out "main"
    let engTier ← parseXs "page" "outputs" out tierName
    let faults := positionFaults "main" g.T g.C engMain ++ positionFaults "tier" g.drain g.C engTier
    let flagFaults := (engMain ++ engTier).filter fun r => r.unsh != engineUnsh r.toModel
    -- O1 on the engine's output and on the model's
    let o1e :=
      if faults.isEmpty then
        checkO1 g.T rawWord expected (engMain.map fun r => (r.pos, r.key, r.val, r.tomb))
          (engTier.map fun r => (r.key, r.val, r.tomb))
      else faults
    let mm := laneTups o.main
    let mt := tierTups g.C o.tier
    let o1m := checkO1 g.T rawWord expected (mm.toArray.map fun t => (t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2))
      (mt.toArray.map fun t => (t.2.2.1, t.2.2.2.1, t.2.2.2.2))
    -- O3
    let (nm, dm) := compareTups ((sortX engMain).map xTup) mm.toArray
    let (nt, dt) := compareTups ((sortX engTier).map xTup) mt.toArray
    let o3 : List (String × Json) :=
      if nm == 0 && nt == 0 && faults.isEmpty && flagFaults.isEmpty then [("o3", "pass")]
      else [("o3", "fail"), ("diff_count", toJson (nm + nt + faults.size + flagFaults.size)),
            ("diff", toJson (faults ++ dm.map ("main: " ++ ·) ++ dt.map ("tier: " ++ ·) ++
              (if flagFaults.isEmpty then #[] else #["unshadowed flag differs from the meta byte"])))]
    let ok := nm == 0 && nt == 0 && faults.isEmpty && flagFaults.isEmpty && o1e.isEmpty &&
      o1m.isEmpty && scatOk
    return (base ++ scat ++
      (if o1e.isEmpty then F [("o1", "pass")] else F [("o1", "fail"), ("violations", toJson o1e)]) ++
      (if o1m.isEmpty then F [("o1_model", "pass")] else F [("o1_model", "fail"), ("model_violations", toJson o1m)]) ++
      F [("o2", "pass"), ("model", "success")] ++ o3 ++
      F [("main", toJson engMain.size), ("tier", toJson engTier.size)], ok)

end RebuildBound.Oracle.TP
