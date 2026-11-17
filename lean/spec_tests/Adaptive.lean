import RebuildBound.Spec.Adaptive

/-!
# The adaptive interaction on a tiny instance (smoke test of `Spec/Model/Adaptive.lean`)

The instance of `spec_tests/OnlineBatch.lean` (a prefix is 32 slots) on the
synchronous schedule, with a public shape that mixes scalar probes, blind
writes and chunks of 1 to 12 lanes. The client hashes the buckets of its two latest
rows into its next keys (24 keys, so lanes repeat keys and chunks hold
duplicates) and tombstone bits. Checks, for two word functions:

* the interaction evaluates, and its run has the shape's widths and pattern;
* the transcripts differ, and so do the runs: the client adapts;
* the replay identity on this instance: the run issued is the replay of the
  transcript, and the replay's view is the transcript;
* a client that ignores its rows issues the same run under both words.

    lake env lean --run spec_tests/Adaptive.lean
-/

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online
open RebuildBound.Model.OnlineBatch RebuildBound.Model.Adaptive RebuildBound.Spec

def cfg : Config :=
  { fanouts := [2], carry1 := 16, topDigit := 1, load := 2, horizon := 4096, initialized := false }
def top : TopGeom :=
  { C := 64, k := 5, e := 0, rho := 0, I := 5, dfs := false, rPages := 1, bPages := 1,
    mergePages := 1, tierPages := 1 }
def prep : TPGeom :=
  { C := 64, k := 5, stashPages := 1, aTierPages := 1, drainPages := 1, rangeBits := 0, I := 5,
    dfs := false }
def sh : Shapes := ⟨selectedDirectGeometry, fun _ _ => selectedDirectSep 2, top, prep, prep⟩
def g : OnlineGeom := ⟨8, 4⟩
abbrev m0 : Nat := 4

def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A public shape of `n` operations. -/
def shape (n : Nat) : List Kind := Id.run do
  let mut s := 4242
  let mut out := #[]
  for _ in [0:n] do
    s := lcg s
    let kind := s / 2 ^ 10 % 5
    out := out.push (if kind < 2 then .chunk (s / 2 ^ 30 % 12 + 1)
      else if kind == 2 then .blind else .probe)
  return out.toList

/-- A digest of the two latest rows and the row count. Rows are closures over
the interaction, so a client that read every row would recompute them all. -/
def digest (rows : List (Fin m0 → Nat)) : Nat :=
  (rows.drop (rows.length - 2)).foldl
    (fun h r => (List.finRange m0).foldl (fun h i => lcg (h + r i)) h) (7 + rows.length)

/-- Keys and tombstone bits from the digest of the observed rows. -/
def client : Client m0 := fun rows i =>
  let h := lcg (digest rows + 1000003 * i)
  ⟨LogicalKey.ofNat (h / 2 ^ 40 % 24 + 1), 1000 * rows.length + i, h / 2 ^ 20 % 5 == 0⟩

/-- A client that reads only how many rows it has seen. -/
def constClient : Client m0 := fun rows i =>
  let h := lcg (rows.length * 7919 + 1000003 * i)
  ⟨LogicalKey.ofNat (h / 2 ^ 40 % 24 + 1), 1000 * rows.length + i, h / 2 ^ 20 % 5 == 0⟩

def adv : AdaptiveRun m0 := ⟨shape 60, [], fun _ => false, client⟩
def advConst : AdaptiveRun m0 := ⟨shape 60, [], fun _ => false, constClient⟩
def w1 : Words := fun ℓ v k => lcg (LogicalKey.toNat k * 1000003 + ℓ * 7919 + v * 104729)
def w2 : Words := fun ℓ v k => lcg (lcg (LogicalKey.toNat k + 17 * ℓ + 31 * v))
def d1 : Nat → Nat → Nat := fun t i => lcg (t * 31 + i)
def S : Schedule := syncSchedule cfg

def keysOf (run : BatchRun) : List LogicalKey := (slots run).map fun s => s.record.key

/-- The rows of a transcript, evaluated once (`transcript` reruns the
interaction at every entry). -/
def rowTable (n : Nat) (t : Fin n → Fin m0 → Nat) : Array (Array Nat) :=
  ((List.finRange n).map fun s => ((List.finRange m0).map fun i => t s i).toArray).toArray

/-- A transcript read from evaluated rows. -/
def ofTable (n : Nat) (rows : Array (Array Nat)) : Fin n → Fin m0 → Nat :=
  fun t i => (rows.getD t #[]).getD i 0

def main : IO Unit := do
  let n := slotCount adv.shape
  let (ops1, rows1) := interact cfg sh g S adv w1 d1
  let (ops2, rows2) := interact cfg sh g S adv w2 d1
  let r1 : BatchRun := ⟨ops1, adv.init, adv.unsh⟩
  let r2 : BatchRun := ⟨ops2, adv.init, adv.unsh⟩
  let a1 := (rows1.map fun r => ((List.finRange m0).map r).toArray).toArray
  let a2 := (rows2.map fun r => ((List.finRange m0).map r).toArray).toArray
  let t1 := ofTable n a1
  let t2 := ofTable n a2
  -- `transcript` and `realized` on a few entries, against the evaluated rows
  let defsOk := rows1.length == n && keysOf (realized cfg sh g S adv w1 d1) == keysOf r1 &&
    [0, n / 2, n - 1].all fun t => (List.range m0).all fun i =>
      if h : t < n ∧ i < m0 then
        transcript cfg sh g S adv n w1 d1 ⟨t, h.1⟩ ⟨i, h.2⟩ == (a1.getD t #[]).getD i 0
      else true
  let shapeOk := OnlineBatch.widths r1 == shapeWidths adv.shape &&
    (List.range n).all fun t => OnlineBatch.probePattern r1 t == shapePattern adv.shape t
  let adapts := a1 != a2 && keysOf r1 != keysOf r2
  let dups := ((slots r1).filter (OnlineBatch.duplicate r1)).length
  let replay1 := keysOf (replay adv t1) == keysOf r1 &&
    rowTable n (OnlineBatch.view cfg sh g (replay adv t1) S n m0 w1 d1) == a1
  let replay2 := keysOf (replay adv t2) == keysOf r2 &&
    rowTable n (OnlineBatch.view cfg sh g (replay adv t2) S n m0 w2 d1) == a2
  let (opsC1, rowsC1) := interact cfg sh g S advConst w1 d1
  let (opsC2, _) := interact cfg sh g S advConst w2 d1
  let c1 : BatchRun := ⟨opsC1, [], fun _ => false⟩
  let constOk := keysOf c1 == keysOf ⟨opsC2, [], fun _ => false⟩ &&
    (rowsC1.map fun r => ((List.finRange m0).map r).toArray).toArray ==
      rowTable n (OnlineBatch.view cfg sh g c1 S n m0 w1 d1)
  IO.println s!"definitions {defsOk}"
  IO.println s!"ops {adv.shape.length}, slots {n}, duplicate lanes {dups}, shape {shapeOk}"
  IO.println s!"adapts {adapts}, replay {replay1 && replay2}, constant client {constOk}"
  if !(defsOk && shapeOk && adapts && replay1 && replay2 && constOk && dups > 0) then
    IO.println "FAIL"
    IO.Process.exit 1
  IO.println "OK"
