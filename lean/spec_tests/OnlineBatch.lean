import RebuildBound.Spec.ObliviousBatch

/-!
# The batch model on a tiny instance (smoke test of `Spec/Model/OnlineBatch.lean`)

The instance of `spec_tests/Online.lean` (a prefix is 32 slots) with a seeded
mix of scalar operations and chunks of 1 to 12 lanes over 24 keys (so chunks
repeat keys and straddle prefix boundaries), on the synchronous schedule.
Checks, for two word functions: duplicate lanes are all dummy; at most one
real probe per (family, key); the pattern is the same under both; the
requester never loses a lane (one unit slot per lane). On a run without
chunks the batch view equals the scalar view.

    lake env lean --run spec_tests/OnlineBatch.lean
-/

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online
open RebuildBound.Model.OnlineBatch RebuildBound.Spec

deriving instance Inhabited for RebuildBound.Model.OnlineBatch.Slot

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

def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def mixed (n : Nat) : List OnlineBatch.Op := Id.run do
  let mut s := 4242
  let mut out := #[]
  for j in [0:n] do
    s := lcg s
    let kind := s / 2 ^ 10 % 5
    if kind < 2 then
      let w := s / 2 ^ 30 % 12 + 1
      let mut lanes := #[]
      for l in [0:w] do
        s := lcg s
        lanes := lanes.push ⟨LogicalKey.ofNat (s / 2 ^ 40 % 24 + 1), 1000 * j + l, s / 2 ^ 20 % 5 == 0⟩
      out := out.push (.batch lanes.toList)
    else
      let r : Rec := ⟨LogicalKey.ofNat (s / 2 ^ 40 % 24 + 1), 1000 * j, s / 2 ^ 20 % 5 == 0⟩
      out := out.push (if kind == 2 then .blind r else .probe r)
  return out.toList

def run : BatchRun := ⟨mixed 60, [], fun _ => false⟩
def w1 : Words := fun ℓ v k => lcg (LogicalKey.toNat k * 1000003 + ℓ * 7919 + v * 104729)
def w2 : Words := fun ℓ v k => lcg (lcg (LogicalKey.toNat k + 17 * ℓ + 31 * v))
def S : Schedule := slotSchedule (widths run) (syncSchedule cfg)

/-- The scalar run of `spec_tests/Online.lean`. -/
def scalarOps (n : Nat) : List Online.Op := Id.run do
  let mut s := 12345
  let mut out := #[]
  for j in [0:n] do
    s := lcg s
    let r : Rec := ⟨LogicalKey.ofNat (s / 2 ^ 40 % 40 + 1), j, s / 2 ^ 20 % 5 == 0⟩
    out := out.push (if s / 2 ^ 10 % 7 == 0 then .blind r else .probe r)
  return out.toList
def srun : OnlineRun := ⟨scalarOps 200, [], fun _ => false⟩

def main : IO Unit := do
  let ns := (slots run).length
  let st := OnlineBatch.stateAt g run run.ops.length
  let units := st.frozen.length * g.unitEntries + st.current.length
  IO.println s!"ops {run.ops.length}, slots {ns}, unit slots {units}, chunks straddling a prefix {
    ((List.range ns).filter fun t => t % 32 == 0 && chunkStart (widths run) t != t).length}"
  let mut reals : Array ((Nat × Nat) × LogicalKey) := #[]
  let mut same := true
  let mut dupOk := true
  let mut dups := 0
  for t in [0:ns] do
    let p := S t
    let sl := (slots run)[t]!
    if duplicate run sl then dups := dups + 1
    for i in [0:p.tables.length] do
      let a := OnlineBatch.isReal cfg sh g run (syncSchedule cfg) w1 t i
      let b := OnlineBatch.isReal cfg sh g run (syncSchedule cfg) w2 t i
      if a != b then same := false
      if a && duplicate run sl then dupOk := false
      if a then
        let c := p.tables[i]!
        reals := reals.push (familyOf cfg c.1 c.2, sl.record.key)
  let distinct := reals.toList.eraseDups.length == reals.size
  IO.println s!"duplicate lanes {dups}, real probes {reals.size}, distinct {distinct}, word-free {same}"
  -- the scalar model is the batch model without chunks
  let d : Nat → Nat → Nat := fun j i => lcg (j * 31 + i)
  let n := srun.ops.length
  let bv := OnlineBatch.view cfg sh g (ofScalar srun) (syncSchedule cfg) n 4 w1 d
  let sv := Online.view cfg sh g srun (syncSchedule cfg) n 4 w1 d
  let scalarSame := (List.finRange n).all fun j => (List.finRange 4).all fun i => bv j i == sv j i
  IO.println s!"scalar view agrees {scalarSame}"
  if !(units == ns && distinct && same && dupOk && scalarSame && dups > 0) then
    IO.println "FAIL"
    IO.Process.exit 1
  IO.println "OK"
