import RebuildBound.Spec.Oblivious

/-!
# The online model on a tiny instance (smoke test of `Spec/Model/Online.lean`)

A two-level configuration (level one with the selected direct geometries at a
reduced load of 2 positions per bucket, so a prefix is 32 operations; a top of
32 homes), a seeded mix of probing and unprobed operations over 40 keys, and
the synchronous schedule. Checks, for two different word functions: the
schedule's windows tile the consumed positions; at most one real probe per
(family, key); the real/dummy pattern is the same under both word functions.

    lake env lean --run spec_tests/Online.lean
-/

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Spec

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

def ops (n : Nat) : List Op := Id.run do
  let mut s := 12345
  let mut out := #[]
  for j in [0:n] do
    s := lcg s
    let key := s / 2 ^ 40 % 40 + 1
    let tomb := s / 2 ^ 20 % 5 == 0
    let r : Rec := ⟨LogicalKey.ofNat (key), j, tomb⟩
    out := out.push (if s / 2 ^ 10 % 7 == 0 then .blind r else .probe r)
  return out.toList

def run : OnlineRun := ⟨ops 200, [], fun _ => false⟩
def w1 : Words := fun ℓ v k => lcg (LogicalKey.toNat k * 1000003 + ℓ * 7919 + v * 104729)
def w2 : Words := fun ℓ v k => lcg (lcg (LogicalKey.toNat k + 17 * ℓ + 31 * v))

def tiles : Bool := (List.range 200).all fun j =>
  let p := syncSchedule cfg j
  let rec go : List (Nat × Nat) → Nat → Bool
    | [], hi => hi == 0
    | c :: cs, hi => (window cfg c.1 c.2).2 == hi && decide ((window cfg c.1 c.2).1 ≤ hi) &&
        go cs (window cfg c.1 c.2).1
  go p.tables (p.consumed * cfg.carryPositions 1)

def main : IO Unit := do
  IO.println s!"tiles {tiles}"
  let mut reals : Array ((Nat × Nat) × LogicalKey) := #[]
  let mut same := true
  for j in [0:200] do
    let p := syncSchedule cfg j
    for i in [0:p.tables.length] do
      let a := isReal cfg sh g run (syncSchedule cfg) w1 j i
      let b := isReal cfg sh g run (syncSchedule cfg) w2 j i
      if a != b then same := false
      if a then
        let c := p.tables[i]!
        reals := reals.push (familyOf cfg c.1 c.2, ((run.ops[j]?.map Op.record).getD default).key)
  let distinct := reals.toList.eraseDups.length == reals.size
  IO.println s!"real probes {reals.size}, distinct {distinct}, pattern word-free {same}"
  if !(tiles && distinct && same) then
    IO.println "FAIL"
    IO.Process.exit 1
  IO.println "OK"
