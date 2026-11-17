import RebuildBound.Spec.Model.Hierarchy

/-!
Core-only mirrors of the selected configurations and geometry data. The oracle
must validate these before permitting any omitted top evidence. Their exact
identity to the canonical Spec definitions is kernel-checked in the default
SpecTests build (`spec_tests/SelectedReplay.lean`); keep those checks when these
snapshots change. This avoids importing probability theory into the executable.
-/

namespace RebuildBound.Oracle.SelectedShapes
open RebuildBound.Model RebuildBound.Model.DirectJob

def uniformConfig : Config :=
  { fanouts := [8, 8, 8, 8, 8], carry1 := 16, topDigit := 8, load := 32,
    horizon := 2 ^ 32, initialized := true }

def halfFanoutConfig : Config :=
  { fanouts := [4, 4, 4, 8, 8, 8], carry1 := 16, topDigit := 8, load := 32,
    horizon := 2 ^ 32, initialized := true }

def uniformSeparated : List (SepGeom × Nat) := [
    -- ordinary_L2_d2
    ({ C := 64, K := 7, e := 1, r := 1, rangeBits := 7, I := 1,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L2_d3
    ({ C := 64, K := 7, e := 0, r := 3, rangeBits := 7, I := 2,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L2_d4
    ({ C := 64, K := 7, e := 2, r := 1, rangeBits := 7, I := 2,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L2_d5
    ({ C := 64, K := 7, e := 0, r := 5, rangeBits := 7, I := 3,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L2_d6
    ({ C := 64, K := 7, e := 1, r := 3, rangeBits := 7, I := 3,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L2_d7
    ({ C := 64, K := 7, e := 0, r := 7, rangeBits := 7, I := 3,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L2_d8
    ({ C := 64, K := 7, e := 3, r := 1, rangeBits := 7, I := 3,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L3_d2
    ({ C := 64, K := 10, e := 1, r := 1, rangeBits := 7, I := 4,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L3_d3
    ({ C := 64, K := 10, e := 0, r := 3, rangeBits := 7, I := 5,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L3_d4
    ({ C := 64, K := 10, e := 2, r := 1, rangeBits := 7, I := 5,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L3_d5
    ({ C := 64, K := 10, e := 0, r := 5, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L3_d6
    ({ C := 64, K := 10, e := 1, r := 3, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L3_d7
    ({ C := 64, K := 10, e := 0, r := 7, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L3_d8
    ({ C := 64, K := 10, e := 3, r := 1, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L4_d2
    ({ C := 64, K := 13, e := 1, r := 1, rangeBits := 8, I := 6,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L4_d3
    ({ C := 64, K := 13, e := 0, r := 3, rangeBits := 8, I := 7,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L4_d4
    ({ C := 64, K := 13, e := 2, r := 1, rangeBits := 8, I := 7,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L4_d5
    ({ C := 64, K := 13, e := 0, r := 5, rangeBits := 8, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L4_d6
    ({ C := 64, K := 13, e := 1, r := 3, rangeBits := 8, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L4_d7
    ({ C := 64, K := 13, e := 0, r := 7, rangeBits := 8, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L4_d8
    ({ C := 64, K := 13, e := 3, r := 1, rangeBits := 9, I := 7,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L5_d2
    ({ C := 64, K := 16, e := 1, r := 1, rangeBits := 9, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L5_d3
    ({ C := 64, K := 16, e := 0, r := 3, rangeBits := 9, I := 9,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L5_d4
    ({ C := 64, K := 16, e := 2, r := 1, rangeBits := 9, I := 9,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L5_d5
    ({ C := 64, K := 16, e := 0, r := 5, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L5_d6
    ({ C := 64, K := 16, e := 1, r := 3, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L5_d7
    ({ C := 64, K := 16, e := 0, r := 7, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L5_d8
    ({ C := 64, K := 16, e := 3, r := 1, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256)]

def halfFanoutSeparated : List (SepGeom × Nat) := [
    -- ordinary_L2_d2
    ({ C := 64, K := 6, e := 1, r := 1, rangeBits := 6, I := 1,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 524288),
    -- ordinary_L2_d3
    ({ C := 64, K := 6, e := 0, r := 3, rangeBits := 6, I := 2,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 524288),
    -- ordinary_L2_d4
    ({ C := 64, K := 6, e := 2, r := 1, rangeBits := 7, I := 1,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 524288),
    -- ordinary_L3_d2
    ({ C := 64, K := 8, e := 1, r := 1, rangeBits := 7, I := 2,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L3_d3
    ({ C := 64, K := 8, e := 0, r := 3, rangeBits := 7, I := 3,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L3_d4
    ({ C := 64, K := 8, e := 2, r := 1, rangeBits := 7, I := 3,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 131072),
    -- ordinary_L4_d2
    ({ C := 64, K := 10, e := 1, r := 1, rangeBits := 7, I := 4,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L4_d3
    ({ C := 64, K := 10, e := 0, r := 3, rangeBits := 7, I := 5,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L4_d4
    ({ C := 64, K := 10, e := 2, r := 1, rangeBits := 7, I := 5,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L4_d5
    ({ C := 64, K := 10, e := 0, r := 5, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L4_d6
    ({ C := 64, K := 10, e := 1, r := 3, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L4_d7
    ({ C := 64, K := 10, e := 0, r := 7, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L4_d8
    ({ C := 64, K := 10, e := 3, r := 1, rangeBits := 7, I := 6,
       stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 16384),
    -- ordinary_L5_d2
    ({ C := 64, K := 13, e := 1, r := 1, rangeBits := 8, I := 6,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L5_d3
    ({ C := 64, K := 13, e := 0, r := 3, rangeBits := 8, I := 7,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L5_d4
    ({ C := 64, K := 13, e := 2, r := 1, rangeBits := 8, I := 7,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L5_d5
    ({ C := 64, K := 13, e := 0, r := 5, rangeBits := 8, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L5_d6
    ({ C := 64, K := 13, e := 1, r := 3, rangeBits := 8, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L5_d7
    ({ C := 64, K := 13, e := 0, r := 7, rangeBits := 8, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L5_d8
    ({ C := 64, K := 13, e := 3, r := 1, rangeBits := 9, I := 7,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 2048),
    -- ordinary_L6_d2
    ({ C := 64, K := 16, e := 1, r := 1, rangeBits := 9, I := 8,
       stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L6_d3
    ({ C := 64, K := 16, e := 0, r := 3, rangeBits := 9, I := 9,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L6_d4
    ({ C := 64, K := 16, e := 2, r := 1, rangeBits := 9, I := 9,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L6_d5
    ({ C := 64, K := 16, e := 0, r := 5, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L6_d6
    ({ C := 64, K := 16, e := 1, r := 3, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L6_d7
    ({ C := 64, K := 16, e := 0, r := 7, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256),
    -- ordinary_L6_d8
    ({ C := 64, K := 16, e := 3, r := 1, rangeBits := 9, I := 10,
       stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 256)]

def selectedTop : TopGeom :=
  { C := 64, k := 19, e := 3, rho := 4, I := 18, dfs := true,
    rPages := 2, bPages := 2, mergePages := 2, tierPages := 2 }

def selectedTP : TPGeom :=
  { C := 64, k := 22, stashPages := 2, aTierPages := 2, drainPages := 2,
    rangeBits := 9, I := 13, dfs := true }

def selectedDirectGeometry (d : Nat) : Geometry :=
  let base : Geometry :=
    ⟨4, d, d * 16, 64, if d = 1 then 0 else 64, 64, 64, 64, 64, .direct⟩
  if d = 1 then base else
    { base with ranges := (.dfs (if d ≤ 4 then 0 else 1)
        (if d = 2 then 5 else 6) base.poolCapacity) }

def separatedClasses (cfg : Config) : List (Nat × Nat) :=
  cfg.exposures.filterMap fun p =>
    match p.1 with
    | .ordinary ℓ d => if 2 ≤ ℓ ∧ 2 ≤ d then some (ℓ, d) else none
    | _ => none

def sepRow (cfg : Config) (rows : List (SepGeom × Nat)) (ℓ d : Nat) :
    Option SepGeom :=
  (((separatedClasses cfg).zip rows).find? fun p => p.1 == (ℓ, d)).map fun p => p.2.1


/-- Current 2^31 geometry; checked against Spec.Configuration31 in SpecTests. -/
def config31 : Config :=
  { fanouts := [4, 4, 8, 8, 8, 8, 8], carry1 := 16, topDigit := 8,
    load := 32, horizon := 2 ^ 32, initialized := true }

def separated31 : List (SepGeom × Nat) := [
    ({ C := 64, K := 6, e := 1, r := 1, rangeBits := 6, I := 1, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 524288),
    ({ C := 64, K := 6, e := 0, r := 3, rangeBits := 6, I := 2, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 524288),
    ({ C := 64, K := 6, e := 2, r := 1, rangeBits := 7, I := 1, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 524288),
    ({ C := 64, K := 8, e := 1, r := 1, rangeBits := 7, I := 2, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 65536),
    ({ C := 64, K := 8, e := 0, r := 3, rangeBits := 7, I := 3, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 65536),
    ({ C := 64, K := 8, e := 2, r := 1, rangeBits := 7, I := 3, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 65536),
    ({ C := 64, K := 8, e := 0, r := 5, rangeBits := 7, I := 4, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 65536),
    ({ C := 64, K := 8, e := 1, r := 3, rangeBits := 7, I := 4, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 65536),
    ({ C := 64, K := 8, e := 0, r := 7, rangeBits := 7, I := 4, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 65536),
    ({ C := 64, K := 8, e := 3, r := 1, rangeBits := 7, I := 4, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 65536),
    ({ C := 64, K := 11, e := 1, r := 1, rangeBits := 7, I := 5, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 8192),
    ({ C := 64, K := 11, e := 0, r := 3, rangeBits := 7, I := 6, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 8192),
    ({ C := 64, K := 11, e := 2, r := 1, rangeBits := 7, I := 6, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 8192),
    ({ C := 64, K := 11, e := 0, r := 5, rangeBits := 7, I := 7, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 8192),
    ({ C := 64, K := 11, e := 1, r := 3, rangeBits := 7, I := 7, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 8192),
    ({ C := 64, K := 11, e := 0, r := 7, rangeBits := 7, I := 7, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 8192),
    ({ C := 64, K := 11, e := 3, r := 1, rangeBits := 7, I := 7, stashPages := 1, aTierPages := 1, bTierPages := 1, tierPages := 1 }, 8192),
    ({ C := 64, K := 14, e := 1, r := 1, rangeBits := 8, I := 7, stashPages := 2, aTierPages := 1, bTierPages := 1, tierPages := 2 }, 1024),
    ({ C := 64, K := 14, e := 0, r := 3, rangeBits := 8, I := 8, stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 1024),
    ({ C := 64, K := 14, e := 2, r := 1, rangeBits := 9, I := 7, stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 1024),
    ({ C := 64, K := 14, e := 0, r := 5, rangeBits := 8, I := 9, stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 1024),
    ({ C := 64, K := 14, e := 1, r := 3, rangeBits := 9, I := 8, stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 1024),
    ({ C := 64, K := 14, e := 0, r := 7, rangeBits := 8, I := 9, stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 1024),
    ({ C := 64, K := 14, e := 3, r := 1, rangeBits := 9, I := 8, stashPages := 2, aTierPages := 2, bTierPages := 1, tierPages := 2 }, 1024),
    ({ C := 64, K := 17, e := 1, r := 1, rangeBits := 9, I := 9, stashPages := 2, aTierPages := 2, bTierPages := 2, tierPages := 2 }, 128),
    ({ C := 64, K := 17, e := 0, r := 3, rangeBits := 9, I := 10, stashPages := 2, aTierPages := 2, bTierPages := 2, tierPages := 2 }, 128),
    ({ C := 64, K := 17, e := 2, r := 1, rangeBits := 9, I := 10, stashPages := 2, aTierPages := 2, bTierPages := 2, tierPages := 2 }, 128),
    ({ C := 64, K := 17, e := 0, r := 5, rangeBits := 9, I := 11, stashPages := 2, aTierPages := 2, bTierPages := 2, tierPages := 2 }, 128),
    ({ C := 64, K := 17, e := 1, r := 3, rangeBits := 9, I := 11, stashPages := 2, aTierPages := 2, bTierPages := 2, tierPages := 2 }, 128),
    ({ C := 64, K := 17, e := 0, r := 7, rangeBits := 9, I := 11, stashPages := 2, aTierPages := 2, bTierPages := 2, tierPages := 2 }, 128),
    ({ C := 64, K := 17, e := 3, r := 1, rangeBits := 9, I := 11, stashPages := 2, aTierPages := 2, bTierPages := 2, tierPages := 2 }, 128),
    ({ C := 64, K := 20, e := 1, r := 1, rangeBits := 9, I := 12, stashPages := 2, aTierPages := 2, bTierPages := 2, tierPages := 2 }, 16),
    ({ C := 64, K := 20, e := 0, r := 3, rangeBits := 9, I := 13, stashPages := 2, aTierPages := 2, bTierPages := 2, tierPages := 2 }, 16),
    ({ C := 64, K := 20, e := 2, r := 1, rangeBits := 9, I := 13, stashPages := 2, aTierPages := 2, bTierPages := 2, tierPages := 2 }, 16),
    ({ C := 64, K := 20, e := 0, r := 5, rangeBits := 9, I := 14, stashPages := 2, aTierPages := 2, bTierPages := 2, tierPages := 2 }, 16),
    ({ C := 64, K := 20, e := 1, r := 3, rangeBits := 9, I := 14, stashPages := 2, aTierPages := 2, bTierPages := 2, tierPages := 2 }, 16),
    ({ C := 64, K := 20, e := 0, r := 7, rangeBits := 9, I := 14, stashPages := 2, aTierPages := 2, bTierPages := 2, tierPages := 2 }, 16),
    ({ C := 64, K := 20, e := 3, r := 1, rangeBits := 9, I := 14, stashPages := 2, aTierPages := 2, bTierPages := 2, tierPages := 2 }, 16)
  ]
def top31 : TopGeom :=
  { C := 64, k := 23, e := 3, rho := 8, I := 18, dfs := true,
    rPages := 4, bPages := 2, mergePages := 4, tierPages := 3 }
def prep31 : TPGeom :=
  { C := 64, k := 26, stashPages := 4, aTierPages := 3, drainPages := 4,
    rangeBits := 10, I := 16, dfs := true }
def init31 : TPGeom := { prep31 with drainPages := 3 }

end RebuildBound.Oracle.SelectedShapes
