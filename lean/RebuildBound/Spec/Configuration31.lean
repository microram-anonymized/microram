import RebuildBound.Spec.ConfigurationGeometry
import RebuildBound.Spec.SelTotal
import RebuildBound.Spec.DirectJobSelected
import RebuildBound.Spec.HierarchyGeometry

/-!
# Configuration inventory for the supported D8, 2^31-capacity instance

Only geometry, exposure arithmetic and proposed budgets live here. These
are not capacity-failure bounds. Rows are derived from the configuration and
page schedules; `spec_tests/Configuration31.lean` compares every field with
the current native shape fixture. Selected-configuration inventories remain inputs to shared numerical certificates.
-/

namespace RebuildBound.Spec
open Model

/-- Supported instance `L8_r8_D8_4.4.8.8.8.8.8`. -/
def config31 : Config :=
  { fanouts := [4, 4, 8, 8, 8, 8, 8], carry1 := 16, topDigit := 8,
    load := 32, horizon := 2 ^ 32, initialized := true }

def tierPages31 (ℓ : Nat) : Nat := [1, 1, 1, 1, 2, 2, 2, 3].getD (ℓ - 1) 0
def stashPages31 (ℓ : Nat) : Nat := [1, 1, 1, 1, 2, 2, 2, 4].getD (ℓ - 1) 0

def separated31 : List (SepGeom × Nat) := separatedRows config31 stashPages31 tierPages31

def top31 : TopGeom :=
  let k := (config31.carry config31.levels).log2
  let e := config31.topDigit.log2
  let retained := stashPages31 config31.levels
  let rho := routedRangeBits (k + e) retained
  { C := 64, k, e, rho, I := k + e - rho, dfs := true,
    rPages := retained, bPages := tierPages31 (config31.levels - 1),
    mergePages := stashPages31 config31.levels, tierPages := tierPages31 config31.levels }

def prep31 : TPGeom :=
  let k := top31.k + top31.e
  let stash := stashPages31 config31.levels
  let tier := tierPages31 config31.levels
  let bits := routedRangeBits k ((k - 1) * stash + tier)
  { C := 64, k, stashPages := stash, aTierPages := tier, drainPages := top31.rPages,
    rangeBits := bits, I := k - bits, dfs := true }

/-- Initialization publishes the top tier; preparation retains a carry. -/
def init31 : TPGeom := { prep31 with drainPages := top31.tierPages }

def keyCapacity31 : Nat := config31.load * top31.T

/-- The inventory instantiated in the hierarchy execution model. -/
def geometry31 : HierarchyGeometry :=
  ⟨config31, separated31, top31, prep31, init31, keyCapacity31, selectedDirectGeometry⟩

/-- Geometry compatibility and complete actual model row lookup, independently
of the still-open structural and probability theorems. -/
def Geometry31_statement : Prop :=
  geometry31.TopCompatible ∧
  (∀ p ∈ config31.separatedClasses,
    geometry31.shapes.sep p.1 p.2 =
      separatedGeometry config31 stashPages31 tierPages31 p.1 p.2) ∧
  geometry31.shapes.init.drainPages ≠ geometry31.shapes.prep.drainPages

/-- Full-geometry reuse at the same load 32, 64-bit law and cutoffs used by
`selSepBound`. Exposure counts are deliberately excluded from reuse. -/
def reusedClasses31 : List (Nat × Nat) :=
  config31.separatedClasses.filter fun (ℓ, d) =>
    ((uniformSeparated ++ halfFanoutSeparated).map Prod.fst).contains
      (separatedGeometry config31 stashPages31 tierPages31 ℓ d)

/-- Finite inventory obligations, including lookup completeness and tier links.
The lookup equality compares all geometry fields, not just `RowsMatch`. -/
def Inventory31_statement : Prop :=
  config31.Valid ∧ config31.load = 32 ∧
  config31.RowsMatch separated31 ∧
  separated31.map Prod.snd = config31.separatedCounts ∧
  separated31.length = 38 ∧
  config31.exposures.length = 51 ∧
  (∀ p ∈ config31.separatedClasses,
    config31.sepRow separated31 p.1 p.2 =
      some (separatedGeometry config31 stashPages31 tierPages31 p.1 p.2)) ∧
  (∀ ℓ ∈ config31.ordinaryLevels, ∀ i ∈ List.range (config31.fanout ℓ),
    config31.ordinaryCount ℓ (i + 1) =
      config31.horizon / (config31.carryPositions ℓ * config31.fanout ℓ) +
        if i = 0 then 1 else 0) ∧
  config31.ordinals config31.levels = 17 ∧
  config31.carry config31.levels = top31.U ∧
  config31.topDigit = top31.D ∧
  top31.T = 2 ^ 26 ∧ keyCapacity31 = 2 ^ 31 ∧
  top31.Valid ∧ prep31.Valid ∧ init31.Valid ∧
  top31.C = 64 ∧ prep31.C = top31.C ∧ init31.C = top31.C ∧
  prep31.T = top31.T ∧ init31.T = top31.T ∧
  init31.drainPages = 3 ∧ prep31.drainPages = 4 ∧
  init31.drainPages ≤ prep31.aTierPages ∧
  top31.tierPages ≤ prep31.aTierPages ∧
  prep31.drainPages ≤ top31.rPages ∧
  tierPages31 (config31.levels - 1) ≤ top31.bPages ∧
  (∀ p ∈ separated31, 0 < p.1.bTierPages ∧ p.1.k ≤ 64 ∧
    p.1.K + val2 (p.1.d - 1) ≤ 64 ∧ p.1.I < p.1.K ∧
    (p.1.r = 7 → 2 ^ (64 - p.1.k) % p.1.r = 4)) ∧
  reusedClasses31 = [(2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4)]

/-- Proposed family budgets; component probability certificates remain open. -/
def familyBudgets31 : List ℚ := [1 / 2 ^ 79, 1 / 2 ^ 65, 1 / 2 ^ 66, 1 / 2 ^ 70]
def errorBudget31 : ℚ := 1 / 2 ^ 64

/-- Exposure arithmetic applied to the existing coarse direct bounds. -/
def directCost31 : ℚ :=
  config31.ordinals 1 * (1 / 2 ^ 117 + 1 / 2 ^ 111) +
    ((List.range (config31.fanout 1 - 1)).map fun i =>
      (config31.ordinaryCount 1 (i + 2) : ℚ) * (1 / 2 ^ 102)).sum

/-- Exact budget arithmetic only, not a probability theorem. -/
def Budget31_statement : Prop :=
  directCost31 < 1 / 2 ^ 79 ∧
  familyBudgets31.sum = (25089 / 32768 : ℚ) * errorBudget31 ∧
  familyBudgets31.sum < errorBudget31

end RebuildBound.Spec
