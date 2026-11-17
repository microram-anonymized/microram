import RebuildBound.Spec.Hierarchy
import RebuildBound.Spec.HierarchyChunkBase

/-!
# Shared chunk contracts and first-failure events

`chunkConfig cfg h` gives a horizon of `h · 2^32` accesses. The generic
assemblies and the supported `geometry31` endpoints reuse these contracts;
selected configuration specializations remain internal proof helpers.
`ChunkFails` records failure by chunk `k + 1`, excluding failure by chunk `k` when `k > 0`.
The public bounds are `HierarchyChunk31` and `HierarchyWindows31`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec
open Model Model.DirectJob Model.Hierarchy

/-- A property at both selected configurations, at every horizon of a positive
number of chunks. -/
def SelectedChunks (P : Config → List (SepGeom × Nat) → Prop) : Prop :=
  ∀ h, 1 ≤ h →
    P (chunkConfig uniformConfig h) uniformSeparated ∧
      P (chunkConfig halfFanoutConfig h) halfFanoutSeparated

/-! ### The model does not read the horizon (HierarchyHorizonFree) -/

/-- **HierarchyHorizonFree**: changing the horizon changes neither the shapes,
the separated rows, nor any potential job's failure or tier fit. -/
def HierarchyHorizonFree_statement : Prop :=
  ∀ (cfg : Config) (H : Nat) (rows : List (SepGeom × Nat)),
    hierarchyShapes { cfg with horizon := H } rows = hierarchyShapes cfg rows ∧
    ({ cfg with horizon := H } : Config).sepRow rows = cfg.sepRow rows ∧
    ∀ (sh : Shapes) (tr : Trace) (words : Words) (j : JobId),
      jobFails { cfg with horizon := H } sh tr words j = jobFails cfg sh tr words j ∧
      (jobTiersFit { cfg with horizon := H } sh tr words j ↔ jobTiersFit cfg sh tr words j)

/-! ### The packages at every chunk horizon -/

/-- **HierarchyInvariantChunks**. -/
def HierarchyInvariantChunks_statement : Prop :=
  HierarchyHorizonFree_statement → SelectedChunks HierarchyInvariantAt

/-- **HierarchyLocalityChunks**. -/
def HierarchyLocalityChunks_statement : Prop :=
  HierarchyHorizonFree_statement → SelectedChunks HierarchyLocalityAt

/-- **HierarchySepLawChunks**, conditional on the invariant and locality at
every chunk horizon and on the density statement. -/
def HierarchySepLawChunks_statement : Prop :=
  HierarchyHorizonFree_statement → SelectedChunks HierarchyInvariantAt →
    SelectedChunks HierarchyLocalityAt → OldWordDensity_statement →
    SelectedChunks HierarchySepLawAt

/-- **HierarchyTopLawChunks**, conditional on the invariant and locality at
every chunk horizon. -/
def HierarchyTopLawChunks_statement : Prop :=
  HierarchyHorizonFree_statement → SelectedChunks HierarchyInvariantAt →
    SelectedChunks HierarchyLocalityAt → SelectedChunks HierarchyTopLawAt

/-- **HierarchyLevelOneChunks**. -/
def HierarchyLevelOneChunks_statement : Prop :=
  HierarchyHorizonFree_statement → SelectedChunks HierarchyLevelOneAt

/-! ### Covering after a failure-free prefix (HierarchyCoveringFrom) -/

/-- Covering after time `T`: if every potential job at time at most `T` does
not fail, a failure is a potential job above level one within the horizon,
after `T`, whose input tiers fit and which fails, or a level-one cycle with an
ordinal after `T` that does not publish. -/
def HierarchyCoveringFromAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  ∀ (tr : Trace) (words : Words) (T : Nat),
    Fails cfg (hierarchyShapes cfg rows) tr words →
    (∀ j ∈ cfg.potentialJobs, jobTime cfg j ≤ T →
      jobFails cfg (hierarchyShapes cfg rows) tr words j = false) →
    (∃ j ∈ cfg.potentialJobs, (∀ o, j ≠ .ordinary 1 o) ∧ WithinHorizon cfg j ∧
      T < jobTime cfg j ∧ jobTiersFit cfg (hierarchyShapes cfg rows) tr words j ∧
      jobFails cfg (hierarchyShapes cfg rows) tr words j = true) ∨
    ∃ c < cfg.levelOneCycles, (∃ i < cfg.cycleLength c, T < cfg.cycleOrdinal c i) ∧
      CycleStuck cfg tr words c

/-- **HierarchyCoveringFrom**, conditional on the tier-fit lemmas. -/
def HierarchyCoveringFrom_statement : Prop :=
  SepTierFit_statement → TopTierFit_statement → TPTierFit_statement →
    HierarchyHorizonFree_statement → SelectedChunks HierarchyCoveringFromAt

/-! ### The theorem -/

/-- The run's first capacity failure lies in chunk `k`. -/
def ChunkFails (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (k : Nat) : Prop :=
  Fails (chunkConfig cfg (k + 1)) sh tr words ∧ (0 < k → ¬ Fails (chunkConfig cfg k) sh tr words)

end RebuildBound.Spec
