import RebuildBound.Spec.HierarchyGeometry.Interfaces
import RebuildBound.Spec.HierarchyChunk
import RebuildBound.Spec.HierarchyUniform31

/-! Fixed-chunk and finite-window bounds for explicit hierarchy geometry.
A chunk contains the run's first failure, using the existing speculative
trigger boundary. No conditioning on survival is part of these statements. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy

/-- Structural contracts and ideal-tape laws at every positive chunk horizon. -/
def HierarchyLawsChunks31_statement : Prop :=
  ∀ h, 1 ≤ h →
    HierarchyInvariantFor (geometry31.chunk h) ∧
    HierarchyLocalityFor (chunkConfig config31 h) (geometry31.chunk h).shapes ∧
    HierarchyLevelOneFor (chunkConfig config31 h) keyCapacity31 ∧
    HierarchySepLawFor (geometry31.chunk h) ∧
    HierarchyTopLawFor (geometry31.chunk h)

/-- Prefix covering at every positive chunk horizon. -/
def HierarchyCoveringChunks31_statement : Prop :=
  ∀ h, 1 ≤ h → HierarchyCoveringFromFor (geometry31.chunk h)

/-- Every fixed chunk has first-capacity-failure probability at most 2^-64. -/
def HierarchyChunk31_statement : Prop :=
  HierarchyChunkFor geometry31 (ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

/-- Failure in the first h ≥ 1 chunks has probability at most h * 2^-64. -/
def HierarchyWindows31_statement : Prop :=
  HierarchyWindowsFor geometry31 (ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

end RebuildBound.Spec
