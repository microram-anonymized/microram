import RebuildBound.Spec.HierarchyGeometry

/-!
# Public chunk horizons

A chunk changes the horizon inventory while preserving the hierarchy's
geometry and key bound. Probability bounds and their intermediate interfaces
live in `Spec/HierarchyChunk.lean` and `Spec/HierarchyChunk31.lean`.
-/

namespace RebuildBound.Spec
open Model

/-- A selected configuration with horizon `h · 2^32`. -/
def chunkConfig (cfg : Config) (h : Nat) : Config := { cfg with horizon := h * 2 ^ 32 }

/-- Change only the execution horizon; all geometry and key bounds stay fixed. -/
def HierarchyGeometry.chunk (geo : HierarchyGeometry) (h : Nat) : HierarchyGeometry :=
  { geo with cfg := chunkConfig geo.cfg h }

end RebuildBound.Spec
