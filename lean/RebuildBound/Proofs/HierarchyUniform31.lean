import RebuildBound.Spec.HierarchyUniform31
import RebuildBound.Proofs.Compose31
import RebuildBound.Proofs.HierarchyUniform
import RebuildBound.Proofs.HierarchyCovering31
import RebuildBound.Proofs.HierarchyLaws31

/-! The first-horizon bound for capacity 2^31. All structural, covering,
local-law and numerical obligations are discharged by the imported proofs. -/

namespace RebuildBound
open Spec

/-- Capacity failure within the first 2^32 accesses has probability at most
2^-64 in the serialised ideal hierarchy with the capacity-2^31 geometry. -/
theorem HierarchyUniform31 : HierarchyUniform31_statement :=
  HierarchyUniformProof.assembleFor geometry31 _ Compose31.directUniform31
    HierarchyCovering31 HierarchySepLaw31 HierarchyTopLaw31 HierarchyLevelOne31

end RebuildBound
