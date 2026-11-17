import RebuildBound.Proofs.BatchOblivious31.Semantics
import RebuildBound.Proofs.BatchObliviousAssembly
import RebuildBound.Proofs.HierarchyChunk31

/-! Numerical batch obliviousness at capacity 2^31. -/

namespace RebuildBound
open Spec

theorem BatchOblivious31 : BatchOblivious31_statement :=
  BatchObliviousAssemblyProof.obliviousFor _ _ HierarchyWindows31 BatchFailure31

end RebuildBound
