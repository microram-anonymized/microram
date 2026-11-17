import RebuildBound.Proofs.OnlineOblivious31.Semantics
import RebuildBound.Proofs.OnlineObliviousAssembly
import RebuildBound.Proofs.HierarchyChunk31

/-! Numerical scalar obliviousness at capacity 2^31. The exact laws and
actual-failure transfer are available separately from `Semantics`. -/

namespace RebuildBound
open Spec

/-- The scalar observation is within h · 2^-64 of the simulator over h chunks. -/
theorem OnlineOblivious31 : OnlineOblivious31_statement :=
  OnlineObliviousAssemblyProof.obliviousFor geometry31 _ HierarchyWindows31 OnlineFailure31

end RebuildBound
