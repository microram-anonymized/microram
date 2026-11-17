import RebuildBound.Spec.ObliviousBatch
import RebuildBound.Proofs.OnlineObliviousAssembly

/-!
# Generic numerical batch obliviousness

Combine the batch failure transfer with the shared geometry-specific window
bound. The batch setting supplies the trace and unshadowed premises.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound
open Spec Model Model.Hierarchy Model.OnlineBatch

namespace BatchObliviousAssemblyProof

/-- Numerical batch obliviousness for explicit geometry and error budget. -/
theorem obliviousFor (geo : HierarchyGeometry) (error : ℝ≥0∞)
    (hWin : HierarchyWindowsFor geo error)
    (hFail : ∀ h, 1 ≤ h → BatchFailureFor (geo.chunk h)) :
    BatchObliviousFor geo error := by
  intro h hh
  dsimp only
  intro N g run S n m hset Ω _ μ _ tape dtape words hT V _ obs ι hobs hι hagree A hA
  have hb := OnlineObliviousAssemblyProof.fails_leFor geo error hWin h hh N
    (Model.OnlineBatch.traceOf g run) hset.1 hset.2.2.1.trace hset.2.2.1.unsh μ tape dtape words hT
  obtain ⟨h1, h2⟩ := hFail h hh N g run S n m hset μ tape dtape words hT obs ι hobs hι hagree A hA
  exact ⟨h1.trans (add_le_add le_rfl hb), h2.trans (add_le_add le_rfl hb)⟩

end BatchObliviousAssemblyProof

end RebuildBound
