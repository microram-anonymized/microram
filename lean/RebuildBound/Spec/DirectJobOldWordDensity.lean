import RebuildBound.Spec.WordHomeFibers
import RebuildBound.Spec.DirectJobSelected

open scoped ENNReal NNReal
namespace RebuildBound.Spec
open Model

/-- The previous selected digit's complete home vector under fresh independent
64-bit words has the recorded old-home density. This concerns the whole vector,
not just one-coordinate marginals, and uses no conditioning on job success. -/
def DirectJobOldWordDensity_statement : Prop := by
  classical
  exact ∀ d, 2 ≤ d → d ≤ 8 → ∀ (keys : Finset LogicalKey)
    (target : keys → Fin (((selectedDirectSep d).d - 1) * (selectedDirectSep d).U)),
    (Fintype.card (keys → Fin (2 ^ 64)) : ℝ≥0∞)⁻¹ *
      ∑ h : keys → Fin (2 ^ 64),
        (if ∀ x, (selectedDirectSep d).oldHome (h x) = (target x : Nat)
          then 1 else 0) ≤
      ((selectedDirectSep d).oldDensity 64 keys.card : ℝ≥0∞) /
        ((((selectedDirectSep d).d - 1) * (selectedDirectSep d).U : Nat) : ℝ≥0∞) ^ keys.card

end RebuildBound.Spec
