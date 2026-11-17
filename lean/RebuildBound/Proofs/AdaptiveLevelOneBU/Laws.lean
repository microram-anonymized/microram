import RebuildBound.Proofs.AdaptiveLevelOneBU.Basic
import RebuildBound.Proofs.DirectJobSelected

/-! Finite shape equalities for the legacy 31 specialization. Local probability
laws are shared in GenericLaws; causal transfer is shared in Generic. -/

namespace RebuildBound.AdaptiveLevelOneBUProof
open Model Model.DirectJob Spec

theorem selected_constants (d : Nat) (hlo : 2 ≤ d) (hhi : d ≤ 8) :
    (selectedDirectGeometry d).K = 4 ∧
    (selectedDirectGeometry d).U = 16 ∧
    (selectedDirectGeometry d).bCapacity = 64 ∧
    (selectedDirectGeometry d).outputCapacity = 64 ∧
    (selectedDirectGeometry d).outputHomes = d * 16 := by
  interval_cases d <;> decide

theorem selected_home (d : Nat) (hlo : 2 ≤ d) (hhi : d ≤ 8) (word : Nat) :
    (selectedDirectGeometry d).home word = (selectedDirectSep d).homeOf word := by
  have hc := DirectJobSelectedAAdapter d hlo hhi
  simp [Geometry.home, digitHome, SepGeom.homeOf, SepGeom.cls, SepGeom.k, hc.K, hc.e, hc.r]

theorem sep_U (d : Nat) : (selectedDirectSep d).U = 16 := rfl

theorem selected_referenceCompatible (d : Nat) (hlo : 2 ≤ d) (hhi : d ≤ 8) :
    ReferenceInputCompatible (selectedDirectGeometry (d - 1)) (selectedDirectSep d) := by
  interval_cases d <;> decide

end RebuildBound.AdaptiveLevelOneBUProof
