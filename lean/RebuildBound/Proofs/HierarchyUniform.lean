import RebuildBound.Spec.HierarchyUniform31
import RebuildBound.Proofs.DirectJobUniformHierarchy
import RebuildBound.Proofs.HierarchyInvariant
import RebuildBound.Proofs.HierarchyLocality
import RebuildBound.Proofs.TierFit
import RebuildBound.Proofs.HierarchyCovering
import RebuildBound.Proofs.OldWordDensity
import RebuildBound.Proofs.HierarchySepLaw
import RebuildBound.Proofs.HierarchyTopLaw
import RebuildBound.Proofs.HierarchyLevelOne

/-!
# Generic first-horizon capacity assembly

The covering, local laws, and level-one cycles instantiate an explicit
geometry and error budget. `HierarchyUniform31` applies this shared assembly
to the supported configuration.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound
open Spec Model Model.DirectJob Model.Hierarchy

namespace HierarchyUniformProof

/-- The assembly at one configuration from the intermediate statements. -/
theorem assembleFor (geo : HierarchyGeometry) (error : ℝ≥0∞)
    (hU : DirectJobUniformHierarchyFor geo.cfg geo.rows geo.top geo.prep geo.init error)
    (hCov : HierarchyCoveringFor geo) (hSep : HierarchySepLawFor geo)
    (hTop : HierarchyTopLawFor geo)
    (hOne : HierarchyLevelOneFor geo.cfg geo.keyCapacity) :
    HierarchyUniformFor geo error := by
  intro N tr hN hTr hUnsh Ω _ μ _ tape words hTape
  obtain ⟨cycTape, hLen, hNodup, hCard, hMeas, hAgree⟩ := hOne N tr hN hTr μ tape words hTape
  have hTopLaw := hTop N tr hN hTr hUnsh μ tape words hTape
  refine hU μ {ω | Fails geo.cfg (geo.shapes) tr (words ω)}
    (jobEvent geo.cfg (geo.shapes) tr words)
    (cycleUnits geo.cfg tr) cycTape (fun c ω => cycleOldWord geo.cfg (words ω) c)
    (fun c j ω => cycleNative geo.cfg c j (words ω)) ?_ ?_ ?_ ?_ ?_ ?_ hLen hNodup hCard hMeas hAgree
  · -- covering
    intro ω hω
    refine (hCov tr (words ω) hω).elim (fun hl => Or.inl ?_) (fun hr => Or.inr hr)
    obtain ⟨j, hj, hne, hrest⟩ := hl
    exact ⟨j, hj, hne, hrest⟩
  · -- separated jobs
    intro ℓ o g hjo hℓ hrow
    exact hSep N tr hN hTr hUnsh μ tape words hTape ℓ o g hjo hℓ hrow
  · exact hTopLaw.1
  · exact hTopLaw.2.1
  · exact hTopLaw.2.2
  · -- adoption: the event is empty
    intro ℓ o _ hℓ hd
    have : jobEvent geo.cfg (geo.shapes) tr words (.ordinary ℓ o) = ∅ := by
      ext ω
      simp only [jobEvent, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _
      simp [jobFails, show ℓ ≠ 1 by omega, hd]
    rw [this, measure_empty]

end HierarchyUniformProof

end RebuildBound
