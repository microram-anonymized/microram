import RebuildBound.Proofs.HierarchyFirstFailure
import RebuildBound.Spec.AdaptiveStepsAssembly
import RebuildBound.Proofs.HierarchyCoveringFrom
import RebuildBound.Proofs.HierarchyLawsChunks31
import RebuildBound.Proofs.TierFit

/-!
# AdaptiveCompose: the first-failure covering

A capacity failure within the horizon is the first-failure event
(`JobFailsFirst`) of the least failing potential job: its input tiers fit
because every earlier job published, and at level one the earlier ordinals of
its cycle do not fail.
-/

namespace RebuildBound.AdaptiveComposeProof
open RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open HierarchyCoveringProof

/-- Compatibility wrapper for the original selected interface. -/
theorem coveringFirst (geo : HierarchyGeometry)
    (hDirect : geo.direct = selectedDirectGeometry)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init)
    (hS : SepTierFit_statement) (hT : TopTierFit_statement) (hP : TPTierFit_statement) :
    ∀ (tr : Trace) (words : Words), Fails geo.cfg geo.shapes tr words →
    ∃ j ∈ geo.cfg.potentialJobs, JobFailsFirst geo.cfg geo.shapes tr words j :=
  HierarchyFirstFailureProof.coveringFor geo (by simpa only [hDirect] using F) hS hT hP

/-- The covering at every chunk horizon of `geometry31`. -/
theorem covering31 : AdaptiveCovering31_statement := fun h _ =>
  coveringFirst (geometry31.chunk h) rfl
    (HierarchyCoveringFromProof.factsFor_chunk HierarchyCovering31Proof.facts
      HierarchyLawsChunks31Proof.chunkFacts31 HierarchyHorizonFree h)
    SepTierFit TopTierFit TPTierFit

end RebuildBound.AdaptiveComposeProof
