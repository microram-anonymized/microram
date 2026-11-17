import RebuildBound.Proofs.HierarchyLawsChunks31
import RebuildBound.Proofs.HierarchyUniform31
import RebuildBound.Proofs.HierarchyCoveringFrom
import RebuildBound.Proofs.HierarchyWindows

/-! Capacity-2^31 fixed-chunk and finite-window bounds. The generic assembly
reuses the certified first-horizon budget; all laws and prefix covering are
discharged here, with no conditioning on earlier capacity success. -/

namespace RebuildBound
open Spec

/-- Prefix covering at every positive chunk horizon of the capacity extension. -/
theorem HierarchyCoveringChunks31 : HierarchyCoveringChunks31_statement := by
  intro h _
  exact HierarchyCoveringFromProof.coveringFromFor (geometry31.chunk h) rfl
    (HierarchyCoveringFromProof.factsFor_chunk HierarchyCovering31Proof.facts
      HierarchyLawsChunks31Proof.chunkFacts31 HierarchyHorizonFree h)
    SepTierFit TopTierFit TPTierFit

/-- The first capacity failure lies in any fixed chunk with probability at most 2^-64. -/
theorem HierarchyChunk31 : HierarchyChunk31_statement :=
  HierarchyChunkAssemblyProof.chunkFor geometry31 _ HierarchyLawsChunks31Proof.chunkFacts31
    HierarchyHorizonFree HierarchyUniform31 Compose31.directUniform31
    (fun h hh => (HierarchyLawsChunks31 h hh).2.2.2.1)
    (fun h hh => (HierarchyLawsChunks31 h hh).2.2.2.2)
    (fun h hh => (HierarchyLawsChunks31 h hh).2.2.1)
    HierarchyCoveringChunks31

/-- Over h positive chunks the failure probability is at most h * 2^-64. -/
theorem HierarchyWindows31 : HierarchyWindows31_statement :=
  HierarchyWindowsProof.windowsFor geometry31 _ HierarchyChunk31

end RebuildBound
