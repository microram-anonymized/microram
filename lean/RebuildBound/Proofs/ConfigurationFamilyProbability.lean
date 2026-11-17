import RebuildBound.Spec.ConfigurationFamilyProbability
import RebuildBound.Proofs.ConfigurationFamilyProbability.Facts

namespace RebuildBound
open Model Model.Hierarchy Spec Spec.ConfigurationFamily ConfigurationFamilyProbabilityProof

theorem ConfigurationFamilySourceLaws : ConfigurationFamilySourceLaws_statement := by
  intro initialized m hm h
  have ha := arithmetic initialized m hm
  have hs := HierarchySemanticsProof.lower (ConfigurationFamilyStructural initialized m hm).1
  have hc := chunkFacts initialized m hm
  have hI := invariant initialized m hm h
  have hL := locality initialized m hm h
  refine ⟨hI, hL, ?_, ?_⟩
  · exact HierarchySepLawProof.sepLawFor _
      (HierarchySepLawChunksProof.good_chunk ha.2.1 hc h)
      (HierarchySepLawChunksProof.rowsMatch_chunk h ha.2.2.1)
      (rowOK initialized m hm) hs.load hI hL OldWordDensity
  · exact HierarchyTopLawProof.topLawFor _ (stepFacts initialized m hm h)
      (HierarchyTopLawChunksProof.carryFacts_chunk hc h) hs.load hs.levels2
      ha.2.2.2.2.1 ha.2.2.2.2.2.1 ha.2.2.2.2.2.2
      (HierarchyTopLawChunksProof.win_chunk hc h) hI hL

theorem ConfigurationFamilyCovering : ConfigurationFamilyCovering_statement := by
  intro initialized m hm
  exact HierarchyFirstFailureProof.chunksFor _ (coveringFacts initialized m hm)
    (chunkFacts initialized m hm)

end RebuildBound
