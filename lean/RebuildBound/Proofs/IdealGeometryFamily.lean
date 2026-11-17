import RebuildBound.Spec.IdealGeometryFamily
import RebuildBound.Proofs.IdealGeometry.Arithmetic
import RebuildBound.Proofs.ConfigurationFamilyDirect.Geometry
import RebuildBound.Proofs.ConfigurationFamilyProbability.Causal

/-! The finite certified inventory supplies geometry-only applicability for the
same generic canonical-tape argument. All arithmetic budgets are unchanged;
no numerical certificates or per-execution probability assumptions enter. -/
namespace RebuildBound
open Model Model.Hierarchy Spec Spec.ConfigurationFamily
open ConfigurationFamilyProbabilityProof

/-- Both starts and all certified members are instances of the generic
analytic interface, using exactly the pre-existing class budgets. -/
theorem IdealGeometryFamily : IdealGeometryFamily_statement := by
  intro initialized m hm geo
  have ha := arithmetic initialized m hm
  have hc := topCutoffs initialized m hm
  refine ⟨ConfigurationFamilyStructural initialized m hm, ha.1,
    IdealGeometryProof.coverage_of_facts geo (coveringFacts initialized m hm), ?_,
    IdealGeometryProof.windows_of_facts geo.cfg (chunkFacts initialized m hm), ?_⟩
  · refine
      { direct := ?_
        separated := ?_
        initWidth := ha.2.2.2.2.2.2
        initDfs := fun _ => hc.2.2.1
        initRoute := hc.2.2.2.1
        initDrain := hc.2.2.2.2
        prepWidth := ha.2.2.2.2.2.1
        prepDfs := fun _ => hc.2.1.1
        prepRoute := hc.2.1.2.1
        prepDrain := hc.2.1.2.2
        finishWidth := ha.2.2.2.2.1
        finishRoute := hc.1.1
        finishDrain := hc.1.2 }
    · exact ⟨ConfigurationFamilyDirectProof.cycleGeometry m hm,
        fun d hd hdn => ConfigurationFamilyDirectProof.facts m hm d hd hdn⟩
    · intro level _ _ d _ _ row hrow
      obtain ⟨_, _, _, hmem⟩ := HierarchySepLawProof.sepRow_spec ha.2.2.1 hrow
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hmem
      obtain ⟨hk, hK, ho, _, hIK, _, hcut⟩ := ha.2.2.2.1 q hq
      exact ⟨hk, hK, ho, hIK, hcut⟩
  · funext cls
    cases cls <;> rfl

end RebuildBound
