import RebuildBound.Spec.ConfigurationFamilyCertification
import RebuildBound.Proofs.ConfigurationFamilyBound.Analytic
import RebuildBound.Proofs.ConfigurationFamilyBound.Exposure
import RebuildBound.Proofs.HierarchyProbability.Fixed
import RebuildBound.Proofs.HierarchySemantics
import RebuildBound.Proofs.AdaptiveCausal.Generic
import RebuildBound.Proofs.AdaptiveAssembly
import RebuildBound.Proofs.OnlineObliviousAssembly
import RebuildBound.Proofs.BatchObliviousAssembly

/-! Shared final composition. The numerical inventory is consumed only here;
all reference semantics and local source laws were established independently. -/
open MeasureTheory
open scoped ENNReal
namespace RebuildBound.ConfigurationFamilyBoundProof
open Model Model.Hierarchy Spec Spec.ConfigurationFamily

/-- Remove initialization through the generic exposure identity, then use the
same initialized numerical certificate for either start. -/
theorem causal (hNum : ConfigurationFamilyNumerics_statement) : ConfigurationFamilyCausal_statement := by
  intro initialized m hm h hh N n w T hT Ω _ μ _ tape dtape words hOT
  have ha := ConfigurationFamilyAnalytic initialized m hm h hh N n w T hT μ tape dtape words hOT
  exact ha.trans (mul_le_mul' le_rfl ((exposure_le_initialized m initialized).trans (hNum m hm)))

theorem windows (hC : ConfigurationFamilyCausal_statement) : ConfigurationFamilyWindows_statement := by
  intro initialized m hm
  let geo := m.geometry initialized
  have hc := hC initialized m hm
  refine ⟨HierarchyProbabilityProof.windows_of_causal geo _ hc, ?_⟩
  apply AdaptiveWindowsUniverse geo _
  apply AdaptiveAssembly.numericFor geo _ ?_ hc
  intro h _
  have hs := HierarchyFixedSemantics (geo.chunk h)
    (ConfigurationFamilyProbabilityProof.structural initialized m hm h)
  exact AdaptiveCausalProof.causalFor (geo.chunk h) hs.2.1 hs.2.2.1
    (ConfigurationFamilyProbabilityProof.timeFacts initialized m hm h)
    AdaptiveProof.rowCausality TraceUnitsPrefix AdaptiveProof.adaptiveReplay

theorem oblivious (hW : ConfigurationFamilyWindows_statement) : ConfigurationFamilyOblivious_statement := by
  intro initialized m hm
  let geo := m.geometry initialized
  obtain ⟨hfixed, hadaptive⟩ := hW initialized m hm
  have hs : ∀ h, (geo.chunk h).Structural :=
    ConfigurationFamilyProbabilityProof.structural initialized m hm
  refine ⟨?_, ?_, ?_⟩
  · apply KeyRelabel.onlineOblivious_transport geo _
    exact OnlineObliviousAssemblyProof.obliviousFor geo _ hfixed
      (fun h _ => (HierarchyFixedSemantics (geo.chunk h) (hs h)).1.2.2.2)
  · apply KeyRelabel.batchOblivious_transport geo _
    exact BatchObliviousAssemblyProof.obliviousFor geo _ hfixed
      (fun h _ => (HierarchyFixedSemantics (geo.chunk h) (hs h)).2.2.2.2)
  · exact AdaptiveObliviousAssembly geo _
      (fun h _ => (HierarchyAdaptiveSemantics (geo.chunk h) (hs h)).1) hadaptive

end RebuildBound.ConfigurationFamilyBoundProof
