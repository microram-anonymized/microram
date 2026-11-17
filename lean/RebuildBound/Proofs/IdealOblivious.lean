import RebuildBound.Spec.IdealOblivious
import RebuildBound.Proofs.IdealProbe
import RebuildBound.Proofs.IdealCapacity
import RebuildBound.Proofs.OnlineFailure

/-! The exact reference law and unconditional capacity bound compose without
conditioning on success. Native agreement remains an explicit correspondence
hypothesis, separate from the ideal probability theorem. -/
namespace RebuildBound
open Model Model.Hierarchy Model.Online Spec IdealHierarchy IdealDirect MeasureTheory
open HierarchyInvariantProof ConfigurationFamilyProbabilityProof

/-- A family instance uses the same request-derived run for all conclusions. -/
theorem IdealApiFamily : IdealApiFamily_statement := by
  intro initialized member hm h hh geo c g S init m width batches fs choose n compiled
    hinit hg hE hhor hS hcap a observe
  have hgeo := structural initialized member hm h
  have G := TopFacts.of_compatible hgeo.2
  have hLen : init.length ≤ geo.init.C / 2 * geo.init.T := by
    rw [G.initC, G.topC, G.initT]
    exact hinit.2.1.trans G.capacity
  have hexact := IdealApiExact geo hgeo c g S init m width batches choose
    hinit.2.2.2 hinit.1 hLen hg hE hhor hS
  refine ⟨?_, hexact.1, hexact.2, ?_⟩
  · intro tape
    exact (ApiLegalLive geo hgeo c g S init m width batches choose hinit hg hE hhor hS hcap
      (words tape) (dummy tape)).1
  · exact IdealCapacity initialized member hm h hh c g S init m width batches choose
      hinit hg hE hhor hS hcap

/-- Agreement outside the actual first-capacity-failure event is the only
observation correspondence needed by the unconditional coupling. -/
theorem IdealApiOblivious : IdealApiOblivious_statement := by
  intro initialized member hm h hh geo c g S init m width batches fs choose n compiled
    hinit hg hE hhor hS hcap a reference simulator Value _ observed encode
    _hobs hencode hagree event hevent
  have hp := IdealApiFamily initialized member hm h hh c g S init m width batches choose
    hinit hg hE hhor hS hcap
  have ht := OnlineFailure.transfer IdealKey.tapeLaw simulator reference observed encode
    {tape | Fails geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape) (words tape)}
    hp.2.1 hencode hp.2.2.1 hagree event hevent
  exact ⟨ht.1.trans (add_le_add le_rfl hp.2.2.2),
    ht.2.trans (add_le_add le_rfl hp.2.2.2)⟩

/-- Seed randomization preserves both laws before the coupling is applied. -/
theorem IdealSeedOblivious : IdealSeedOblivious_statement := by
  intro Seed _ _ _ μ _ initialized member hm h hh geo c g S init m width batches fs n
    choose hinit hg hE hhor hS hcap reference bad simulator Value _ observed encode
    _hobs hencode hagree event hevent
  have hgeo := structural initialized member hm h
  have G := TopFacts.of_compatible hgeo.2
  have hLen (seed : Seed) : (init seed).length ≤ geo.init.C / 2 * geo.init.T := by
    rw [G.initC, G.topC, G.initT]
    exact (hinit seed).2.1.trans G.capacity
  have hexact := IdealApiSeedExact Seed μ geo hgeo c g S init m width batches choose
    (fun seed => (hinit seed).2.2.2) (fun seed => (hinit seed).1) hLen hg hE hhor hS
  have hbound := IdealSeedCapacity Seed μ initialized member hm h hh c g S init m width
    batches choose hinit hg hE hhor hS hcap
  have ht := OnlineFailure.transfer (μ.prod IdealKey.tapeLaw) simulator
    (Function.uncurry reference) observed encode bad hexact.1 hencode hexact.2.2
    hagree event hevent
  exact ⟨ht.1.trans (add_le_add le_rfl hbound),
    ht.2.trans (add_le_add le_rfl hbound)⟩

end RebuildBound
