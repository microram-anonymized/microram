import RebuildBound.Spec.IdealTopFinish
import RebuildBound.Proofs.IdealTopFinish.Actual
import RebuildBound.Proofs.ApiLegal
import RebuildBound.Proofs.ConfigurationFamilyProbability.Causal

/-! Legal adaptive API clients derive top-finish structure and both live-capacity
populations on every tape. The existing analytic budget applies to the actual
unconditional reference execution, including its overflow continuations. -/
namespace RebuildBound
open Model Model.Hierarchy Model.Online Spec Spec.IdealHierarchy Spec.IdealDirect
open HierarchyInvariantProof ConfigurationFamilyProbabilityProof
open MeasureTheory

theorem IdealTopFinish : IdealTopFinish_statement := by
  intro geo hgeo c g S init m width batches fs choose n compiled hinit hgeom hE hn hS
    hcap K1 K2 hwide hK1 hK2 ordinal hpot a
  have G := TopFacts.of_compatible hgeo.2
  have hInit : init.length ≤ geo.init.C / 2 * geo.init.T := by
    rw [G.initC, G.topC, G.initT]
    exact hinit.2.1.trans G.capacity
  have hapi := ApiLegalLive geo hgeo c g S init m width batches choose
    hinit hgeom hE hn hS hcap
  obtain ⟨ho, hoh⟩ := pj_top (Or.inr hpot)
  exact IdealTopFinishProof.actual_bound geo hgeo g S a hgeom hE hS
    (fun tape => ⟨(hapi (words tape) (dummy tape)).1.1, hInit,
      (hapi (words tape) (dummy tape)).1.2.1⟩) ordinal ho hoh
    (fun tape w => ((hapi (words tape) (dummy tape)).2.1.2 w ordinal ho hoh).2)
    K1 K2 hwide hK1 hK2

theorem IdealTopFinishFirstFailure : IdealTopFinishFirstFailure_statement := by
  intro initialized member hm horizon geo c g S init m width batches fs choose n compiled
    hinit hgeom hE hn hS hcap ordinal hpot a
  have hgeo := structural initialized member hm horizon
  have ha := arithmetic initialized member hm
  have hcut := topCutoffs initialized member hm
  have hb := IdealTopFinish geo hgeo c g S init m width batches choose
    hinit hgeom hE hn hS hcap 576 576 ha.2.2.2.2.1
      hcut.1.1 hcut.1.2 ordinal hpot
  refine (measure_mono ?_).trans hb
  intro tape htape
  obtain ⟨_, hfit, hfail, _⟩ := htape
  exact ⟨hfit, by simpa only [jobFails, Bool.not_eq_eq_eq_not, Bool.not_true] using hfail⟩

end RebuildBound
