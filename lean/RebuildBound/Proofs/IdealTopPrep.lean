import RebuildBound.Spec.IdealTopPrep
import RebuildBound.Proofs.IdealTopPrep.Actual
import RebuildBound.Proofs.ApiLegal
import RebuildBound.Proofs.ConfigurationFamilyProbability.Causal

/-! Legal adaptive API clients supply top-preparation structure and population
on every canonical tape. The analytic section bound therefore requires no
fixed dictionary or externally supplied job law. -/
namespace RebuildBound
open Model Model.Hierarchy Model.Online Spec Spec.IdealHierarchy Spec.IdealDirect
open HierarchyInvariantProof ConfigurationFamilyProbabilityProof
open MeasureTheory

theorem IdealTopPreparation : IdealTopPreparation_statement := by
  intro geo hgeo c g S init m width batches fs choose n compiled hinit hgeom hE hn hS
    hcap K1 K2 hwide hdfs hK1 hK2 ordinal hpot a
  have G := TopFacts.of_compatible hgeo.2
  have hInit : init.length ≤ geo.init.C / 2 * geo.init.T := by
    rw [G.initC, G.topC, G.initT]
    exact hinit.2.1.trans G.capacity
  have hapi := ApiLegalLive geo hgeo c g S init m width batches choose
    hinit hgeom hE hn hS hcap
  obtain ⟨ho, hoh⟩ := pj_top (Or.inl hpot)
  apply IdealTopPrepProof.actual_bound geo hgeo g S a hgeom hE hS
    (fun tape => ⟨(hapi (words tape) (dummy tape)).1.1, hInit,
      (hapi (words tape) (dummy tape)).1.2.1⟩) ordinal ho hoh
    (fun tape w => ((hapi (words tape) (dummy tape)).2.1.2 w ordinal ho hoh).1)
    K1 K2 hwide hdfs hK1 hK2

theorem IdealTopPreparationFirstFailure : IdealTopPreparationFirstFailure_statement := by
  intro initialized member hm horizon geo c g S init m width batches fs choose n compiled
    hinit hgeom hE hn hS hcap ordinal hpot a
  have hgeo := structural initialized member hm horizon
  have ha := arithmetic initialized member hm
  have hcut := topCutoffs initialized member hm
  have hb := IdealTopPreparation geo hgeo c g S init m width batches choose
    hinit hgeom hE hn hS hcap 576 576 ha.2.2.2.2.2.1
      (fun _ => hcut.2.1.1) hcut.2.1.2.1 hcut.2.1.2.2 ordinal hpot
  refine (measure_mono ?_).trans hb
  intro tape htape
  obtain ⟨_, hfit, hfail, _⟩ := htape
  exact ⟨hfit, by simpa only [jobFails, Bool.not_eq_eq_eq_not, Bool.not_true] using hfail⟩

end RebuildBound
