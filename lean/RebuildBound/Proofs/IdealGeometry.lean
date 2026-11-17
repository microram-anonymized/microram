import RebuildBound.Proofs.IdealGeometry.Arithmetic
import RebuildBound.Proofs.IdealGeometry.Local
import RebuildBound.Proofs.HierarchyProbability
import RebuildBound.Proofs.IdealProbe
import RebuildBound.Proofs.ApiSeed
import RebuildBound.Proofs.OnlineFailure

/-! One geometry-parametric canonical chain: actual local laws, explicit public
exposures, request correctness, exact simulation and unconditional transfer.
No numerical matrices or family membership are used in these theorems. -/
namespace RebuildBound
open Model Model.Hierarchy Model.Online Spec Spec.IdealHierarchy Spec.IdealDirect
open Spec.IdealGeometry IdealGeometryProof MeasureTheory
open scoped ENNReal

theorem IdealGeometryCapacity : IdealGeometryCapacity_statement := by
  intro geo p hgeo hv hc ha error he c g S init m width batches fs choose n compiled
    hinit hgeom hE hn hS hcap a
  have hb := local_bounds geo p hgeo ha c g S init m width batches choose
    hinit hgeom hE hn hS hcap
  have hcover := HierarchyFirstFailureProof.coveringFor geo (coverage_facts geo hc)
    SepTierFit TopTierFit TPTierFit
  exact ((G4a geo.cfg hv IdealKey.tapeLaw _ _ (classBudget geo p)
    (fun tape hf => hcover _ _ hf) hb).trans (min_le_right _ _)).trans he

theorem IdealGeometryWindows : IdealGeometryWindows_statement := by
  intro base p hgeo hv hc ha hw error he h hh geo c g S init m width batches fs choose
    n compiled hinit hgeom hE hn hS hcap a
  have hb := local_bounds geo p (structural_chunk base hgeo h) (analytic_chunk base p ha h)
    c g S init m width batches choose hinit hgeom hE hn hS hcap
  have hb' : ∀ j ∈ geo.cfg.potentialJobs,
      IdealKey.tapeLaw {tape | JobFailsFirst geo.cfg geo.shapes
        (trace geo.cfg geo.shapes g S a tape) (words tape) j} ≤
        classBudget base p (base.cfg.classOf j) := by
    intro j hj
    have hjb := hb j hj
    change _ ≤ classBudget (base.chunk h) p (base.cfg.classOf j) at hjb
    rwa [classBudget_chunk] at hjb
  have bound := HierarchyProbabilityProof.composeFor base (window_facts base.cfg hw) hv
    (HierarchyFirstFailureProof.chunksFor base (coverage_facts base hc) (window_facts base.cfg hw))
    (classBudget base p) h hh IdealKey.tapeLaw (trace geo.cfg geo.shapes g S a) words hb'
  exact bound.trans (mul_le_mul' le_rfl he)

theorem IdealGeometryApi : IdealGeometryApi_statement := by
  intro geo p hgeo hv hc ha error he c g S init m width batches fs choose n compiled
    hinit hg hE hhor hS hcap a observe
  have G := HierarchyInvariantProof.TopFacts.of_compatible hgeo.2
  have hLen : init.length ≤ geo.init.C / 2 * geo.init.T := by
    rw [G.initC, G.topC, G.initT]
    exact hinit.2.1.trans G.capacity
  have hexact := IdealApiExact geo hgeo c g S init m width batches choose
    hinit.2.2.2 hinit.1 hLen hg hE hhor hS
  refine ⟨?_, hexact.1, hexact.2, ?_⟩
  · intro tape
    exact (ApiLegalLive geo hgeo c g S init m width batches choose hinit hg hE hhor hS hcap
      (words tape) (dummy tape)).1
  · exact IdealGeometryCapacity geo p hgeo hv hc ha error he c g S init m width batches
      choose hinit hg hE hhor hS hcap

theorem IdealGeometrySeedCapacity : IdealGeometrySeedCapacity_statement := by
  intro Seed _ _ _ μ _ geo p hgeo hv hc ha error he c g S init m width batches fs n choose
    hinit hgeom hE hn hS hcap
  apply (ApiSeedFailure Seed μ c geo.cfg geo.shapes g S init m width batches choose).2
  intro seed
  exact IdealGeometryCapacity geo p hgeo hv hc ha error he c g S (init seed) m width batches
    (choose seed) (hinit seed) hgeom hE hn hS (hcap seed)

theorem IdealGeometryOblivious : IdealGeometryOblivious_statement := by
  intro geo p hgeo hv hc ha error he c g S init m width batches fs choose n compiled
    hinit hg hE hhor hS hcap a reference simulator Value _ observed encode
    _hobs hencode hagree event hevent
  have hp := IdealGeometryApi geo p hgeo hv hc ha error he c g S init m width batches choose
    hinit hg hE hhor hS hcap
  have ht := OnlineFailure.transfer IdealKey.tapeLaw simulator reference observed encode
    {tape | Fails geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape) (words tape)}
    hp.2.1 hencode hp.2.2.1 hagree event hevent
  exact ⟨ht.1.trans (add_le_add le_rfl hp.2.2.2),
    ht.2.trans (add_le_add le_rfl hp.2.2.2)⟩

end RebuildBound
