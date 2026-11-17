import RebuildBound.Proofs.IdealCapacity.Analytic
import RebuildBound.Proofs.ConfigurationFamilyBound.Exposure
import RebuildBound.Proofs.ConfigurationFamilyNumerics
import RebuildBound.Proofs.ApiSeed

/-! The existing exact numerical certificates instantiate canonical arbitrary-key
capacity, then independent seed mixtures preserve the same finite-window budget.
Reference transcript simulation and native refinement are separate obligations. -/
open MeasureTheory
open scoped ENNReal
namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Spec.IdealHierarchy Spec.IdealDirect

/-- Every certified member and either start satisfy the ideal finite-window
capacity budget for legal adaptive clients preserving logical live capacity. -/
theorem IdealCapacity : IdealCapacity_statement := by
  intro initialized member hm h hh geo c g S init m width batches fs choose n compiled
    hinit hgeom hE hn hS hcap a
  have hb := IdealCapacityAnalytic initialized member hm h hh c g S init m width batches
    choose hinit hgeom hE hn hS hcap
  exact hb.trans (mul_le_mul' le_rfl
    ((ConfigurationFamilyBoundProof.exposure_le_initialized member initialized).trans
      (ConfigurationFamilyNumerics member hm)))

/-- Client randomness may range over infinitely many seeds and byte keys.
The actual failure event is measurable, and every seed slice has the bound. -/
theorem IdealSeedCapacity : IdealSeedCapacity_statement := by
  intro Seed _ _ _ μ _ initialized member hm h hh geo c g S init m width batches fs n choose
    hinit hgeom hE hn hS hcap
  apply (ApiSeedFailure Seed μ c geo.cfg geo.shapes g S init m width batches choose).2
  intro seed
  exact IdealCapacity initialized member hm h hh c g S (init seed) m width batches
    (choose seed) (hinit seed) hgeom hE hn hS (hcap seed)

end RebuildBound
