import RebuildBound.Spec.IdealCapacity
import RebuildBound.Proofs.IdealGeometry
import RebuildBound.Proofs.IdealGeometryFamily

/-! The certified inventory is an instance of the geometry-parametric canonical
capacity theorem, with exactly its existing analytic exposure budget.
No numerical certificate enters this analytic module. -/
namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Spec.IdealHierarchy Spec.IdealDirect
open scoped ENNReal

theorem IdealCapacityAnalytic : IdealCapacityAnalytic_statement := by
  intro initialized member hm h hh geo c g S init m width batches fs choose n compiled
    hinit hgeom hE hn hS hcap a
  obtain ⟨hgeo, hv, hc, ha, hw, hb⟩ := IdealGeometryFamily initialized member hm
  apply IdealGeometryWindows (member.geometry initialized)
    (IdealGeometry.familyParameters member) hgeo hv hc ha hw
    ((member.config initialized).exposureSum (ConfigurationFamily.classBudget member initialized))
    (by rw [hb]; exact le_rfl) h hh c g S init m width batches choose
    hinit hgeom hE hn hS hcap

end RebuildBound
