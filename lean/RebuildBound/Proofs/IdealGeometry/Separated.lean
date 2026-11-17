import RebuildBound.Proofs.IdealSepA.Actual
import RebuildBound.Proofs.IdealSepA.Compose
import RebuildBound.Proofs.IdealSepUnion.Actual

/-! Separated first-failure applicability for arbitrary structural geometries.
Only actual row arithmetic supplements the structural certificate; all local
populations and probability laws are derived from the canonical execution. -/
namespace RebuildBound.IdealGeometryProof
open Model Model.Hierarchy Spec Spec.IdealHierarchy Spec.IdealDirect
open MeasureTheory
open scoped ENNReal

/-- The separated first-failure estimate needs no membership in a finite
configuration family, no fixed dictionary, and no supplied run-probability law. -/
theorem separated_first_failure (geo : HierarchyGeometry) (hgeo : geo.Structural)
    (g : Online.OnlineGeom) (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (hgeom : g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1)
    (hE : 0 < g.unitEntries)
    (hS : SchedulePremises geo.cfg S (Adaptive.slotCount a.shape) m)
    (level ordinal : Nat) (row : SepGeom)
    (hpot : JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs)
    (hlevel : 2 ≤ level)
    (hrow : geo.cfg.sepRow geo.rows level (geo.cfg.digitAt level ordinal) = some row)
    (hk : row.k < 64) (hK : row.K + val2 (row.d - 1) ≤ 64)
    (hodd : 0 < (row.d - 1) / 2 ^ val2 (row.d - 1))
    (hIK : row.I < row.K) (hcut : row.stashPages * row.C < 256) :
    IdealKey.tapeLaw {tape |
      JobFailsFirst geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape)
        (words tape) (.ordinary level ordinal)} ≤ selSepBound row := by
  by_cases hdigit : 2 ≤ geo.cfg.digitAt level ordinal
  · have F := HierarchySemanticsProof.lower hgeo.1
    obtain ⟨h1, hbelow, _⟩ := HierarchyInvariantProof.pj_ordinary hpot
    have hdmax := HierarchyInvariantProof.digit_le
      (lt_of_lt_of_le (by decide : 0 < 2) (F.fan level h1 hbelow).1) ordinal
    change geo.cfg.digitAt level ordinal ≤ geo.cfg.fanout level at hdmax
    have hr := hgeo.1.2.2.2.2 level hbelow (geo.cfg.digitAt level ordinal)
      (Nat.lt_succ_of_le hdmax) hlevel hdigit
    rw [hrow] at hr
    obtain ⟨hd, hU, hv, hC, hpages, _⟩ := hr
    have hshape : geo.shapes.sep level (geo.cfg.digitAt level ordinal) = row := by
      simp [HierarchyGeometry.shapes, hierarchyShapesWith, hrow]
    apply IdealSepAProof.first_failure_bound geo.cfg geo.shapes IdealKey.tapeLaw
      (trace geo.cfg geo.shapes g S a) words level ordinal row hlevel hshape hv
    · intro tape hdigit
      rw [← hshape]
      exact IdealSepAProof.sep_shape geo hgeo.1 (trace geo.cfg geo.shapes g S a tape)
        (IdealDirectProof.trace_units geo.cfg g _ hgeom hE).1
        (IdealDirectProof.trace_units geo.cfg g _ hgeom hE).2
        (words tape) level ordinal hpot hlevel hdigit
    · intro hdigit
      exact IdealSepAProof.early_bound geo hgeo g S a hgeom hE hS level ordinal row
        hpot hlevel hdigit hshape hd hU
        (HierarchySepLawProof.rowOK_of_width hk hK hodd) hv hC hIK hcut
    · intro hdigit
      exact IdealSepUnionProof.actual_bound geo hgeo g S a hgeom hE hS level ordinal row
        hpot hlevel hdigit hd hU hv hk hC hpages
        (lt_of_le_of_lt (min_le_left _ _) hcut)
  · have hd : geo.cfg.digitAt level ordinal = 1 := by
      unfold Config.digitAt Config.digitOf at hdigit ⊢
      omega
    have hempty : {tape | JobFailsFirst geo.cfg geo.shapes
        (trace geo.cfg geo.shapes g S a tape) (words tape) (.ordinary level ordinal)} = ∅ := by
      ext tape
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, _, hf, _⟩
      simp [jobFails, show level ≠ 1 by omega, hd] at hf
    rw [hempty, measure_empty]
    exact zero_le

end RebuildBound.IdealGeometryProof
