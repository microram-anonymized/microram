import RebuildBound.Spec.IdealSepA
import RebuildBound.Proofs.IdealSepA.Actual
import RebuildBound.Proofs.IdealGeometry.Separated
import RebuildBound.Proofs.IdealSepUnion

/-! The two-family early section and current-family union section cover every
separated first failure in the certified geometry family, using the existing
analytic budgets and the actual adaptive canonical tape. -/
namespace RebuildBound
open Model Model.Hierarchy Spec Spec.IdealHierarchy Spec.IdealDirect
open ConfigurationFamilyProbabilityProof

theorem IdealSepA : IdealSepA_statement := by
  intro initialized member hm horizon geo g S m a hgeom hE hS level ordinal row
    hpot hlevel hdigit hrow
  have hgeo := structural initialized member hm horizon
  have F := HierarchySemanticsProof.lower hgeo.1
  obtain ⟨h1, hbelow, _⟩ := HierarchyInvariantProof.pj_ordinary hpot
  have hdmax := HierarchyInvariantProof.digit_le
    (lt_of_lt_of_le (by decide : 0 < 2) (F.fan level h1 hbelow).1) ordinal
  change geo.cfg.digitAt level ordinal ≤ geo.cfg.fanout level at hdmax
  have hr := hgeo.1.2.2.2.2 level hbelow (geo.cfg.digitAt level ordinal)
    (Nat.lt_succ_of_le hdmax) hlevel hdigit
  rw [hrow] at hr
  obtain ⟨hd, hU, hv, hC, _⟩ := hr
  have ha := arithmetic initialized member hm
  have hrows := HierarchySepLawChunksProof.rowsMatch_chunk horizon ha.2.2.1
  obtain ⟨_, _, _, hmem⟩ := HierarchySepLawProof.sepRow_spec hrows hrow
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hmem
  obtain ⟨_, _, _, _, hIK, _, hcut⟩ := ha.2.2.2.1 q hq
  have hshape : geo.shapes.sep level (geo.cfg.digitAt level ordinal) = q.1 := by
    simp [HierarchyGeometry.shapes, hierarchyShapesWith, hrow]
  exact IdealSepAProof.early_bound geo hgeo g S a hgeom hE hS level ordinal q.1
    hpot hlevel hdigit hshape hd hU (rowOK initialized member hm q hq) hv hC hIK hcut

/-- Family row arithmetic instantiates the same separated first-failure
argument used for arbitrary compatible geometries. -/
theorem IdealSepFirstFailure : IdealSepFirstFailure_statement := by
  intro initialized member hm horizon geo g S m a hgeom hE hS level ordinal row
    hpot hlevel hrow
  have hgeo := structural initialized member hm horizon
  have ha := arithmetic initialized member hm
  have hrows := HierarchySepLawChunksProof.rowsMatch_chunk horizon ha.2.2.1
  obtain ⟨_, _, _, hmem⟩ := HierarchySepLawProof.sepRow_spec hrows hrow
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hmem
  obtain ⟨hk, hK, hodd, _, hIK, _, hcut⟩ := ha.2.2.2.1 q hq
  exact IdealGeometryProof.separated_first_failure geo hgeo g S a hgeom hE hS
    level ordinal q.1 hpot hlevel hrow hk hK hodd hIK hcut

end RebuildBound
