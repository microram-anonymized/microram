import RebuildBound.Spec.IdealSepUnion
import RebuildBound.Proofs.IdealSepUnion.Actual
import RebuildBound.Proofs.ConfigurationFamilyProbability.Facts

/-! The canonical separated union bound for the certified family. All finite
populations and laws are derived from actual execution; the existing analytic
current-home budget is reused without new numerical certificates. -/
namespace RebuildBound
open Model Model.Hierarchy Spec Spec.IdealHierarchy Spec.IdealDirect
open ConfigurationFamilyProbabilityProof

theorem IdealSepUnion : IdealSepUnion_statement := by
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
  obtain ⟨hd, hU, hv, hC, hpages, _⟩ := hr
  have ha := arithmetic initialized member hm
  have hrows := HierarchySepLawChunksProof.rowsMatch_chunk horizon ha.2.2.1
  obtain ⟨_, _, _, hmem⟩ := HierarchySepLawProof.sepRow_spec hrows hrow
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hmem
  obtain ⟨hk, _, _, _, _, _, hcut⟩ := ha.2.2.2.1 q hq
  exact IdealSepUnionProof.actual_bound geo hgeo g S a hgeom hE hS level ordinal q.1
    hpot hlevel hdigit hd hU hv hk hC hpages
    (lt_of_le_of_lt (min_le_left _ _) hcut)

end RebuildBound
