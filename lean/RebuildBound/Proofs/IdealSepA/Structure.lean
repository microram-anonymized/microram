import RebuildBound.Proofs.IdealSepUnion.Structure
import RebuildBound.Proofs.IdealExposure
import RebuildBound.Proofs.HierarchySepLaw.Cone

/-! Lower separated shape and locality, independent of any storage-capacity
or global key-domain premise. Finite trace restriction only serves the legacy
lower-invariant helpers. -/
namespace RebuildBound.IdealSepAProof
open Model Model.Hierarchy Spec HierarchyInvariantProof HierarchyStructuralProof
open HierarchyLocalityProof IdealSepUnionProof

/-- A finite local trace has the same complete separated inputs. -/
theorem restrict_inputs (geo : HierarchyGeometry) (tr : Trace)
    (hnodup : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup)
    (hload : ∀ i, (DirectMasks.records (tr.units i)).length ≤ geo.cfg.load * geo.cfg.carry1)
    (level ordinal : Nat) (hlevel : 2 ≤ level) (hbelow : level < geo.cfg.levels) :
    ∃ (tr' : Trace) (N : Nat), TracePremises geo.cfg N tr' ∧
      ∀ words, sepInputsAt geo.cfg geo.shapes tr words level ordinal =
        sepInputsAt geo.cfg geo.shapes tr' words level ordinal := by
  let clean : Trace := { tr with init := [] }
  let cut := time geo.cfg level ordinal
  have hclean : TraceStructural geo.cfg clean := ⟨hnodup, hload, by simp [clean]⟩
  obtain ⟨N, hN⟩ := truncate_premises hclean cut
  refine ⟨truncate clean cut, N, hN, fun words => ?_⟩
  apply sep_prefix geo.cfg geo.shapes tr _ words level ordinal hlevel hbelow
  intro i hi
  have hic : i < cut := by dsimp only [cut]; omega
  simp [truncate, clean, hic]

/-- The shape of a separated reference input uses only lower invariants. -/
theorem sep_shape (geo : HierarchyGeometry) (hgeo : geo.LowerCompatible) (tr : Trace)
    (hnodup : ∀ i, ∀ u ∈ tr.units i, (u.recs.map Rec.key).Nodup)
    (hload : ∀ i, (DirectMasks.records (tr.units i)).length ≤ geo.cfg.load * geo.cfg.carry1)
    (words : Words) (level ordinal : Nat)
    (hpot : JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs)
    (hlevel : 2 ≤ level) (hdigit : 2 ≤ geo.cfg.digitAt level ordinal) :
    SInputShape (geo.shapes.sep level (geo.cfg.digitAt level ordinal))
      (jobWord geo.cfg words level (ordinal - 1)) (jobWord geo.cfg words level ordinal)
      (sepInputsAt geo.cfg geo.shapes tr words level ordinal) := by
  obtain ⟨_, hbelow, _⟩ := pj_ordinary hpot
  obtain ⟨tr', N, hT, heq⟩ := restrict_inputs geo tr hnodup hload level ordinal hlevel hbelow
  rw [heq words]
  obtain ⟨row, hr, hd, hU, _, hC, hP, _, hA, hpred, _, hB⟩ :=
    sep_ctxFor geo (HierarchySemanticsProof.lower hgeo) hT words hpot hlevel hdigit
  rw [sepInputsAt_eqFor geo, hr]
  exact sep_shape_pos hd hU hC hP hpred hA hB

/-- Every record read by a lower cone belongs to the finite local trace. -/
theorem lower_jobKeys_below (geo : HierarchyGeometry)
    (F : LowFacts geo.cfg geo.rows geo.direct) {N : Nat} {tr : Trace}
    (hT : TracePremises geo.cfg N tr) (words : Words)
    (level ordinal : Nat) (h1 : 1 ≤ level) (hbelow : level < geo.cfg.levels)
    (key : LogicalKey) (hkey : key ∈ jobKeys geo.cfg geo.shapes tr words level ordinal) :
    key.toNat < N := by
  have hne : level ≠ geo.cfg.levels := by omega
  simp only [jobKeys, hne, false_and, ite_false, List.mem_append,
    List.not_mem_nil, or_false] at hkey
  rcases hkey with (hk | hk) | hk
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
    exact low_belowFor geo F hT words h1 hbelow _ x hx
  · split_ifs at hk with hlevel
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
      exact hT.keys _ x hx
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
      exact low_belowFor geo F hT words (by omega) (by omega) _ x hx
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
    exact low_belowFor geo F hT words h1 hbelow _ x hx

/-- A predecessor does not read the current family. Every remaining read can
be restricted to the finite local trace's keys. -/
theorem previous_congr (geo : HierarchyGeometry) (hgeo : geo.Structural)
    {N : Nat} {tr : Trace} (hT : TracePremises geo.cfg N tr)
    (w w' : Words) (level ordinal : Nat)
    (h1 : 1 ≤ level) (hbelow : level < geo.cfg.levels) (ho : geo.cfg.seed level < ordinal)
    (hw : ∀ family, family ≠ familyOf geo.cfg level ordinal →
      ∀ key, key.toNat < N → w family.1 family.2 key = w' family.1 family.2 key) :
    table geo.cfg geo.shapes tr w level (ordinal - 1) =
      table geo.cfg geo.shapes tr w' level (ordinal - 1) := by
  have hf := IdealExposureProof.timeFacts (IdealExposureGeometry geo hgeo)
  apply table_congr
  intro q hq key hk
  have hqt := cone_time geo.cfg hf level (ordinal - 1) h1 hbelow.le (by omega) q hq
  have hql := HierarchySepLawProof.cone_lt level (ordinal - 1) hbelow q hq
  exact hw (familyOf geo.cfg q.1 q.2)
    (family_ne geo.cfg hf level ordinal h1 hbelow.le ho q hq) key
    (lower_jobKeys_below geo (HierarchySemanticsProof.lower hgeo.1) hT w q.1 q.2 hqt.1 hql key hk)

end RebuildBound.IdealSepAProof
