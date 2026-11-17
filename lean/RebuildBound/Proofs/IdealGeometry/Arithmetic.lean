import RebuildBound.Spec.IdealGeometry
import RebuildBound.Proofs.HierarchyFirstFailure
import RebuildBound.Proofs.IdealExposure
import RebuildBound.Proofs.HierarchyLawsChunks31

/-! Convert the public arithmetic certificates to existing first-failure and
window helpers. Horizon transport changes neither geometry nor local budgets. -/
namespace RebuildBound.IdealGeometryProof
open Model Model.Hierarchy Spec Spec.IdealGeometry

theorem coverage_facts (geo : HierarchyGeometry) (h : Coverage geo) :
    HierarchyCoveringProof.FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct :=
  ⟨h.levels_ge, h.levels_le, h.fanout_ge, h.seed_dvd, h.seed_succ,
    h.per_one, h.per_succ, h.per_pos, h.horizon, h.rowA, h.rowCarry, h.rowOne,
    h.topB, h.initPrep, h.topPrep, h.prepTop⟩

theorem coverage_of_facts (geo : HierarchyGeometry)
    (h : HierarchyCoveringProof.FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct) :
    Coverage geo :=
  ⟨h.levels_ge, h.levels_le, h.fanout_ge, h.seed_dvd, h.seed_succ,
    h.per_one, h.per_succ, h.per_pos, h.horizon, h.rowA, h.rowCarry, h.rowOne,
    h.topB, h.initPrep, h.topPrep, h.prepTop⟩

theorem window_facts (cfg : Config) (h : WindowArithmetic cfg) :
    HierarchyChunkArith.ChunkFacts cfg :=
  ⟨h.horizon, h.levels_ge, h.dvd, h.seed_succ, h.scale, h.seed, h.ords,
    h.per_pos, h.per_top, h.fanout_pos⟩

theorem windows_of_facts (cfg : Config) (h : HierarchyChunkArith.ChunkFacts cfg) :
    WindowArithmetic cfg :=
  ⟨h.horizon, h.levels_ge, h.dvd, h.seed_succ, h.scale, h.seed, h.ords,
    h.per_pos, h.per_top, h.fanout_pos⟩

theorem structural_chunk (geo : HierarchyGeometry) (hgeo : geo.Structural) (h : Nat) :
    (geo.chunk h).Structural := by
  refine ⟨(HierarchySemanticsProof.lower_iff _).2
    (HierarchyLawsChunks31Proof.lowFacts_horizon (HierarchySemanticsProof.lower hgeo.1) _), ?_⟩
  have he := (HierarchyHorizonFree geo.cfg (h * 2 ^ 32) geo.rows).2.1
  have hi : (geo.chunk h).incomingTopCapacity = geo.incomingTopCapacity := by
    unfold HierarchyGeometry.incomingTopCapacity
    change (if geo.cfg.levels = 2 then some (geo.direct (geo.cfg.fanout 1)).outputCapacity
      else (((geo.chunk h).cfg.sepRow geo.rows (geo.cfg.levels - 1)
        (geo.cfg.fanout (geo.cfg.levels - 1))).map fun row => row.tierPages * row.C)) = _
    dsimp only [HierarchyGeometry.chunk, chunkConfig]
    rw [he]
  rw [HierarchyGeometry.TopCompatible, hi]
  exact hgeo.2

theorem analytic_chunk (geo : HierarchyGeometry) (p : Parameters)
    (ha : Analytic geo p) (h : Nat) : Analytic (geo.chunk h) p := by
  refine ⟨ha.direct, ?_, ha.initWidth, ha.initDfs, ha.initRoute, ha.initDrain,
    ha.prepWidth, ha.prepDfs, ha.prepRoute, ha.prepDrain,
    ha.finishWidth, ha.finishRoute, ha.finishDrain⟩
  intro level hlevel h2 d hd hd2 row hr
  apply ha.separated level hlevel h2 d hd hd2 row
  change (chunkConfig geo.cfg h).sepRow geo.rows level d = some row at hr
  dsimp only [chunkConfig] at hr
  rwa [(HierarchyHorizonFree geo.cfg (h * 2 ^ 32) geo.rows).2.1] at hr

theorem classBudget_chunk (geo : HierarchyGeometry) (p : Parameters) (h : Nat) :
    classBudget (geo.chunk h) p = classBudget geo p := by
  funext j
  cases j with
  | ordinary level d =>
    simp only [classBudget, HierarchyGeometry.chunk, chunkConfig]
    rw [(HierarchyHorizonFree geo.cfg (h * 2 ^ 32) geo.rows).2.1]
    rfl
  | _ => rfl

end RebuildBound.IdealGeometryProof
