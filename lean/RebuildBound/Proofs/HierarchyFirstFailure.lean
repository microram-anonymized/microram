import RebuildBound.Proofs.HierarchyHorizonFree
import RebuildBound.Spec.HierarchyFirstFailure
import RebuildBound.Proofs.HierarchyCoveringFrom
import RebuildBound.Proofs.TierFit

/-! Scalar, adaptive and prefix first-failure adapters share one minimum-job
proof. All compatible direct shapes, hierarchy depths and starts use it. -/

namespace RebuildBound.HierarchyFirstFailureProof
open Spec Model Model.Hierarchy HierarchyCoveringProof

/-- First-failure covering at arbitrary compatible direct geometry. The
shared least-failure witness supplies tier fitting and the earlier-cycle facts. -/
theorem coveringFor (geo : HierarchyGeometry)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (hS : SepTierFit_statement) (hT : TopTierFit_statement) (hP : TPTierFit_statement) :
    ∀ (tr : Trace) (words : Words), Fails geo.cfg geo.shapes tr words →
    ∃ j ∈ geo.cfg.potentialJobs, JobFailsFirst geo.cfg geo.shapes tr words j := by
  intro tr words hfails
  obtain ⟨j, hj, hW, hfit, hf, hB⟩ := firstFailureBelowFor geo F hS hT hP tr words hfails
  refine ⟨j, hj, hW, hfit, hf, ?_⟩
  rintro o rfl i hi0 hid
  obtain ⟨h1, h2, h3, h4⟩ := mem_ordinary.1 hj
  have hsd := F.seed_dvd
  have hb : 0 < geo.cfg.fanout 1 := by
    have := F.fanout_ge 1 (by have := F.levels_ge; omega) le_rfl; omega
  have hmod : (o - 1) % geo.cfg.fanout 1 ≤ o - 1 - geo.cfg.seed 1 := by
    have e : o - 1 = (o - 1 - geo.cfg.seed 1) + geo.cfg.seed 1 := by omega
    have h2 : (o - 1) % geo.cfg.fanout 1 = (o - 1 - geo.cfg.seed 1) % geo.cfg.fanout 1 := by
      conv_lhs => rw [e]
      rw [Nat.add_mod, hsd, Nat.add_zero, Nat.mod_mod]
    rw [h2]
    exact Nat.mod_le _ _
  simp only [Config.digitAt, Config.digitOf] at hid
  have hseed : geo.cfg.seed 1 < o - i := by omega
  apply hB
  · exact mem_ordinary.2 ⟨le_rfl, h2, hseed, by omega⟩
  · unfold WithinHorizon at hW ⊢
    simp only [jobTime, time_eq, F.per_one, Nat.mul_one] at hW ⊢
    omega
  · simp only [key, time_eq, F.per_one, Nat.mul_one]
    omega

/-- Covering transfers to every positive finite window without imposing a
selected first-level shape. -/
theorem chunksFor (geo : HierarchyGeometry)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (C : HierarchyChunkArith.ChunkFacts geo.cfg) : HierarchyFirstFailureChunksFor geo := by
  intro h _
  exact coveringFor (geo.chunk h)
    (HierarchyCoveringFromProof.factsFor_chunk F C HierarchyHorizonFree h)
    SepTierFit TopTierFit TPTierFit

end RebuildBound.HierarchyFirstFailureProof
