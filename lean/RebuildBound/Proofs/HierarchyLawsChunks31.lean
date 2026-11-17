import RebuildBound.Spec.HierarchyChunk31
import RebuildBound.Proofs.HierarchyLaws31
import RebuildBound.Proofs.HierarchyInvariantChunks
import RebuildBound.Proofs.HierarchyLocalityChunks
import RebuildBound.Proofs.HierarchySepLawChunks
import RebuildBound.Proofs.HierarchyTopLawChunks
import RebuildBound.Proofs.HierarchyHorizonFree

namespace RebuildBound.HierarchyLawsChunks31Proof
open Model Model.Hierarchy Spec HierarchyChunkArith

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem chunkFacts31 : ChunkFacts config31 where
  horizon := rfl
  levels_ge := by decide +kernel
  dvd := by decide +kernel
  seed_succ := by decide +kernel
  scale := by decide +kernel
  seed := by decide +kernel
  ords := by decide +kernel
  per_pos := by decide +kernel
  per_top := by decide +kernel
  fanout_pos := by decide +kernel

/-- Lower configuration facts transfer without evaluating an execution. -/
theorem lowFacts_horizon {cfg : Config} {rows : List (SepGeom × Nat)}
    {direct : Nat → Model.DirectJob.Geometry}
    (F : HierarchyInvariantProof.LowFacts cfg rows direct) (H : Nat) :
    HierarchyInvariantProof.LowFacts {cfg with horizon := H} rows direct where
  levels2 := F.levels2
  load := F.load
  direct := F.direct
  fan := F.fan
  seed := F.seed
  carrySucc := F.carrySucc
  carryPow := F.carryPow
  rows ℓ d a b c e := by
    rw [(HierarchyHorizonFree cfg H rows).2.1]
    exact F.rows ℓ d a b c e

/-- Top dimensions and capacity do not read the horizon. -/
theorem topFacts_chunk {geo : HierarchyGeometry}
    (F : HierarchyInvariantProof.TopFacts geo) (h : Nat) :
    HierarchyInvariantProof.TopFacts (geo.chunk h) where
  topValid := F.topValid
  prepValid := F.prepValid
  initValid := F.initValid
  topC := F.topC
  prepC := F.prepC
  initC := F.initC
  prepT := F.prepT
  initT := F.initT
  carryTop := F.carryTop
  capacity := F.capacity

/-- Ordinal scaling supplies the level-one step bound at every chunk. -/
theorem stepFacts_chunk {cfg : Config} (F : ChunkFacts cfg)
    (hp : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels → 0 < cfg.fanout ℓ) (h : Nat) :
    HierarchyLevelOneProof.StepFacts (chunkConfig cfg h) := by
  intro ℓ h1 hL
  refine ⟨F.seed_succ ℓ hL h1, hp ℓ h1 hL, ?_⟩
  change (chunkConfig cfg h).ordinals ℓ / cfg.fanout ℓ ≤
    (chunkConfig cfg h).ordinals (ℓ + 1)
  rw [ordinals_chunk F h ℓ h1 hL.le,
    ordinals_chunk F h (ℓ + 1) (by omega) hL, F.scale ℓ hL h1]
  apply Nat.div_le_of_le_mul
  have hb := hp ℓ h1 hL
  generalize cfg.fanout ℓ = b at hb ⊢
  generalize cfg.ordinals (ℓ + 1) - 1 = q
  calc
    h * (b * q) + 1 ≤ h * (b * q) + b := by omega
    _ = b * (h * q + 1) := by ring

theorem invariant (h : Nat) : HierarchyInvariantFor (geometry31.chunk h) := by
  intro N tr hN hT hU words
  exact HierarchyInvariantProof.contractsFor (geometry31.chunk h)
    (lowFacts_horizon HierarchyInvariant31Proof.lowFacts (h * 2 ^ 32))
    (topFacts_chunk (HierarchyInvariantProof.TopFacts.of_compatible Geometry31.1) h)
    hN hT hU words

theorem locality (h : Nat) :
    HierarchyLocalityFor (chunkConfig config31 h) (geometry31.chunk h).shapes :=
  HierarchyLocalityProof.localityFor _ _
    (HierarchyLocalityChunksProof.timeFacts_chunk HierarchyLaws31Proof.timeFacts h)

theorem stepFacts (h : Nat) : HierarchyLevelOneProof.StepFacts (chunkConfig config31 h) :=
  stepFacts_chunk chunkFacts31
    (fun ℓ h1 hL => by have := (HierarchyInvariant31Proof.lowFacts.fan ℓ h1 hL).1; omega) h

theorem levelOne (h : Nat) : HierarchyLevelOneFor (chunkConfig config31 h) keyCapacity31 :=
  HierarchyLevelOneProof.levelOneFor _ _ (stepFacts h) rfl

theorem sepLaw (h : Nat) : HierarchySepLawFor (geometry31.chunk h) :=
  HierarchySepLawProof.sepLawFor _
    (HierarchySepLawChunksProof.good_chunk HierarchyLaws31Proof.good chunkFacts31 h)
    (HierarchySepLawChunksProof.rowsMatch_chunk h Inventory31.2.2.1)
    HierarchyLaws31Proof.rowOK rfl (invariant h) (locality h) OldWordDensity

theorem topLaw (h : Nat) : HierarchyTopLawFor (geometry31.chunk h) :=
  HierarchyTopLawProof.topLawFor _ (stepFacts h)
    (HierarchyTopLawChunksProof.carryFacts_chunk chunkFacts31 h)
    rfl (by change 2 ≤ config31.levels; decide +kernel)
    (by change top31.k + top31.e ≤ 64; decide +kernel)
    (by change prep31.k ≤ 64; decide +kernel) (by change init31.k ≤ 64; decide +kernel)
    (HierarchyTopLawChunksProof.win_chunk chunkFacts31 h) (invariant h) (locality h)

end RebuildBound.HierarchyLawsChunks31Proof

theorem RebuildBound.HierarchyLawsChunks31 : RebuildBound.Spec.HierarchyLawsChunks31_statement := by
  intro h _
  exact ⟨HierarchyLawsChunks31Proof.invariant h, HierarchyLawsChunks31Proof.locality h,
    HierarchyLawsChunks31Proof.levelOne h, HierarchyLawsChunks31Proof.sepLaw h,
    HierarchyLawsChunks31Proof.topLaw h⟩
