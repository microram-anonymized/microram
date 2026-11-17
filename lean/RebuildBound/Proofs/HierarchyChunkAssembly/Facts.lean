import RebuildBound.Proofs.HierarchyChunk.Arith

/-! # HierarchyChunkAssembly: the arithmetic of the chunk relabelling

Every chunk of `2^32` accesses holds `m_ℓ = cfg.ordinals ℓ - 1` ordinals of
level `ℓ`, a multiple of the fanout below the top; the level-one cycles and
their lengths of `chunkConfig cfg h` in terms of `m_ℓ`. The numeric facts of
the two selected configurations (`HierarchyChunkArith.ChunkFacts`) are checked
by `decide`. -/

namespace RebuildBound.HierarchyChunkAssemblyProof
open Model Model.DirectJob Model.Hierarchy Spec HierarchyChunkArith

section
variable {cfg : Config}

theorem ordinals_pos (c : Config) (ℓ : Nat) : 1 ≤ c.ordinals ℓ := Nat.le_add_left 1 _

/-- The number of full level-one cycles of one chunk. -/
def cyc1 (cfg : Config) : Nat := (cfg.ordinals 1 - 1) / cfg.fanout 1

theorem m1_eq (F : ChunkFacts cfg) : cfg.ordinals 1 - 1 = cyc1 cfg * cfg.fanout 1 :=
  (Nat.div_mul_cancel ⟨_, F.scale 1 (by have := F.levels_ge; omega) le_rfl⟩).symm

/-- `h` chunks hold `h C + 1` level-one cycles. -/
theorem levelOneCycles_chunk (F : ChunkFacts cfg) (h : Nat) :
    (chunkConfig cfg h).levelOneCycles = h * cyc1 cfg + 1 := by
  have hb := F.fanout_pos
  unfold Config.levelOneCycles
  rw [ordinals_chunk F h 1 le_rfl (by have := F.levels_ge; omega), m1_eq F, chunk_fanout,
    show h * (cyc1 cfg * cfg.fanout 1) + 1 + cfg.fanout 1 - 1 = (h * cyc1 cfg + 1) * cfg.fanout 1 by
      rw [add_mul, one_mul, mul_assoc]; omega]
  exact Nat.mul_div_cancel _ hb

/-- Cycle `c + k C` of `k + 1` chunks has the length of cycle `c` of the first. -/
theorem cycleLength_chunk (F : ChunkFacts cfg) (k c : Nat) :
    (chunkConfig cfg (k + 1)).cycleLength (c + k * cyc1 cfg) = cfg.cycleLength c := by
  unfold Config.cycleLength
  rw [ordinals_chunk F (k + 1) 1 le_rfl (by have := F.levels_ge; omega), chunk_fanout]
  have hm := m1_eq F
  have h1 := ordinals_pos cfg 1
  have e1 : (c + k * cyc1 cfg) * cfg.fanout 1 = c * cfg.fanout 1 + k * (cfg.ordinals 1 - 1) := by
    rw [hm]; ring
  have e2 : (k + 1) * (cfg.ordinals 1 - 1) = k * (cfg.ordinals 1 - 1) + (cfg.ordinals 1 - 1) := by
    ring
  rw [e1, e2]
  congr 1
  omega

end

end RebuildBound.HierarchyChunkAssemblyProof
