import RebuildBound.Spec.HierarchyChunk
import RebuildBound.Proofs.HierarchyCovering.Basic

/-! # The arithmetic of the chunk configurations, shared by the chunk packages

`chunkConfig cfg h` changes only the horizon, so its levels, seeds, fanouts,
carries and periods are those of `cfg` (definitionally; the `chunk_*` lemmas).
Every carry's positions divide `2^32`, so each level's ordinal count scales:
`m_ℓ(h · 2^32) - 1 = h · (m_ℓ(2^32) - 1)` (`ordinals_chunk`). The selected
configurations' numeric facts at horizon `2^32` (`ChunkFacts`) are checked by
`decide`; the carry and step inequalities and the level-`ℓ` form of level
one's time bound then hold at every chunk horizon. -/

namespace RebuildBound.HierarchyChunkArith
open Model Model.Hierarchy Spec
open HierarchyCoveringProof (per)

/-- The numeric facts of a selected configuration at horizon `2^32` that the
chunk packages use. `P_ℓ = per cfg ℓ` and `m_ℓ = cfg.ordinals ℓ - 1`. -/
structure ChunkFacts (cfg : Config) : Prop where
  horizon : cfg.horizon = 2 ^ 32
  levels_ge : 2 ≤ cfg.levels
  dvd : ∀ ℓ < cfg.levels + 1, 1 ≤ ℓ → cfg.carryPositions ℓ ∣ 2 ^ 32
  seed_succ : ∀ ℓ < cfg.levels, 1 ≤ ℓ → cfg.seed ℓ = cfg.fanout ℓ * cfg.seed (ℓ + 1)
  scale : ∀ ℓ < cfg.levels, 1 ≤ ℓ →
    cfg.ordinals ℓ - 1 = cfg.fanout ℓ * (cfg.ordinals (ℓ + 1) - 1)
  seed : ∀ ℓ < cfg.levels + 1, 1 ≤ ℓ → cfg.seed ℓ * per cfg ℓ = cfg.seed 1
  ords : ∀ ℓ < cfg.levels + 1, 1 ≤ ℓ → cfg.ordinals 1 - 1 = (cfg.ordinals ℓ - 1) * per cfg ℓ
  per_pos : ∀ ℓ < cfg.levels + 1, 1 ≤ ℓ → 1 ≤ per cfg ℓ
  per_top : 2 ≤ per cfg cfg.levels
  fanout_pos : 0 < cfg.fanout 1

theorem chunkFacts_uniform : ChunkFacts uniformConfig where
  horizon := by decide
  levels_ge := by decide
  dvd := by decide
  seed_succ := by decide
  scale := by decide
  seed := by decide
  ords := by decide
  per_pos := by decide
  per_top := by decide
  fanout_pos := by decide

theorem chunkFacts_half : ChunkFacts halfFanoutConfig where
  horizon := by decide
  levels_ge := by decide
  dvd := by decide
  seed_succ := by decide
  scale := by decide
  seed := by decide
  ords := by decide
  per_pos := by decide
  per_top := by decide
  fanout_pos := by decide

/-! ### The chunk configurations -/

section
variable {cfg : Config}

@[simp] theorem chunk_levels (h : Nat) : (chunkConfig cfg h).levels = cfg.levels := rfl
@[simp] theorem chunk_seed (h : Nat) : (chunkConfig cfg h).seed = cfg.seed := rfl
@[simp] theorem chunk_fanout (h : Nat) : (chunkConfig cfg h).fanout = cfg.fanout := rfl
@[simp] theorem chunk_carryPositions (h : Nat) :
    (chunkConfig cfg h).carryPositions = cfg.carryPositions := rfl
@[simp] theorem chunk_initialized (h : Nat) :
    (chunkConfig cfg h).initialized = cfg.initialized := rfl
@[simp] theorem chunk_per (h : Nat) : per (chunkConfig cfg h) = per cfg := rfl
theorem chunk_jobTime (h : Nat) (j : JobId) : jobTime (chunkConfig cfg h) j = jobTime cfg j := rfl

/-- One chunk is the configuration itself. -/
theorem chunk_one (F : ChunkFacts cfg) : chunkConfig cfg 1 = cfg := by
  unfold chunkConfig
  rw [one_mul, ← F.horizon]

/-- `h` chunks hold `h m_ℓ + 1` potential ordinals of level `ℓ`. -/
theorem ordinals_chunk (F : ChunkFacts cfg) (h ℓ : Nat) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ cfg.levels) :
    (chunkConfig cfg h).ordinals ℓ = h * (cfg.ordinals ℓ - 1) + 1 := by
  show h * 2 ^ 32 / cfg.carryPositions ℓ + 1 = h * (cfg.horizon / cfg.carryPositions ℓ + 1 - 1) + 1
  rw [F.horizon, Nat.add_sub_cancel, Nat.mul_div_assoc _ (F.dvd ℓ (by omega) h1)]

/-- The carry inequality at every chunk horizon: the top ordinal of level `ℓ`
times `b_(ℓ-1)` lies below level `ℓ - 1`'s range. -/
theorem carry_chunk (F : ChunkFacts cfg) (h : Nat) {ℓ : Nat} (h2 : 2 ≤ ℓ) (hL : ℓ ≤ cfg.levels) :
    (cfg.seed ℓ + (chunkConfig cfg h).ordinals ℓ - 1) * cfg.fanout (ℓ - 1) <
      cfg.seed (ℓ - 1) + (chunkConfig cfg h).ordinals (ℓ - 1) := by
  have e : ℓ - 1 + 1 = ℓ := by omega
  have hs := F.seed_succ (ℓ - 1) (by omega) (by omega)
  have hm := F.scale (ℓ - 1) (by omega) (by omega)
  rw [e] at hs hm
  rw [ordinals_chunk F h ℓ (by omega) hL, ordinals_chunk F h (ℓ - 1) (by omega) (by omega), hs, hm]
  generalize cfg.seed ℓ = s
  generalize cfg.ordinals ℓ - 1 = q
  generalize cfg.fanout (ℓ - 1) = b
  have : (s + (h * q + 1) - 1) * b = b * s + h * (b * q) := by
    rw [show s + (h * q + 1) - 1 = s + h * q by omega]; ring
  omega

/-- The step inequality at every chunk horizon: level `ℓ`'s range divided by
`b_ℓ` lies within level `ℓ + 1`'s. -/
theorem step_chunk (F : ChunkFacts cfg) (h : Nat) {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels)
    (hb : 0 < cfg.fanout ℓ) :
    (cfg.seed ℓ + (chunkConfig cfg h).ordinals ℓ) / cfg.fanout ℓ ≤
      cfg.seed (ℓ + 1) + (chunkConfig cfg h).ordinals (ℓ + 1) := by
  rw [ordinals_chunk F h ℓ h1 hL.le, ordinals_chunk F h (ℓ + 1) (by omega) hL, F.scale ℓ hL h1,
    F.seed_succ ℓ hL h1]
  apply Nat.div_le_of_le_mul
  generalize cfg.fanout ℓ = b at hb ⊢
  generalize cfg.seed (ℓ + 1) = s
  generalize cfg.ordinals (ℓ + 1) - 1 = q
  have : b * (s + (h * q + 1)) = b * s + h * (b * q) + b := by ring
  omega

/-- Level one's time bound `s_1 + k m_1 + 1` at level `ℓ`. -/
theorem bound_eq (F : ChunkFacts cfg) (k ℓ : Nat) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ cfg.levels) :
    cfg.seed 1 + (k * (cfg.ordinals 1 - 1) + 1) =
      (cfg.seed ℓ + k * (cfg.ordinals ℓ - 1)) * per cfg ℓ + 1 := by
  rw [← F.seed ℓ (by omega) h1, F.ords ℓ (by omega) h1]
  ring

end

/-! ### Comparing multiples of a period -/

theorem aux_le_succ {o P B : Nat} (hP : 1 ≤ P) (h : o * P ≤ B * P + 1) : o ≤ B + 1 := by
  by_contra hc
  have := Nat.mul_le_mul_right P (show B + 2 ≤ o by omega)
  rw [add_mul] at this
  omega

theorem aux_le {o P B : Nat} (hP : 2 ≤ P) (h : o * P ≤ B * P + 1) : o ≤ B := by
  by_contra hc
  have := Nat.mul_le_mul_right P (show B + 1 ≤ o by omega)
  rw [add_mul, one_mul] at this
  omega

theorem aux_lt {o P B : Nat} (h : B * P + 1 < o * P) : B < o :=
  Nat.lt_of_mul_lt_mul_right (a := P) (by omega)

end RebuildBound.HierarchyChunkArith
