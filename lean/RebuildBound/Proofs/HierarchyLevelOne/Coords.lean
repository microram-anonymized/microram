import RebuildBound.Spec.Hierarchy

/-! # HierarchyLevelOne: level one's families are coordinates of the horizon. -/

namespace RebuildBound.HierarchyLevelOneProof
open Model Model.Hierarchy Spec

theorem familyOfAux_fst_ge (cfg : Config) :
    ∀ fuel ℓ v, ℓ ≤ (familyOfAux cfg fuel ℓ v).1
  | 0, ℓ, v => by simp [familyOfAux]
  | fuel + 1, ℓ, v => by
    unfold familyOfAux
    split_ifs
    · exact Nat.le_of_succ_le (familyOfAux_fst_ge cfg fuel (ℓ + 1) _)
    · exact le_rfl

theorem familyOfAux_injective (cfg : Config) :
    ∀ fuel ℓ v w, familyOfAux cfg fuel ℓ v = familyOfAux cfg fuel ℓ w → v = w
  | 0, ℓ, v, w, h => by simpa [familyOfAux] using h
  | fuel + 1, ℓ, v, w, h => by
    unfold familyOfAux at h
    split_ifs at h with hv hw hw
    · have := familyOfAux_injective cfg fuel (ℓ + 1) _ _ h
      rw [← Nat.div_add_mod v (cfg.fanout ℓ), ← Nat.div_add_mod w (cfg.fanout ℓ), hv.2, hw.2,
        this]
    · have := familyOfAux_fst_ge cfg fuel (ℓ + 1) (v / cfg.fanout ℓ)
      rw [h] at this
      simp at this
    · have := familyOfAux_fst_ge cfg fuel (ℓ + 1) (w / cfg.fanout ℓ)
      rw [← h] at this
      simp at this
    · simpa using h

/-- The per-level facts of a configuration that the forwards preserve. -/
def StepFacts (cfg : Config) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels →
    cfg.seed ℓ = cfg.fanout ℓ * cfg.seed (ℓ + 1) ∧ 0 < cfg.fanout ℓ ∧
      cfg.ordinals ℓ / cfg.fanout ℓ ≤ cfg.ordinals (ℓ + 1)

/-- A coordinate of a level of the horizon. -/
def InRange (cfg : Config) (p : Nat × Nat) : Prop :=
  1 ≤ p.1 ∧ p.1 ≤ cfg.levels ∧ cfg.seed p.1 ≤ p.2 ∧ p.2 ≤ cfg.seed p.1 + cfg.ordinals p.1

theorem familyOfAux_inRange (cfg : Config) (hs : StepFacts cfg) :
    ∀ fuel ℓ v, InRange cfg (ℓ, v) → InRange cfg (familyOfAux cfg fuel ℓ v)
  | 0, ℓ, v, h => by simpa [familyOfAux] using h
  | fuel + 1, ℓ, v, h => by
    unfold familyOfAux
    split_ifs with hv
    · apply familyOfAux_inRange cfg hs fuel
      obtain ⟨h1, -, h3, h4⟩ := h
      obtain ⟨hseed, hb, hord⟩ := hs ℓ h1 hv.1
      refine ⟨by omega, by omega, ?_, ?_⟩
      · show cfg.seed (ℓ + 1) ≤ v / cfg.fanout ℓ
        rw [Nat.le_div_iff_mul_le hb, Nat.mul_comm, ← hseed]
        exact h3
      · show v / cfg.fanout ℓ ≤ cfg.seed (ℓ + 1) + cfg.ordinals (ℓ + 1)
        calc v / cfg.fanout ℓ ≤ (cfg.seed ℓ + cfg.ordinals ℓ) / cfg.fanout ℓ :=
              Nat.div_le_div_right h4
          _ = cfg.seed (ℓ + 1) + cfg.ordinals ℓ / cfg.fanout ℓ := by
              rw [hseed, Nat.add_comm, Nat.add_mul_div_left _ _ hb, Nat.add_comm]
          _ ≤ _ := Nat.add_le_add_left hord _
    · exact h

theorem mem_coordinates (cfg : Config) (p : Nat × Nat) (h : InRange cfg p) :
    p ∈ cfg.coordinates := by
  obtain ⟨ℓ, v⟩ := p
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  simp only [Config.coordinates, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    Config.ordinaryLevels, List.mem_singleton, Prod.mk.injEq]
  refine ⟨ℓ, ?_, v - cfg.seed ℓ, by omega, rfl, by omega⟩
  by_cases hl : ℓ = cfg.levels
  · exact Or.inr hl
  · exact Or.inl ⟨ℓ - 1, by omega, by omega⟩

end RebuildBound.HierarchyLevelOneProof
