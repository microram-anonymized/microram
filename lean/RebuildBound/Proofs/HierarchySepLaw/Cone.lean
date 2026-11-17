import RebuildBound.Spec.Hierarchy

/-! # HierarchySepLaw: the horizon's coordinates and the past cones.

At a configuration meeting `Good` (checked by `decide` at both selected
configurations): the terminal coordinate of an in-range ordinal is a
coordinate of the horizon (`familyOf_inC`); the cone of a level-`ℓ < L` table
at an ordinal before the level's last potential one lies in the horizon
(`cone_inC`), below the top (`cone_lt`); consecutive ordinals of a level have different families
(`familyOf_pred_ne`, by the level-one time). -/

namespace RebuildBound.HierarchySepLawProof
open Model Model.Hierarchy Spec

/-- The product `b_1 ⋯ b_(ℓ-1)`. -/
def prodBelow (cfg : Config) (ℓ : Nat) : Nat := (cfg.fanouts.take (ℓ - 1)).foldr (· * ·) 1

/-- The arithmetic of a configuration the cone argument uses. -/
def Good (cfg : Config) : Prop :=
  (∀ ℓ < cfg.levels, 1 ≤ ℓ → 2 ≤ cfg.fanout ℓ ∧ cfg.seed ℓ = cfg.fanout ℓ * cfg.seed (ℓ + 1) ∧
    (cfg.seed ℓ + cfg.ordinals ℓ) / cfg.fanout ℓ ≤ cfg.seed (ℓ + 1) + cfg.ordinals (ℓ + 1) ∧
    prodBelow cfg (ℓ + 1) = prodBelow cfg ℓ * cfg.fanout ℓ) ∧
  (∀ ℓ < cfg.levels, 2 ≤ ℓ → (cfg.seed ℓ + cfg.ordinals ℓ - 1) * cfg.fanout (ℓ - 1) <
    cfg.seed (ℓ - 1) + cfg.ordinals (ℓ - 1)) ∧
  (∀ ℓ < cfg.levels + 1, 0 < prodBelow cfg ℓ)

theorem good_uniform : Good uniformConfig := by
  unfold Good; decide +kernel

theorem good_half : Good halfFanoutConfig := by
  unfold Good; decide +kernel


/-- In the horizon: a level `1 … L` and an ordinal from the seed to the last
potential one. -/
def InC (cfg : Config) (q : Nat × Nat) : Prop :=
  1 ≤ q.1 ∧ q.1 ≤ cfg.levels ∧ cfg.seed q.1 ≤ q.2 ∧ q.2 ≤ cfg.seed q.1 + cfg.ordinals q.1

theorem mem_coordinates (cfg : Config) (q : Nat × Nat) : q ∈ cfg.coordinates ↔ InC cfg q := by
  obtain ⟨ℓ, v⟩ := q
  have hL : 1 ≤ cfg.levels := by simp [Config.levels]
  simp only [Config.coordinates, Config.ordinaryLevels, List.mem_flatMap, List.mem_append,
    List.mem_map, List.mem_range, List.mem_singleton, Prod.mk.injEq, InC]
  constructor
  · rintro ⟨ℓ', hℓ', i, hi, rfl, rfl⟩
    rcases hℓ' with ⟨j, hj, rfl⟩ | rfl
    · exact ⟨by omega, by omega, by omega, by omega⟩
    · exact ⟨by omega, by omega, by omega, by omega⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨ℓ, ?_, v - cfg.seed ℓ, by omega, rfl, by omega⟩
    by_cases hl : ℓ = cfg.levels
    · exact Or.inr hl
    · exact Or.inl ⟨ℓ - 1, by omega, by omega⟩

theorem familyOfAux_inC {cfg : Config} (hg : Good cfg) :
    ∀ fuel ℓ v, InC cfg (ℓ, v) → InC cfg (familyOfAux cfg fuel ℓ v)
  | 0, ℓ, v, h => by simpa [familyOfAux] using h
  | fuel + 1, ℓ, v, h => by
    simp only [familyOfAux]
    split_ifs with hc
    · obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨hb, hs, hu, -⟩ := hg.1 ℓ hc.1 h1
      apply familyOfAux_inC hg fuel
      refine ⟨by omega, by omega, ?_, ?_⟩
      · show cfg.seed (ℓ + 1) ≤ v / cfg.fanout ℓ
        rw [Nat.le_div_iff_mul_le (by omega)]
        rw [hs] at h3
        simpa [Nat.mul_comm] using h3
      · exact (Nat.div_le_div_right h4).trans hu
    · exact h

theorem familyOf_inC {cfg : Config} (hg : Good cfg) {ℓ v : Nat} (h : InC cfg (ℓ, v)) :
    InC cfg (familyOf cfg ℓ v) := familyOfAux_inC hg _ _ _ h

theorem familyOfAux_time {cfg : Config} (hg : Good cfg) :
    ∀ fuel ℓ v, 1 ≤ ℓ →
      time cfg (familyOfAux cfg fuel ℓ v).1 (familyOfAux cfg fuel ℓ v).2 = time cfg ℓ v
  | 0, ℓ, v, _ => by simp [familyOfAux]
  | fuel + 1, ℓ, v, h1 => by
    simp only [familyOfAux]
    split_ifs with hc
    · obtain ⟨hb, -, -, hp⟩ := hg.1 ℓ hc.1 h1
      rw [familyOfAux_time hg fuel (ℓ + 1) (v / cfg.fanout ℓ) (by omega)]
      have hdvd : cfg.fanout ℓ ∣ v := Nat.dvd_of_mod_eq_zero hc.2
      show v / cfg.fanout ℓ * prodBelow cfg (ℓ + 1) = v * prodBelow cfg ℓ
      rw [hp, ← Nat.mul_assoc, Nat.mul_comm (v / cfg.fanout ℓ) (prodBelow cfg ℓ),
        Nat.mul_assoc, Nat.div_mul_cancel hdvd, Nat.mul_comm]
    · rfl

/-- Consecutive ordinals of a level route under different families. -/
theorem familyOf_pred_ne {cfg : Config} (hg : Good cfg) {ℓ o : Nat} (h1 : 1 ≤ ℓ)
    (hL : ℓ ≤ cfg.levels) (ho : 1 ≤ o) : familyOf cfg ℓ (o - 1) ≠ familyOf cfg ℓ o := by
  intro h
  have ht := familyOfAux_time hg cfg.levels ℓ (o - 1) h1
  have ht' := familyOfAux_time hg cfg.levels ℓ o h1
  have hpos := hg.2.2 ℓ (by omega)
  unfold familyOf at h
  rw [h, ht'] at ht
  change o * prodBelow cfg ℓ = (o - 1) * prodBelow cfg ℓ at ht
  have := Nat.eq_of_mul_eq_mul_right hpos ht
  omega

/-- The cone of a table before a level's last potential ordinal lies in the
horizon (and so do its coordinates' families, `familyOf_inC`). -/
theorem cone_inC {cfg : Config} (hg : Good cfg) :
    ∀ ℓ v, 1 ≤ ℓ → ℓ < cfg.levels → v < cfg.seed ℓ + cfg.ordinals ℓ →
      ∀ q ∈ cone cfg ℓ v, InC cfg q := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ihℓ =>
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ihv =>
  intro h1 hL hv q hq
  rw [cone] at hq
  split_ifs at hq with hb hl h1'
  · omega
  · simp at hq
  · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | hq
    · exact ⟨h1, hL.le, show cfg.seed ℓ ≤ v by omega, show v ≤ cfg.seed ℓ + cfg.ordinals ℓ by omega⟩
    · exact ihv (v - 1) (by omega) h1 hL (by omega) q hq
  · simp only [List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · exact ⟨h1, hL.le, show cfg.seed ℓ ≤ v by omega, show v ≤ cfg.seed ℓ + cfg.ordinals ℓ by omega⟩
    · exact ihv (v - 1) (by omega) h1 hL (by omega) q hq
    · have hc := hg.2.1 ℓ hL (by omega)
      refine ihℓ (ℓ - 1) (by omega) (v * cfg.fanout (ℓ - 1)) (by omega) (by omega) ?_ q hq
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hc

theorem cone_lt {cfg : Config} :
    ∀ ℓ v, ℓ < cfg.levels → ∀ q ∈ cone cfg ℓ v, q.1 < cfg.levels := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ihℓ =>
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ihv =>
  intro hL q hq
  rw [cone] at hq
  split_ifs at hq with hb hl h1'
  · omega
  · simp at hq
  · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | hq
    · exact hL
    · exact ihv (v - 1) (by omega) hL q hq
  · simp only [List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · exact hL
    · exact ihv (v - 1) (by omega) hL q hq
    · exact ihℓ (ℓ - 1) (by omega) _ (by omega) q hq

/-- A potential ordinary job's level and ordinal. -/
theorem mem_potential {cfg : Config} {ℓ o : Nat} (h : JobId.ordinary ℓ o ∈ cfg.potentialJobs) :
    1 ≤ ℓ ∧ ℓ < cfg.levels ∧ cfg.seed ℓ < o ∧ o ≤ cfg.seed ℓ + cfg.ordinals ℓ := by
  simp only [Config.potentialJobs, Config.ordinaryLevels, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_range] at h
  rcases h with (⟨ℓ', ⟨j, hj, rfl⟩, i, hi, he⟩ | ⟨i, hi, he⟩) | he
  · cases he
    exact ⟨by omega, by omega, by omega, by omega⟩
  · simp at he
  · split_ifs at he <;> simp at he

end RebuildBound.HierarchySepLawProof
