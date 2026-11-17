import RebuildBound.Proofs.HierarchyLocality.Table

/-! # HierarchyLocality: a job's family is the family of no coordinate of its previous cone

The level-one time `time ℓ v = v · P_ℓ` is kept by every forward, never grows
along a cone, and strictly grows from `(ℓ, v - 1)` to `(ℓ, v)`. -/

namespace RebuildBound.HierarchyLocalityProof
open Model Model.DirectJob Model.Hierarchy Spec

/-- The product `P_ℓ = b_1 ⋯ b_(ℓ-1)`. -/
def prodTo (cfg : Config) (ℓ : Nat) : Nat := (cfg.fanouts.take (ℓ - 1)).foldr (· * ·) 1

theorem time_eq (cfg : Config) (ℓ v : Nat) : time cfg ℓ v = v * prodTo cfg ℓ := rfl

/-- The configuration facts the argument uses. -/
structure TimeFacts (cfg : Config) : Prop where
  seed : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels → cfg.seed ℓ = cfg.fanout ℓ * cfg.seed (ℓ + 1)
  prod : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels → prodTo cfg (ℓ + 1) = prodTo cfg ℓ * cfg.fanout ℓ
  pos : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ cfg.levels → 0 < prodTo cfg ℓ

theorem familyOfAux_time (cfg : Config) (hf : TimeFacts cfg) :
    ∀ fuel ℓ v, 1 ≤ ℓ →
      time cfg (familyOfAux cfg fuel ℓ v).1 (familyOfAux cfg fuel ℓ v).2 = time cfg ℓ v
  | 0, ℓ, v, _ => rfl
  | fuel + 1, ℓ, v, h1 => by
    unfold familyOfAux
    split_ifs with hv
    · rw [familyOfAux_time cfg hf fuel (ℓ + 1) _ (by omega), time_eq, time_eq, hf.prod ℓ h1 hv.1,
        ← Nat.mul_assoc, Nat.mul_right_comm, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hv.2)]
    · rfl

theorem familyOf_time (cfg : Config) (hf : TimeFacts cfg) (ℓ v : Nat) (h1 : 1 ≤ ℓ) :
    time cfg (familyOf cfg ℓ v).1 (familyOf cfg ℓ v).2 = time cfg ℓ v :=
  familyOfAux_time cfg hf _ ℓ v h1

theorem cone_time (cfg : Config) (hf : TimeFacts cfg) :
    ∀ ℓ v, 1 ≤ ℓ → ℓ ≤ cfg.levels → cfg.seed ℓ ≤ v →
      ∀ q ∈ cone cfg ℓ v, 1 ≤ q.1 ∧ time cfg q.1 q.2 ≤ time cfg ℓ v := by
  have hbase : ∀ ℓ v, 1 ≤ ℓ → ℓ ≤ cfg.levels → cfg.seed ℓ ≤ v → v ≤ cfg.seed ℓ →
      ∀ q ∈ cone cfg ℓ v, 1 ≤ q.1 ∧ time cfg q.1 q.2 ≤ time cfg ℓ v := by
    intro ℓ v h1 hL hs hv q hq
    rw [cone_eq, ite_eq_left (Or.inr (Or.inr hv))] at hq
    split_ifs at hq with hl
    · rw [List.mem_singleton] at hq
      subst hq hl
      simp only
      exact ⟨h1, by rw [show v = cfg.seed cfg.levels by omega]⟩
    · simp at hq
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ihℓ =>
  intro v
  induction v with
  | zero => exact fun h1 hL hs => hbase ℓ 0 h1 hL hs (Nat.zero_le _)
  | succ n ihn =>
    intro h1 hL hs q hq
    by_cases hv : n + 1 ≤ cfg.seed ℓ
    · exact hbase ℓ (n + 1) h1 hL hs hv q hq
    have hb : ¬(ℓ = 0 ∨ cfg.levels < ℓ ∨ n + 1 ≤ cfg.seed ℓ) := by omega
    rw [cone_eq, ite_eq_right hb, Nat.add_sub_cancel] at hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨h1, le_rfl⟩
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨hq1, hq2⟩ := ihn h1 hL (by omega) q hq
      refine ⟨hq1, hq2.trans ?_⟩
      rw [time_eq, time_eq]
      exact Nat.mul_le_mul_right _ (Nat.le_succ n)
    · split_ifs at hq with hl
      · simp at hq
      · have hs' : cfg.seed (ℓ - 1) ≤ (n + 1) * cfg.fanout (ℓ - 1) := by
          rw [hf.seed (ℓ - 1) (by omega) (by omega), Nat.sub_add_cancel (by omega), Nat.mul_comm]
          exact Nat.mul_le_mul_right _ (by omega)
        obtain ⟨hq1, hq2⟩ := ihℓ (ℓ - 1) (by omega) _ (by omega) (by omega) hs' q hq
        refine ⟨hq1, hq2.trans (le_of_eq ?_)⟩
        have hp := hf.prod (ℓ - 1) (by omega) (by omega)
        rw [Nat.sub_add_cancel (by omega)] at hp
        rw [time_eq, time_eq, hp, Nat.mul_assoc, Nat.mul_comm (cfg.fanout _)]

theorem family_ne (cfg : Config) (hf : TimeFacts cfg) :
    ∀ ℓ v, 1 ≤ ℓ → ℓ ≤ cfg.levels → cfg.seed ℓ < v →
      ∀ q ∈ cone cfg ℓ (v - 1), familyOf cfg q.1 q.2 ≠ familyOf cfg ℓ v := by
  intro ℓ v h1 hL hs q hq heq
  obtain ⟨hq1, hq2⟩ := cone_time cfg hf ℓ (v - 1) h1 hL (by omega) q hq
  have e1 := familyOf_time cfg hf q.1 q.2 hq1
  have e2 := familyOf_time cfg hf ℓ v h1
  rw [heq, e2] at e1
  have hp := hf.pos ℓ h1 hL
  rw [← e1, time_eq, time_eq] at hq2
  have : (v - 1) * prodTo cfg ℓ < v * prodTo cfg ℓ := Nat.mul_lt_mul_of_pos_right (by omega) hp
  omega

end RebuildBound.HierarchyLocalityProof
