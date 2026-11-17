import RebuildBound.Spec.HierarchyExposure

open scoped ENNReal
namespace RebuildBound
open Model Spec

namespace HierarchyExposureProof

lemma seed_mul (cfg : Config) (ℓ : Nat) (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels) :
    cfg.seed ℓ = cfg.fanout ℓ * cfg.seed (ℓ + 1) := by
  have h : ℓ - 1 < cfg.fanouts.length := by simp [Config.levels] at hL; omega
  simp only [Config.seed]
  split
  · rw [List.drop_eq_getElem_cons h]
    simp only [List.foldr_cons, Nat.add_sub_cancel]
    have he : cfg.fanout ℓ = cfg.fanouts[ℓ - 1] := by
      simp [Config.fanout, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rw [he, show ℓ - 1 + 1 = ℓ by omega]
    ring
  · simp

/-- Translating both endpoints by whole digit cycles preserves the count. -/
lemma count_seed_zero (b s m d : Nat) (hs : b ∣ s) :
    (((s : Int) + m - d).fdiv b - ((s : Int) - d).fdiv b).toNat =
      (((m : Int) - d).fdiv b - (-(d : Int)).fdiv b).toNat := by
  by_cases hb : b = 0
  · subst b
    simp
  obtain ⟨q, rfl⟩ := hs
  have hb' : (b : Int) ≠ 0 := by exact_mod_cast hb
  simp only [Nat.cast_mul]
  rw [show (b : Int) * q + m - d = (b : Int) * q + (m - d) by ring,
    Int.mul_add_fdiv_left _ _ hb', Int.mul_sub_fdiv_left _ _ hb']
  congr 1
  omega

lemma ordinaryCount_empty (cfg : Config) (ℓ d : Nat)
    (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels) :
    cfg.ordinaryCount ℓ d = ({cfg with initialized := false} : Config).ordinaryCount ℓ d := by
  unfold Config.ordinaryCount
  rw [count_seed_zero (cfg.fanout ℓ) (cfg.seed ℓ) (cfg.ordinals ℓ) d
    ⟨cfg.seed (ℓ + 1), seed_mul cfg ℓ h1 hL⟩]
  simp only [Config.seed, Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, zero_add, zero_sub]
  rfl

end HierarchyExposureProof

open HierarchyExposureProof in
theorem HierarchyExposure : HierarchyExposure_statement := by
  intro cfg
  have hcounts : (cfg.ordinaryLevels.flatMap fun ℓ =>
      (List.range (cfg.fanout ℓ)).map fun i =>
        (JobClass.ordinary ℓ (i + 1), cfg.ordinaryCount ℓ (i + 1))) =
      (cfg.ordinaryLevels.flatMap fun ℓ =>
      (List.range (cfg.fanout ℓ)).map fun i =>
        (JobClass.ordinary ℓ (i + 1), ({cfg with initialized := false} : Config).ordinaryCount ℓ (i + 1))) := by
    simp only [List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro ℓ hℓ
    apply List.map_congr_left
    intro i _
    have h : 1 ≤ ℓ ∧ ℓ < cfg.levels := by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hℓ
      have := List.mem_range.mp hk
      omega
    rw [ordinaryCount_empty cfg ℓ (i + 1) h.1 h.2]
  unfold Config.exposures
  rw [hcounts]
  simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
  rfl

theorem HierarchyExposureBudget : HierarchyExposureBudget_statement := by
  intro cfg B
  have heq : cfg.exposureSum B = ({cfg with initialized := false} : Config).exposureSum B +
      (if cfg.initialized then B .initialization else 0) := by
    unfold Config.exposureSum
    rw [HierarchyExposure cfg, List.map_append, List.sum_append]
    cases cfg.initialized <;> simp
  exact ⟨heq, heq ▸ le_self_add⟩

end RebuildBound
