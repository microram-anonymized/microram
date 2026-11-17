import RebuildBound.Spec.ConfigurationFamilyBound
import RebuildBound.Proofs.HierarchyExposure

/-! One initialized numerical exposure sum serves either start. The transport
is symbolic and applies to every member, independently of the finite inventory. -/
open scoped ENNReal
namespace RebuildBound.ConfigurationFamilyBoundProof
open Model Spec Spec.ConfigurationFamily

private theorem classes_empty (cfg : Config) :
    ({cfg with initialized := false} : Config).separatedClasses = cfg.separatedClasses := by
  unfold Config.separatedClasses
  rw [HierarchyExposure cfg]
  cases cfg.initialized <;> simp

private theorem rows_empty (cfg : Config) (stash tier : Nat → Nat) :
    separatedRows {cfg with initialized := false} stash tier = separatedRows cfg stash tier := by
  unfold separatedRows
  rw [classes_empty]
  apply List.map_congr_left
  rintro ⟨ℓ, d⟩ hp
  have hℓ : 1 ≤ ℓ ∧ ℓ < cfg.levels := by
    obtain ⟨⟨c, n⟩, hc, heq⟩ := List.mem_filterMap.mp hp
    cases c with
    | ordinary l k =>
      dsimp only at heq
      split_ifs at heq with hk
      · cases heq
        have hc' : ∃ j ∈ cfg.ordinaryLevels, ∃ i ∈ List.range (cfg.fanout j),
            j = ℓ ∧ i + 1 = d ∧ cfg.ordinaryCount j (i + 1) = n := by
          cases cfg.initialized <;> simpa [Config.exposures, List.mem_flatMap] using hc
        obtain ⟨j, hj, i, hi, rfl, rfl, _⟩ := hc'
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hj
        have := List.mem_range.mp ha
        omega
    | _ => cases heq
  dsimp only
  rw [← HierarchyExposureProof.ordinaryCount_empty cfg ℓ d hℓ.1 hℓ.2]
  rfl

theorem startRows (m : Member) (initialized : Bool) :
    (m.geometry initialized).rows = (m.geometry true).rows ∧
    (m.geometry initialized).cfg.separatedClasses = (m.geometry true).cfg.separatedClasses := by
  cases initialized with
  | false => exact ⟨rows_empty (m.config true) m.stashPages m.tierPages,
      classes_empty (m.config true)⟩
  | true => exact ⟨rfl, rfl⟩

theorem budget_start (m : Member) (initialized : Bool) :
    classBudget m initialized = classBudget m true := by
  have hr := startRows m initialized
  funext c
  cases c with
  | ordinary ℓ d => simp only [classBudget, Config.sepRow, hr.1, hr.2]
  | _ => rfl

theorem exposure_le_initialized (m : Member) (initialized : Bool) :
    (m.config initialized).exposureSum (classBudget m initialized) ≤
      (m.config true).exposureSum (classBudget m true) := by
  rw [budget_start m initialized]
  cases initialized with
  | true => exact le_rfl
  | false => exact (HierarchyExposureBudget (m.config true) (classBudget m true)).2

end RebuildBound.ConfigurationFamilyBoundProof
