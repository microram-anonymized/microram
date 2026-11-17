import RebuildBound.Spec.DirectGroups
import RebuildBound.Proofs.DirectSelect
import Mathlib.Tactic
namespace RebuildBound
open Model Model.DirectGroups

theorem DirectGroupsPermutation : Spec.DirectGroupsPermutation_statement := by
  intro U home source hb
  apply List.perm_iff_count.mpr
  intro i
  simp only [groups, List.count_flatten, List.map_map, Function.comp_def]
  have he : (List.range U).map (fun h => List.count i
      (source.filter (fun j => home j == h))) =
      (List.range U).map (fun h => if home i == h then List.count i source else 0) := by
    apply List.map_congr_left
    intro h _
    by_cases heq : home i = h
    · simp [heq, List.count_filter]
    · simp only [beq_iff_eq, heq, ↓reduceIte]
      exact List.count_eq_zero.mpr (by simp [heq])
  rw [he, ← List.sum_toFinset _ List.nodup_range]
  by_cases hi : i ∈ source
  · simp [List.mem_range.mpr (hb i hi)]
  · simp [List.count_eq_zero.mpr hi]

theorem DirectGroupsGrouped : Spec.DirectGroupsGrouped_statement := by
  intro U home source hn hb
  refine ⟨hn, DirectGroupsPermutation U home source hb, ?_⟩
  intro xs hx
  obtain ⟨h, _, rfl⟩ := List.mem_map.mp hx
  exact List.filter_sublist

-- Interleaved input retains within-home order; duplicate multiplicity is preserved.
example : groups 3 (fun i => i % 3) [4, 0, 5, 1, 3, 2] =
    [[0, 3], [4, 1], [5, 2]] := by decide
example : (groups 2 (fun i => i % 2) [0, 1, 0, 1]).flatten.Perm [0, 1, 0, 1] := by
  apply DirectGroupsPermutation
  intro i hi
  exact Nat.mod_lt _ (by decide)

end RebuildBound
