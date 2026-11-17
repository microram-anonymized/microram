import RebuildBound.Spec.LaneFold
import RebuildBound.Proofs.DirectDrain
import Mathlib.Tactic
namespace RebuildBound
open Model

theorem LaneFoldExact : Spec.LaneFoldExact_statement := by
  intro α laneCapacity capacity init lanes hw hinit
  unfold LaneFold.run
  split_ifs with hall
  · rw [DirectDrainRunExact capacity lanes.flatten init hinit]
    rfl
  · -- some lane overflows its copy, hence the whole stage overflows the phase stash
    simp only [List.all_eq_true, decide_eq_true_eq, not_forall, not_le] at hall
    obtain ⟨lane, hmem, hlane⟩ := hall
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hmem
    have : ¬ (init ++ (s ++ lane :: t).flatten.flatten).length ≤ capacity := by
      simp only [List.flatten_append, List.flatten_cons, List.length_append] at *
      omega
    simp only [DirectDrain.appendChecked, this, ite_false]

theorem LaneFoldNarrow : Spec.LaneFoldNarrow_statement := by
  intro laneCapacity capacity h
  refine ⟨[[List.replicate capacity 0]], ?_, ?_⟩
  · simp [LaneFold.run, h]
  · simp [DirectDrain.appendChecked]

end RebuildBound
