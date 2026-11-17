import RebuildBound.Spec.DirectDrain
import RebuildBound.Proofs.DirectB
import Mathlib.Tactic
namespace RebuildBound
open Model.DirectDrain

theorem DirectDrainRunExact {α : Type} (capacity : Nat) (chunks : List (List α)) :
    ∀ state, state.length ≤ capacity →
    run capacity state chunks =
      if (state ++ chunks.flatten).length ≤ capacity
      then some (state ++ chunks.flatten) else none := by
  induction chunks with
  | nil => intro state h; simp [run, h]
  | cons chunk chunks ih =>
    intro state h
    by_cases hc : (state ++ chunk).length ≤ capacity
    · simp only [run, appendChecked, ite_eq_left hc, Option.bind_some]
      rw [ih _ hc]
      simp only [List.flatten_cons, List.append_assoc]
    · have ht : ¬ (state ++ (chunk :: chunks).flatten).length ≤ capacity := by
        simp only [List.flatten_cons, List.length_append] at *
        omega
      simp only [run, appendChecked, ite_eq_right hc, Option.bind_none, ite_eq_right ht]

theorem DirectDrainExact : Spec.DirectDrainExact_statement := by
  intro capacity state chunks h
  exact DirectDrainRunExact capacity chunks state h

theorem DirectDrainRechunk : Spec.DirectDrainRechunk_statement := by
  intro capacity state first second hs he
  rw [DirectDrainExact _ _ _ hs, DirectDrainExact _ _ _ hs, he]

-- Output tier width is used directly at digit one, even when wider than 64.
example : run (tierCapacity 1 128) [] [List.range 65] = some (List.range 65) := by decide
example : run (tierCapacity 2 128) [] [List.range 65] = none := by decide
-- Distributed residuals exceed a single producer bucket together.
example : run (tierCapacity 2 128) [] [List.range 33, List.range 32] = none := by decide
-- The initial-state bound in Exact is necessary, even for an empty drain.
example : run 0 [1] [] = some [1] := by decide
end RebuildBound
