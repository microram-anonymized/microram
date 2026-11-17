import RebuildBound.Spec.DirectB
import Mathlib.Tactic
namespace RebuildBound
open Model.DirectB

theorem DirectBResidual : Spec.DirectBResidual_statement := by
  intro cap homes
  simp [Model.DirectB.residual, excess, List.length_flatten, List.map_map,
    Function.comp_def, List.length_drop]

theorem DirectBHome : Spec.DirectBHome_statement := by
  intro word U stride radix
  simp [finalHome, Nat.add_mod, Nat.mul_mod, Nat.mod_mod_of_dvd,
    show U ∣ U * stride from dvd_mul_right U stride]

theorem DirectBConservation : Spec.DirectBConservation_statement := by
  intro cap homes
  simpa [main, Model.DirectB.residual, List.flatMap, List.take_append_drop] using
    (List.flatMap_append_perm homes (List.take cap) (List.drop cap))

theorem DirectBUnique : Spec.DirectBUnique_statement := by
  intro cap homes h
  exact (DirectBConservation cap homes).nodup_iff.mpr h

-- Kernel-evaluated examples: distributed excess.
example : residual 1 [[0, 1], [2, 3]] = [1, 3] := by decide
example : excess 1 [[0, 1], [2, 3]] = 2 := by decide
example : residual 2 [[0, 1], [], [2]] = [] := by decide
example : finalHome 31 4 2 3 % 4 = 31 % 4 := by decide
example : excess 2 [[0, 1, 2, 3], [4, 5, 6, 7]] = 4 := by decide
end RebuildBound
