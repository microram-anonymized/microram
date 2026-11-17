import RebuildBound.Spec.DirectSelect
import RebuildBound.Proofs.DirectB
import RebuildBound.Proofs.DirectDrain
import Mathlib.Tactic
namespace RebuildBound
open Model Model.DirectSelect

private theorem residual_sublist (cap : Nat) (homes : List (List Nat)) :
    (DirectB.residual cap homes).Sublist homes.flatten := by
  simpa only [DirectB.residual, List.flatMap_def, List.map_id] using
    List.Sublist.flatMap_right (g := id) homes (fun xs _ => List.drop_sublist cap xs)

/-- Conservation uses unique occurrence indices and grouping permutation only.
Stable within-home order remains part of the operational `Grouped` contract. -/
theorem DirectSelectDrainOfPerm (cap : Nat) (source : List Nat) (homes : List (List Nat))
    (hs : source.Nodup) (hp : homes.flatten.Perm source) :
    (drain cap source homes).Perm (DirectB.residual cap homes) := by
  have hr : (DirectB.residual cap homes).Nodup :=
    (hp.nodup_iff.mpr hs).sublist (residual_sublist cap homes)
  apply (List.perm_ext_iff_of_nodup (hs.filter _) hr).mpr
  intro i
  simp only [List.mem_filter, decide_eq_true_eq]
  exact and_iff_right_of_imp fun h => hp.mem_iff.mp ((residual_sublist cap homes).subset h)

theorem DirectSelectOccupancyOfPerm (cap : Nat) (source : List Nat)
    (homes : List (List Nat)) (hs : source.Nodup) (hp : homes.flatten.Perm source) :
    (drain cap source homes).length = DirectB.excess cap homes :=
  (DirectSelectDrainOfPerm cap source homes hs hp).length_eq.trans
    (DirectBResidual cap homes)

theorem DirectSelectConservationOfPerm (cap : Nat) (source : List Nat)
    (homes : List (List Nat)) (hs : source.Nodup) (hp : homes.flatten.Perm source) :
    ((DirectB.main cap homes).flatten ++ drain cap source homes).Perm source :=
  ((DirectSelectDrainOfPerm cap source homes hs hp).append_left _).trans
    ((DirectBConservation cap homes).trans hp)

theorem DirectSelectDrain : Spec.DirectSelectDrain_statement := by
  intro cap source homes hg
  exact DirectSelectDrainOfPerm cap source homes hg.1 hg.2.1

theorem DirectSelectStable : Spec.DirectSelectStable_statement := by
  intro cap source homes
  exact List.filter_sublist

theorem DirectSelectOccupancy : Spec.DirectSelectOccupancy_statement := by
  intro cap source homes hg
  exact DirectSelectOccupancyOfPerm cap source homes hg.1 hg.2.1

theorem DirectSelectConservation : Spec.DirectSelectConservation_statement := by
  intro cap source homes hg
  exact DirectSelectConservationOfPerm cap source homes hg.1 hg.2.1

theorem DirectSelectUnique : Spec.DirectSelectUnique_statement := by
  intro cap source homes hg
  exact (DirectSelectConservation cap source homes hg).nodup_iff.mpr hg.1

-- Interleaving witnesses unequal drain/home order with exact occupancy.
example : Grouped [0, 1, 2, 3] [[1, 3], [0, 2]] := by
  refine ⟨by decide, by decide, ?_⟩
  intro xs hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> decide
example : drain 1 [0, 1, 2, 3] [[1, 3], [0, 2]] = [2, 3] := by decide
example : DirectB.residual 1 [[1, 3], [0, 2]] = [3, 2] := by decide
example : drain 1 [0, 1, 2, 3] [[1, 3], [0, 2]] ≠
    DirectB.residual 1 [[1, 3], [0, 2]] := by decide
example : drain 0 [0, 1, 2] [[1], [0, 2]] = [0, 1, 2] := by decide
example : drain 3 [0, 1, 2] [[1], [0, 2]] = [] := by decide
end RebuildBound
