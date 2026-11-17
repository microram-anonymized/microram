import RebuildBound.Spec.DirectRemaining
import RebuildBound.Proofs.DirectSelect
import Mathlib.Tactic
namespace RebuildBound
open Model Model.DirectRemaining

theorem DirectRemainingFold : Spec.DirectRemainingFold_statement := by
  intro cap source homes
  induction homes generalizing source with
  | nil => simp [run, clear, DirectB.main]
  | cons xs homes ih =>
    change run cap (clear (xs.take cap) source) homes = _
    rw [ih]
    simp only [clear, List.filter_filter, DirectB.main, List.map_cons, List.flatten_cons]
    apply List.filter_congr
    intro i hi
    simp [Bool.and_comm]

theorem DirectRemainingDrain : Spec.DirectRemainingDrain_statement := by
  intro cap source homes hg
  rw [DirectRemainingFold]
  unfold clear DirectSelect.drain
  apply List.filter_congr
  intro i hi
  have hmem := (DirectBConservation cap homes).trans hg.2.1
  have hcover : i ∈ (DirectB.main cap homes).flatten ∨ i ∈ DirectB.residual cap homes := by
    simpa only [List.mem_append] using hmem.mem_iff.mpr hi
  have hd := (DirectBUnique cap homes (hg.2.1.nodup_iff.mpr hg.1)).disjoint
  have hdis : ¬ (i ∈ (DirectB.main cap homes).flatten ∧ i ∈ DirectB.residual cap homes) := by
    intro h
    exact List.disjoint_left.mp hd h.1 h.2
  simp only [decide_eq_decide]
  tauto

theorem DirectRemainingOccupancy : Spec.DirectRemainingOccupancy_statement := by
  intro cap source homes hg
  rw [DirectRemainingDrain cap source homes hg]
  exact DirectSelectOccupancy cap source homes hg

theorem DirectRemainingChunks : Spec.DirectRemainingChunks_statement := by
  intro cap chunks homes
  simp_rw [DirectRemainingFold cap]
  exact List.filter_flatten.symm

theorem DirectRemainingFreshHome : Spec.DirectRemainingFreshHome_statement := by
  intro cap source homes home h hf
  rw [DirectRemainingFold]
  simp only [clear, List.filter_filter]
  apply List.filter_congr
  intro i hi
  have hn : i ∈ (DirectB.main cap homes).flatten → home i ≠ h := by
    intro hm
    obtain ⟨xs, hx, hm⟩ := List.mem_flatten.mp hm
    obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp hx
    exact hf ys hy i (List.mem_of_mem_take hm)
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  tauto

example : run 1 [0, 1, 2, 3] [[1, 3], [0, 2]] = [2, 3] := by decide
example : run 0 [0, 1, 2] [[1], [0, 2]] = [0, 1, 2] := by decide
end RebuildBound
