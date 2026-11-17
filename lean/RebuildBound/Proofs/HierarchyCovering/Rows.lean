import RebuildBound.Proofs.HierarchyCovering.Basic

/-! # HierarchyCovering: the numeric facts of the selected configurations

Every field of `Facts` is a bounded statement about concrete numbers, checked
by `decide`. -/

namespace RebuildBound.HierarchyCoveringProof
open Model Model.DirectJob Model.Hierarchy Spec

theorem facts_uniform : Facts uniformConfig uniformSeparated where
  levels_ge := by decide
  levels_le := by decide
  fanout_ge := by decide
  seed_dvd := by decide
  seed_succ := by decide
  per_one := by decide
  per_succ := by decide
  per_pos := by decide
  horizon := by decide
  rowA := by decide
  rowCarry := by decide
  rowOne := by decide
  topB := by decide
  initPrep := by decide
  topPrep := by decide
  prepTop := by decide

theorem facts_half : Facts halfFanoutConfig halfFanoutSeparated where
  levels_ge := by decide
  levels_le := by decide
  fanout_ge := by decide
  seed_dvd := by decide
  seed_succ := by decide
  per_one := by decide
  per_succ := by decide
  per_pos := by decide
  horizon := by decide
  rowA := by decide
  rowCarry := by decide
  rowOne := by decide
  topB := by decide
  initPrep := by decide
  topPrep := by decide
  prepTop := by decide

end RebuildBound.HierarchyCoveringProof
