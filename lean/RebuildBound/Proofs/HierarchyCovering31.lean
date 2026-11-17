import RebuildBound.Proofs.HierarchyCovering
import RebuildBound.Proofs.TierFit

/-! Instantiate the shared covering proof using finite geometry checks.
Bounds come from the configuration; no execution tables are evaluated. -/

namespace RebuildBound.HierarchyCovering31Proof
open Model Spec HierarchyCoveringProof

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem facts : FactsFor config31 separated31 top31 prep31 init31 where
  levels_ge := by decide +kernel
  levels_le := by decide +kernel
  fanout_ge := by decide +kernel
  seed_dvd := by decide +kernel
  seed_succ := by decide +kernel
  per_one := by decide +kernel
  per_succ := by decide +kernel
  per_pos := by decide +kernel
  horizon := by decide +kernel
  rowA := by decide +kernel
  rowCarry := by decide +kernel
  rowOne := by decide +kernel
  topB := by decide +kernel
  initPrep := by decide +kernel
  topPrep := by decide +kernel
  prepTop := by decide +kernel

end RebuildBound.HierarchyCovering31Proof

/-- The capacity extension's first-failure covering, with no local-law,
structural-contract or tier-fit premises left to the caller. -/
theorem RebuildBound.HierarchyCovering31 : RebuildBound.Spec.HierarchyCovering31_statement :=
  RebuildBound.HierarchyCoveringProof.coveringFor RebuildBound.Spec.geometry31 rfl
    RebuildBound.HierarchyCovering31Proof.facts
    RebuildBound.SepTierFit RebuildBound.TopTierFit RebuildBound.TPTierFit
