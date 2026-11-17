import RebuildBound.Proofs.HierarchyInvariant.ContractsFor
import RebuildBound.Proofs.HierarchyInvariant.TopInd

/-!
# HierarchyInvariant: the jobs' contracts at a configuration with `Facts`
-/

namespace RebuildBound.HierarchyInvariantProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.DirectJob RebuildBound.Spec

section
variable {cfg : Config} {rows : List (SepGeom × Nat)} {tr : Trace} {N : Nat}

/-- The carry consumed at level `2 ≤ ℓ ≤ L`. -/
theorem carry_inv (F : Facts cfg rows) (hT : TracePremises cfg N tr) (words : Words) {ℓ v : Nat}
    (h2 : 2 ≤ ℓ) (hL : ℓ ≤ cfg.levels) (hv : cfg.seed ℓ < v) :
    CInv cfg N ℓ (jobWord cfg words ℓ v) (carryOf cfg (hierarchyShapes cfg rows) tr words ℓ v) := by
  exact carry_invFor (selectedGeometry cfg rows) F.lowFacts hT words h2 hL hv

theorem sepInputsAt_eq (words : Words) (ℓ o : Nat) :
    sepInputsAt cfg (hierarchyShapes cfg rows) tr words ℓ o =
      sepInputs ((hierarchyShapes cfg rows).sep ℓ (cfg.digitAt ℓ o))
        (table cfg (hierarchyShapes cfg rows) tr words ℓ (o - 1))
        (carryOf cfg (hierarchyShapes cfg rows) tr words ℓ o) := by
  exact sepInputsAt_eqFor (selectedGeometry cfg rows) words ℓ o

/-- The context of a potential separated job. -/
theorem sep_ctx (F : Facts cfg rows) (hT : TracePremises cfg N tr) (words : Words) {ℓ o : Nat}
    (hj : JobId.ordinary ℓ o ∈ cfg.potentialJobs) (h2 : 2 ≤ ℓ) (hd2 : 2 ≤ cfg.digitAt ℓ o) :
    ∃ g, (hierarchyShapes cfg rows).sep ℓ (cfg.digitAt ℓ o) = g ∧ g.d = cfg.digitAt ℓ o ∧
      g.U = cfg.carry ℓ ∧ g.Valid ∧ g.C = 64 ∧ g.bTierPages = 1 ∧ val2 g.d = g.e ∧
      LInv cfg N ℓ (o - 1) (jobWord cfg words ℓ (o - 1))
        (table cfg (hierarchyShapes cfg rows) tr words ℓ (o - 1)) ∧
      cfg.digitAt ℓ (o - 1) = cfg.digitAt ℓ o - 1 ∧ cfg.seed ℓ < o - 1 ∧
      CInv cfg N ℓ (jobWord cfg words ℓ o) (carryOf cfg (hierarchyShapes cfg rows) tr words ℓ o) := by
  obtain ⟨h1, hL, hv⟩ := pj_ordinary hj
  obtain ⟨hb2, -, -⟩ := F.fan ℓ h1 hL
  have hdvd : cfg.fanout ℓ ∣ cfg.seed ℓ := ⟨_, F.seed ℓ h1 hL⟩
  have hdb : cfg.digitAt ℓ o ≤ cfg.fanout ℓ := digit_le (by omega) o
  obtain ⟨g, hg, hgd, hgU, hgV, hC, hP, he⟩ := row_of F h2 hL hd2 hdb
  have hp := pred_gt hdvd hv hd2
  exact ⟨g, hg, hgd, hgU, hgV, hC, hP, he, (low F hT words ℓ h1 hL _ hp).1,
    digit_pred (by omega) hd2, hp, carry_inv F hT words h2 hL.le hv⟩

theorem sepAt_aAll (words : Words) (ℓ o : Nat) :
    (sepInputsAt cfg (hierarchyShapes cfg rows) tr words ℓ o).aAll =
      (table cfg (hierarchyShapes cfg rows) tr words ℓ (o - 1)).records := by
  exact sepAt_aAllFor (selectedGeometry cfg rows) words ℓ o

theorem sepAt_bAll (words : Words) (ℓ o : Nat)
    (hP : ((hierarchyShapes cfg rows).sep ℓ (cfg.digitAt ℓ o)).bTierPages = 1) :
    (sepInputsAt cfg (hierarchyShapes cfg rows) tr words ℓ o).bAll =
      (carryOf cfg (hierarchyShapes cfg rows) tr words ℓ o).records := by
  apply sepAt_bAllFor (selectedGeometry cfg rows) words ℓ o
  change 0 < ((hierarchyShapes cfg rows).sep ℓ (cfg.digitAt ℓ o)).bTierPages
  omega

theorem finish_below (F : Facts cfg rows) (hT : TracePremises cfg N tr) (hN : N ≤ 2 ^ 27)
    (words : Words) {o : Nat} (ho : cfg.seed cfg.levels < o) :
    ∀ x ∈ (finishInputsAt cfg (hierarchyShapes cfg rows) tr words o).aAll ++
      (finishInputsAt cfg (hierarchyShapes cfg rows) tr words o).bAll, x.key.toNat < N := by
  exact finish_belowFor (selectedGeometry cfg rows) F.lowFacts F.topFacts hT hN words ho

theorem contracts (F : Facts cfg rows) (hN : N ≤ 2 ^ 27) (hT : TracePremises cfg N tr)
    (hU : UnshPromise cfg (hierarchyShapes cfg rows) tr) (words : Words) :
    JobContracts cfg (hierarchyShapes cfg rows) tr N words := by
  exact contractsFor (selectedGeometry cfg rows) F.lowFacts F.topFacts hN hT hU words

end

end RebuildBound.HierarchyInvariantProof
