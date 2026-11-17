import RebuildBound.Spec.HierarchyChunk
import RebuildBound.Proofs.HierarchyLocality.Table

/-! # HierarchyHorizonFree: the model does not read the horizon -/

namespace RebuildBound
open Model Model.DirectJob Model.Hierarchy Spec

namespace HierarchyHorizonFreeProof

theorem familyOfAux_horizon (cfg : Config) (H : Nat) :
    familyOfAux { cfg with horizon := H } = familyOfAux cfg := by
  funext n; induction n with
  | zero => rfl
  | succ n ih => funext ℓ v; simp only [familyOfAux, ih]; rfl

theorem jobWord_horizon (cfg : Config) (H : Nat) : jobWord { cfg with horizon := H } = jobWord cfg := by
  unfold jobWord familyOf; rw [familyOfAux_horizon]; rfl

theorem base_horizon (cfg : Config) (H : Nat) : base { cfg with horizon := H } = base cfg := by
  unfold base initOutput; rw [jobWord_horizon]; rfl

theorem step_horizon (cfg : Config) (H : Nat) : step { cfg with horizon := H } = step cfg := by
  unfold step prepOutput; rw [jobWord_horizon]; rfl

theorem table_horizon (cfg : Config) (H : Nat) (sh : Shapes) (tr : Trace) (words : Words) :
    ∀ ℓ v, table { cfg with horizon := H } sh tr words ℓ v = table cfg sh tr words ℓ v := by
  have hl : ({ cfg with horizon := H } : Config).levels = cfg.levels := rfl
  have hs : ∀ ℓ, ({ cfg with horizon := H } : Config).seed ℓ = cfg.seed ℓ := fun _ => rfl
  have hf : ∀ ℓ, ({ cfg with horizon := H } : Config).fanout ℓ = cfg.fanout ℓ := fun _ => rfl
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ihℓ =>
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ihv =>
      rw [HierarchyLocalityProof.table_eq { cfg with horizon := H } sh tr words ℓ v, HierarchyLocalityProof.table_eq cfg sh tr words ℓ v]
      simp only [hl, hs, hf, base_horizon, step_horizon]
      split_ifs with h1
      · rfl
      all_goals (rw [ihv (v - 1) (by omega)]; try rw [ihℓ (ℓ - 1) (by omega)])

end HierarchyHorizonFreeProof

open HierarchyHorizonFreeProof in
theorem HierarchyHorizonFree : Spec.HierarchyHorizonFree_statement := by
  intro cfg H rows
  have hrow : ({ cfg with horizon := H } : Config).sepRow rows = cfg.sepRow rows := by
    have : ({ cfg with horizon := H } : Config).separatedClasses = cfg.separatedClasses := by
      unfold Config.separatedClasses Config.exposures
      simp only [List.filterMap_append, List.filterMap_flatMap, List.filterMap_map]
      rfl
    unfold Config.sepRow; rw [this]
  refine ⟨?_, hrow, fun sh tr words j => ?_⟩
  · unfold hierarchyShapes hierarchyShapesWith; rw [hrow]
  · have ht := table_horizon cfg H sh tr words
    cases j <;> simp only [jobFails, jobTiersFit, levelOneResult, levelOneInputs, sepResult,
      sepInputsAt, carryOf, prepResult, prepInputsAt, finishResult, finishInputsAt, initResult,
      prepOutput, ht, jobWord_horizon] <;>
      first | exact ⟨rfl, Iff.rfl⟩ | exact ⟨rfl, trivial⟩
