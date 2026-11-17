import RebuildBound.Proofs.HierarchyProbability
import RebuildBound.Proofs.AdaptiveCompose.Rows
import RebuildBound.Proofs.Compose31
import RebuildBound.Proofs.G4a
import RebuildBound.Proofs.HierarchyChunkAssembly
import RebuildBound.Proofs.HierarchyChunkPartition
import RebuildBound.Proofs.HierarchyCoveringFrom
import RebuildBound.Proofs.HierarchyLawsChunks31
import RebuildBound.Proofs.HierarchyHorizonTransfer
import RebuildBound.Proofs.Inventory31

/-!
# AdaptiveCompose: the windows bound from the per-class bounds

Per chunk, G4a with the first-failure events of the chunk's jobs (shifted into
the horizon `h`), the class budgets of `Compose31` and the covering; then a
union over the `h` chunks.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.AdaptiveComposeProof
open RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open HierarchyChunkAssemblyProof HierarchyChunkArith

/-- The class budgets at `geometry31`. -/
noncomputable def classBound31 : JobClass → ℝ≥0∞
  | .ordinary ℓ d => if ℓ = 1 then selectedDirectBound selectedDirectABudget d
      else if d = 1 then 0 else ((config31.sepRow separated31 ℓ d).map selSepBound).getD 1
  | .topFinish => ENNReal.ofReal (topFinishBound top31.C top31.SR top31.rho top31.I top31.T
      (min top31.SMerge top31.STier) 576 576 32)
  | .topPrepare => tpBound prep31 32 1 576 576
  | .initialization => tpBound init31 32 1 576 576

theorem classBound31_eq : classBound31 = Compose31.classBound config31 separated31
    (selectedDirectBound selectedDirectABudget) (Compose31.finishBound top31)
    (tpBound prep31 32 1 576 576) (tpBound init31 32 1 576 576) := by
  funext c; cases c <;> rfl

theorem budget31 : config31.exposureSum classBound31 ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 64) := by
  rw [classBound31_eq]; exact Compose31.budget31_le

/-- The existing 31 assembly specializes the shared geometry-parametric proof. -/
theorem compose (hCov : AdaptiveCovering31_statement) (b : JobClass → ℝ≥0∞) (h : Nat)
    (hh : 1 ≤ h) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tr : Ω → Trace) (words : Ω → Words)
    (hb : ∀ j ∈ (geometry31.chunk h).cfg.potentialJobs,
      μ {ω | JobFailsFirst (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω)
        (words ω) j} ≤ b (geometry31.cfg.classOf j)) :
    μ {ω | Fails (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω) (words ω)} ≤
      (h : ℝ≥0∞) * geometry31.cfg.exposureSum b :=
  HierarchyProbabilityProof.composeFor geometry31 HierarchyLawsChunks31Proof.chunkFacts31
    Inventory31.1 hCov b h hh μ tr words hb

/-- The windows step: the covering and the per-class causal bounds. -/
theorem windowsStep : CausalWindowsStep_statement := by
  intro hCov hSep hOne hTop h hh N n m T hT Ω _ μ _ tape dtape words hprem
  have hS := hSep h hh N n m T hT μ tape dtape words hprem
  have hO := hOne h hh N n m T hT μ tape dtape words hprem
  have hP := hTop h hh N n m T hT μ tape dtape words hprem
  obtain ⟨hF, hPr, hI⟩ := hP
  refine (compose hCov classBound31 h hh μ _ words ?_).trans ?_
  swap
  · exact mul_le_mul' le_rfl budget31
  intro j hj
  cases j with
  | ordinary ℓ o =>
    by_cases hℓ : ℓ = 1
    · subst hℓ
      show _ ≤ classBound31 (config31.classOf (.ordinary 1 o))
      simp only [classBound31, Config.classOf, if_true]
      exact hO o hj
    · have hl1 := (HierarchyCoveringProof.mem_ordinary.1 hj).1
      by_cases hd : Config.digitOf (config31.fanout ℓ) o = 1
      · have : {ω | JobFailsFirst (geometry31.chunk h).cfg (geometry31.chunk h).shapes
            (T (tape ω, dtape ω)) (words ω) (.ordinary ℓ o)} = ∅ := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨-, -, hf, -⟩
          simp [jobFails, hℓ] at hf
          exact absurd hd hf.1
        rw [this, measure_empty]; exact zero_le
      · cases hg : config31.sepRow separated31 ℓ (Config.digitOf (config31.fanout ℓ) o) with
        | none =>
          show _ ≤ classBound31 (config31.classOf (.ordinary ℓ o))
          simp only [classBound31, Config.classOf, hℓ, hd, if_false, hg, Option.map_none,
            Option.getD_none]
          exact prob_le_one
        | some g =>
          show _ ≤ classBound31 (config31.classOf (.ordinary ℓ o))
          simp only [classBound31, Config.classOf, hℓ, hd, if_false, hg, Option.map_some,
            Option.getD_some]
          refine hS ℓ o g hj (by omega) ?_
          rw [sepRow_chunk]; exact hg
  | topFinish o => exact hF o hj
  | topPrepare o => exact hPr o hj
  | initialization => exact hI hj

end RebuildBound.AdaptiveComposeProof
