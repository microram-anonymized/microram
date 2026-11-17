import RebuildBound.Spec.ConfigurationFamilyBound
import RebuildBound.Proofs.ConfigurationFamilyDirect
import RebuildBound.Proofs.ConfigurationFamilyProbability.Causal
import RebuildBound.Proofs.HierarchyProbability

/-! One class-exposure composition for all family geometries and both starts.
No numerical certificate enters the local probability applicability proof. -/
open MeasureTheory
open scoped ENNReal
namespace RebuildBound
open Spec Model Model.Hierarchy Spec.ConfigurationFamily HierarchyChunkArith

/-- Fixed and adaptive consumers share these analytic class budgets. -/
theorem ConfigurationFamilyAnalytic : ConfigurationFamilyAnalytic_statement := by
  intro initialized m hm h hh N n w T hT Ω _ μ _ tape dtape words hOT
  let geo := m.geometry initialized
  have hS := ConfigurationFamilyProbabilityProof.sepFor initialized m hm h
    N n w T hT μ tape dtape words hOT
  have hO := ConfigurationFamilyDirect initialized m hm h N n w T hT μ tape dtape words hOT
  obtain ⟨hF, hP, hI⟩ := ConfigurationFamilyProbabilityProof.topFor initialized m hm h
    N n w T hT μ tape dtape words hOT
  apply HierarchyProbabilityProof.composeFor geo
    (ConfigurationFamilyProbabilityProof.chunkFacts initialized m hm)
    (ConfigurationFamilyProbabilityProof.arithmetic initialized m hm).1
    (ConfigurationFamilyCovering initialized m hm) (classBudget m initialized) h hh μ
    (fun ω => T (tape ω, dtape ω)) words
  intro j hj
  cases j with
  | ordinary ℓ o =>
    by_cases hℓ : ℓ = 1
    · subst ℓ
      change _ ≤ directBound m (((m.geometry initialized).chunk h).cfg.digitAt 1 o)
      exact hO o hj
    · have hl1 := (HierarchyCoveringProof.mem_ordinary.1 hj).1
      by_cases hd : Config.digitOf (geo.cfg.fanout ℓ) o = 1
      · have hempty : {ω | JobFailsFirst (geo.chunk h).cfg (geo.chunk h).shapes
            (T (tape ω, dtape ω)) (words ω) (.ordinary ℓ o)} = ∅ := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨_, _, hf, _⟩
          simp [jobFails, hℓ] at hf
          exact absurd hd hf.1
        rw [hempty, measure_empty]
        exact zero_le
      · cases hg : geo.cfg.sepRow geo.rows ℓ (Config.digitOf (geo.cfg.fanout ℓ) o) with
        | none =>
          change _ ≤ classBudget m initialized (geo.cfg.classOf (.ordinary ℓ o))
          simp only [classBudget, Config.classOf, hℓ, hd, ite_false]
          change _ ≤ ((geo.cfg.sepRow geo.rows ℓ (Config.digitOf (geo.cfg.fanout ℓ) o)).map
            selSepBound).getD 1
          rw [hg]
          exact prob_le_one
        | some g =>
          change _ ≤ classBudget m initialized (geo.cfg.classOf (.ordinary ℓ o))
          simp only [classBudget, Config.classOf, hℓ, hd, ite_false]
          change _ ≤ ((geo.cfg.sepRow geo.rows ℓ (Config.digitOf (geo.cfg.fanout ℓ) o)).map
            selSepBound).getD 1
          rw [hg]
          apply hS ℓ o g hj (by omega)
          change (chunkConfig geo.cfg h).sepRow geo.rows ℓ (Config.digitOf (geo.cfg.fanout ℓ) o) = some g
          dsimp only [chunkConfig]
          rw [(HierarchyHorizonFree geo.cfg (h * 2 ^ 32) geo.rows).2.1]
          exact hg
  | topFinish o => exact hF o hj
  | topPrepare o => exact hP o hj
  | initialization => exact hI hj

end RebuildBound
