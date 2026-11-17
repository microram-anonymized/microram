import RebuildBound.Proofs.ConfigurationFamilyDirect.A
import RebuildBound.Proofs.AdaptiveLevelOneA.Geometry
import RebuildBound.Proofs.AdaptiveLevelOneBU.Generic
import RebuildBound.Proofs.AdaptiveCompose.Direct
import RebuildBound.Proofs.AdaptiveCell
import RebuildBound.Proofs.AdaptiveTracePrefix

/-! One causal direct-job proof for every finite family member and both
starts. A/B/union certificates retain their separate source-law arguments. -/

open MeasureTheory
open scoped ENNReal NNReal
namespace RebuildBound
open Model Model.DirectJob Model.Hierarchy Spec Spec.ConfigurationFamily
open ConfigurationFamilyDirectProof

set_option maxHeartbeats 800000

theorem ConfigurationFamilyDirect : ConfigurationFamilyDirect_statement := by
  intro initialized m hm h
  let geo := (m.geometry initialized).chunk h
  change CausalBound geo _
  have F := causalGeometry initialized m hm h
  have hc := ConfigurationFamilyProbabilityProof.coveringFacts initialized m hm
  have hb : 0 < geo.cfg.fanout 1 := by
    have hb := hc.fanout_ge 1 (by have := hc.levels_ge; omega) le_rfl
    exact lt_of_lt_of_le (by decide : 0 < 2) hb
  have hseed : geo.cfg.seed 1 % geo.cfg.fanout 1 = 0 := hc.seed_dvd
  have hG : DirectCycleGeometry geo.direct (geo.cfg.fanout 1) := cycleGeometry m hm
  have hA := AdaptiveLevelOneAProof.levelOneAFor geo F hb hseed m.directSep
    (fun d hd hdn => by
      have hs := (facts m hm d (by omega) hdn).2.2.2.2.2.2 hd
      exact ⟨hs.2.2.1, hs.2.2.2.1⟩)
    (directABound m) (fun d hd hdn data hv => ConfigurationFamilyDirectA m hm d hd hdn data hv)
    CausalCell
  intro N n w T hcs Ω _ μ _ tape dtape words hOT o ho
  let d := geo.cfg.digitAt 1 o
  have hdpos : 1 ≤ d := by unfold d Config.digitAt Config.digitOf; omega
  have hdmax : d ≤ geo.cfg.fanout 1 := HierarchyCoveringProof.digit_le hb
  obtain ⟨hg, hgd, hK, hU, hBcut, hUcut, hrest⟩ := facts m hm d hdpos hdmax
  change μ {ω | JobFailsFirst geo.cfg geo.shapes (T (tape ω, dtape ω)) (words ω)
    (.ordinary 1 o)} ≤ directBound m d
  unfold directBound
  by_cases hd1 : d = 1
  · rw [if_pos hd1, hd1]
    have hh := AdaptiveLevelOneBUProof.term_digitOneFor geo F TracePrefix CausalCell hcs
      μ tape dtape words hOT o ho hd1 256
    subst d
    exact hh (hd1 ▸ hg) (hd1 ▸ hgd) (hd1 ▸ hK) (hd1 ▸ hU) (hd1 ▸ hBcut)
  · rw [if_neg hd1]
    have hd : 2 ≤ d := by omega
    obtain ⟨hprior, hs, hsd, hsU, hk, _, _, _, _, hHomes, hsK, hse, hsr, _⟩ := hrest hd
    apply AdaptiveComposeProof.levelOne_boundFor geo F.levels hb hseed hG μ
      (fun ω => T (tape ω, dtape ω)) words o
      (fun ω => (hcs.2.2 (tape ω, dtape ω)).1.nodup) ho hd
      (directBBound m d) (directABound m d) (directUBound m d)
    · exact AdaptiveLevelOneBUProof.term_BFor geo F TracePrefix CausalCell hcs
        μ tape dtape words hOT o ho 256 hK hU hBcut
    · exact hA N n w T hcs μ tape dtape words hOT o ho hd
    · apply AdaptiveLevelOneBUProof.term_UFor geo F hb hseed TracePrefix CausalCell hcs
        μ tape dtape words hOT o ho hd (m.directSep d) 256 hprior hs hk hsd hsU hHomes
        _ hUcut
      intro word
      change (m.direct d).home word = (m.directSep d).homeOf word
      simp [Geometry.home, digitHome, SepGeom.homeOf, SepGeom.cls, SepGeom.k, hsK, hse, hsr]

end RebuildBound
