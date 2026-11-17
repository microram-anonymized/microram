import RebuildBound.Proofs.G3fin
import RebuildBound.Proofs.TPJobfin.Generic
import RebuildBound.Proofs.ConfigurationFamilyProbability
import RebuildBound.Proofs.AdaptiveSepA
import RebuildBound.Proofs.AdaptiveSepU
import RebuildBound.Proofs.AdaptiveTop.Finish
import RebuildBound.Proofs.AdaptiveTop.Prep
import RebuildBound.Proofs.AdaptiveTop.Init
import RebuildBound.Proofs.AdaptiveCompose.Sep
import RebuildBound.Proofs.AdaptiveCell
import RebuildBound.Proofs.AdaptiveTracePrefix

/-! Family applicability of the common causal separated and top adapters.
These supply symbolic analytic bounds, not the pending family exposure sum. -/
open MeasureTheory
open scoped ENNReal NNReal
namespace RebuildBound.ConfigurationFamilyProbabilityProof
open Model Model.Hierarchy Spec Spec.ConfigurationFamily

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem sepFor (initialized : Bool) (m : Member) (hm : m ∈ members) (h : Nat) :
    let geo := (m.geometry initialized).chunk h
    CausalBound geo fun μ tr words => ∀ ℓ o g,
      JobId.ordinary ℓ o ∈ geo.cfg.potentialJobs → 2 ≤ ℓ →
      geo.cfg.sepRow geo.rows ℓ (geo.cfg.digitAt ℓ o) = some g →
      μ {ω | JobFailsFirst geo.cfg geo.shapes (tr ω) (words ω) (.ordinary ℓ o)} ≤
        selSepBound g := by
  let geo := (m.geometry initialized).chunk h
  have ha := arithmetic initialized m hm
  have hs := HierarchySemanticsProof.lower (ConfigurationFamilyStructural initialized m hm).1
  have hI := invariant initialized m hm h
  have hL := locality initialized m hm h
  have hg := HierarchySepLawChunksProof.good_chunk ha.2.1 (chunkFacts initialized m hm) h
  have hr := HierarchySepLawChunksProof.rowsMatch_chunk h ha.2.2.1
  have hv : ∀ g ∈ geo.rows.map Prod.fst,
      g.Valid ∧ g.I < g.K ∧ g.C = 64 ∧ g.stashPages * g.C < 256 := by
    intro g hgm
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hgm
    exact (ha.2.2.2.1 q hq).2.2.2
  have hA := AdaptiveSepAProof.sepAFor geo hg hr (rowOK initialized m hm)
    hv hs.load hI hL TracePrefix CausalCell
  have hU : AdaptiveSepUProof.GeoFacts geo :=
    { good := hg, rows := hr, rowOK := rowOK initialized m hm
      rowV := by
        intro q hq
        have hqv := hv q.1 (List.mem_map.2 ⟨q, hq, rfl⟩)
        exact ⟨hqv.1, hqv.2.2.1, lt_of_le_of_lt (min_le_left _ _) hqv.2.2.2⟩
      load := hs.load, inv := hI, loc := hL }
  dsimp only
  intro N n w T hcs Ω _ μ _ tape dtape words hOT ℓ o g hj hℓ hrow
  exact AdaptiveComposeProof.sep_boundFor geo hI (fun g hgm => (hv g hgm).1)
    N hcs.1 μ (fun ω => T (tape ω, dtape ω)) words
    (fun ω => (hcs.2.2 (tape ω, dtape ω)).1)
    (fun ω => (hcs.2.2 (tape ω, dtape ω)).2) ℓ o g hj hℓ hrow _ _
    (fun hd => hA N n w T hcs μ tape dtape words hOT ℓ o g hj hℓ hd hrow)
    (fun hd => AdaptiveSepUProof.sepU_for geo hU TracePrefix CausalCell
      N n w T hcs μ tape dtape words hOT ℓ o g hj hℓ hd hrow)

/-- The fixed cutoffs are sufficient at every top shape and either start. -/
theorem topCutoffs (initialized : Bool) : ∀ m ∈ members,
    let geo := m.geometry initialized
    (geo.top.C < 576 ∧ min geo.top.SMerge geo.top.STier < 576) ∧
    (geo.prep.I + 1 < geo.prep.k ∧ geo.prep.stashPages * geo.prep.C < 576 ∧
      geo.prep.drainPages * geo.prep.C < 576) ∧
    (geo.init.I + 1 < geo.init.k ∧ geo.init.stashPages * geo.init.C < 576 ∧
      geo.init.drainPages * geo.init.C < 576) := by
  cases initialized <;> decide +kernel

theorem topFor (initialized : Bool) (m : Member) (hm : m ∈ members) (h : Nat) :
    let geo := (m.geometry initialized).chunk h
    CausalBound geo fun μ tr words =>
      (∀ o, JobId.topFinish o ∈ geo.cfg.potentialJobs →
        μ {ω | JobFailsFirst geo.cfg geo.shapes (tr ω) (words ω) (.topFinish o)} ≤
          ENNReal.ofReal (topFinishBound geo.top.C geo.top.SR geo.top.rho geo.top.I geo.top.T
            (min geo.top.SMerge geo.top.STier) 576 576 32)) ∧
      (∀ o, JobId.topPrepare o ∈ geo.cfg.potentialJobs →
        μ {ω | JobFailsFirst geo.cfg geo.shapes (tr ω) (words ω) (.topPrepare o)} ≤
          tpBound geo.prep 32 1 576 576) ∧
      (JobId.initialization ∈ geo.cfg.potentialJobs →
        μ {ω | JobFailsFirst geo.cfg geo.shapes (tr ω) (words ω) .initialization} ≤
          tpBound geo.init 32 1 576 576) := by
  let geo := (m.geometry initialized).chunk h
  have ha := arithmetic initialized m hm
  have hs := HierarchySemanticsProof.lower (ConfigurationFamilyStructural initialized m hm).1
  have ht := HierarchyInvariantProof.TopFacts.of_compatible
    (ConfigurationFamilyStructural initialized m hm).2
  have hc := chunkFacts initialized m hm
  have hcut := topCutoffs initialized m hm
  have hI := invariant initialized m hm h
  have hL := locality initialized m hm h
  have hstep := stepFacts initialized m hm h
  have hcarry := HierarchyTopLawChunksProof.carryFacts_chunk hc h
  dsimp only
  intro N n w T hcs Ω _ μ _ tape dtape words hOT
  refine ⟨fun o ho => ?_, fun o ho => ?_, fun hj => ?_⟩
  · exact AdaptiveTopProof.finish_bound geo hstep hcarry hL hI hs.load
      ha.2.2.2.2.1 hs.levels2 (HierarchyTopLawChunksProof.win_chunk hc h) TracePrefix CausalCell _
      (fun L unsh hLaw => G3 geo.top L unsh 32 576 576 hLaw ht.topValid
        hcut.1.1 hcut.1.2) hcs μ tape dtape words hOT o ho
  · exact AdaptiveTopProof.prep_bound geo hstep hcarry hL hI hs.load
      ha.2.2.2.2.2.1 TracePrefix CausalCell _
      (fun L unsh hLaw => TPJob geo.prep L unsh 32 1 engineRule 576 576 ht.prepValid hLaw D1
        (fun _ => hcut.2.1.1) hcut.2.1.2.1 hcut.2.1.2.2)
      hcs μ tape dtape words hOT o ho
  · apply AdaptiveTopProof.init_bound geo (ConfigurationFamilySourceLaws initialized m hm h).2.2.2
      TracePrefix _ ?_ hcs μ tape dtape words hOT hj
    intro L input hLaw
    have hb := IJob geo.init L input engineRule 576 576 ht.initValid hLaw D1
      (fun _ => hcut.2.2.1) hcut.2.2.2.1 hcut.2.2.2.2
    have hC : geo.init.C = 64 := ht.initC
    simpa only [hC, Nat.reduceDiv, Nat.cast_ofNat] using hb

end RebuildBound.ConfigurationFamilyProbabilityProof
