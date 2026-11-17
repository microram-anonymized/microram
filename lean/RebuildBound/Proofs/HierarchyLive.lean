import RebuildBound.Proofs.HierarchyLive.Prefix
import RebuildBound.Proofs.HierarchyStructural

/-! Logical capacity bounds the four actual top-job populations after their
chronological cuts have been identified. API prefix correspondence and the
local flag rule remain explicit intermediate premises, never load promises. -/
namespace RebuildBound.HierarchyLiveProof
open Model Model.Hierarchy Model.Online Spec HierarchyInvariantProof OnlineCorrectnessProof

/-- API initialization is live-only; every later top publication is live-only
by the unconditional structural theorem, including reference overflow. -/
theorem top_live (geo : HierarchyGeometry) (hg : geo.Structural) (tr : Trace)
    (hT : TraceStructural geo.cfg tr) (hLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hU : UnshPromise geo.cfg geo.shapes tr)
    (hInit : ∀ r ∈ tr.init, r.tomb = false) (words : Words) (v : Nat)
    (hvh : v ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels) :
    ∀ r ∈ (table geo.cfg geo.shapes tr words geo.cfg.levels v).records, r.tomb = false := by
  by_cases hv : geo.cfg.seed geo.cfg.levels < v
  · exact (HierarchyStructuralTop geo hg tr hT hLen hU words v hvh).2.2.2.2.2 hv
  · cases hi : geo.cfg.initialized with
    | false =>
      rw [top_base_emptyFor geo hi words (by omega)]
      simp [Output.records, Bucket.recs, Bucket.empty]
    | true =>
      rw [top_base_eqFor geo hi words (by omega)]
      apply tpReference_P
      intro r hr
      rw [TG1Proof.aAll_initMain geo.init tr.init hLen] at hr
      exact hInit r hr

/-- A published snapshot's record count is the independent logical support at
its consumed prefix. Uniqueness and absence of tombstones are proved first. -/
theorem top_count (geo : HierarchyGeometry) (hg : geo.Structural)
    (g : OnlineGeom) (run : OnlineBatch.BatchRun) (c : Api.Codec)
    (requests : List Api.Request)
    (hInit : ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized run.init)
    (hE : 0 < g.unitEntries)
    (hfit : RequesterCuts.WidthsFit g.unitEntries 0 (OnlineBatch.widths run))
    (hT : TraceStructural geo.cfg (OnlineBatch.traceOf g run))
    (hU : UnshPromise geo.cfg geo.shapes (OnlineBatch.traceOf g run))
    (hlen : requests.length = (OnlineBatch.slots run).length)
    (hcorr : ApiPrefixCorrespondence c run requests)
    (hcap : ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c run.init)
      (run.init.map Rec.key) requests)
    (hLen : run.init.length ≤ geo.init.C / 2 * geo.init.T) (words : Words) (v : Nat)
    (hvh : v ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels) :
    (table geo.cfg geo.shapes (OnlineBatch.traceOf g run) words geo.cfg.levels v).records.length ≤
      geo.keyCapacity := by
  obtain ⟨_, _, hn, _, hm, _⟩ :=
    HierarchyStructuralTop geo hg _ hT hLen hU words v hvh
  have hl := top_live geo hg _ hT hLen hU hInit.2.2.1 words v hvh
  have he := (stateOf_congr c hm).trans
    (consumed_map geo.cfg g run c requests hInit.2.2.2 hE hfit hlen hcorr v)
  rw [ApiSnapshotPopulation c _ _ requests _ _ hcap.1 hn hl he]
  apply hcap.2
  rw [hlen]
  exact (RequesterTraceSaturatedCuts g run hE hfit _).1

end RebuildBound.HierarchyLiveProof

namespace RebuildBound
open Model Model.Hierarchy Model.Online Spec HierarchyLiveProof HierarchyInvariantProof
open OnlineCorrectnessProof

theorem HierarchyLivePopulations : HierarchyLivePopulations_statement := by
  intro geo hg g run c requests hInit hE hfit hT hU hlen hcorr hcap
  have G := TopFacts.of_compatible hg.2
  have hLen : run.init.length ≤ geo.init.C / 2 * geo.init.T := by
    rw [G.initC, G.topC, G.initT]
    exact hInit.2.1.trans G.capacity
  refine ⟨hInit.2.1, ?_⟩
  intro words v hv hvh
  have hp := top_count geo hg g run c requests hInit hE hfit hT hU hlen hcorr hcap
    hLen words (v - 1) (by omega)
  have hn := top_count geo hg g run c requests hInit hE hfit hT hU hlen hcorr hcap
    hLen words v hvh
  obtain ⟨_, hpub, hprep⟩ := HierarchyStructuralStep geo hg _ hT hLen hU words v hv hvh
  refine ⟨hp, ?_, ?_⟩
  · rw [hprep.length_eq, prepInputsAt_eqFor, survivors_eq]
    exact (List.length_filter_le _ _).trans hp
  · rw [← hpub.length_eq]
    exact hn

end RebuildBound
