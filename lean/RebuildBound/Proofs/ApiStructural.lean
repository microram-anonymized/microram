import RebuildBound.Spec.ApiStructural
import RebuildBound.Proofs.ApiExecution
import RebuildBound.Proofs.ApiAdaptive.Correctness
import RebuildBound.Proofs.HierarchyLive

/-! The old numeric bound is a private provenance witness for a finite run,
independent of storage capacity. Initialization length is the only population
needed by deterministic lookup and flag soundness. Logical capacity enters
only after correctness has been established on unconditional reference tapes. -/
namespace RebuildBound.ApiStructuralProof
open Model Model.Hierarchy Model.Online Spec HierarchyInvariantProof

/-- A finite run supplies a finite numeric provenance bound, without limiting
its identities, its historical distinct keys, or the client's other branches. -/
theorem run_premises (cfg : Config) (g : OnlineGeom) (run : OnlineBatch.BatchRun)
    (hg : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) (hi : (run.init.map Rec.key).Nodup) :
    ∃ N, (∀ s ∈ OnlineBatch.slots run, s.record.key.toNat < N) ∧
      TracePremises cfg N (OnlineBatch.traceOf g run) := by
  let keys := run.init.map Rec.key ++ (OnlineBatch.slots run).map (fun s => s.record.key)
  let U := keys.toFinset
  have hslots : ∀ s ∈ OnlineBatch.slots run, s.record.key ∈ U := by
    intro s hs
    exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨s, hs, rfl⟩))
  have hinit : ∀ r ∈ run.init, r.key ∈ U := by
    intro r hr
    exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
  have ht := RequesterTrace cfg U g run hg hE hslots hi hinit
  have hbound : ∀ k ∈ U, k.toNat < U.sup LogicalKey.toNat + 1 := by
    intro k hk
    exact Nat.lt_succ_of_le (Finset.le_sup (f := LogicalKey.toNat) hk)
  exact ⟨U.sup LogicalKey.toNat + 1, fun s hs => hbound _ (hslots s hs),
    ⟨ht.nodup, ht.load, fun i r hr => hbound _ (ht.keys i r hr),
      ht.initNodup, fun r hr => hbound _ (ht.initKeys r hr)⟩⟩

/-- Both semantic conclusions follow from one arbitrary finite provenance bound.
There is no compression, change of execution, or key-capacity comparison. -/
theorem constructed : ApiExecutionStructural_statement := by
  intro geo hgeo c g S init groups m hInit hn hLen hg hE hhor hv hS
  let run := ApiExecution.run c geo.cfg geo.shapes g S init groups
  have hi := ApiExecutionImplements c geo.cfg geo.shapes g S init groups m hg hE hv hS
  have hflag := ApiExecutionFlags c geo.cfg geo.shapes g S init groups m hg hE hv hS
  obtain ⟨N, hkeys, htrace⟩ := run_premises geo.cfg g run hg hE hn
  have F := HierarchySemanticsProof.lower hgeo.1
  have G := TopFacts.of_compatible hgeo.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hD, _⟩ := hgeo.2
  have hslotsHor : (OnlineBatch.slots run).length ≤ geo.cfg.horizon := hi.length ▸ hhor
  have hslotsS : SchedulePremises geo.cfg S (OnlineBatch.slots run).length m := hi.length ▸ hS
  have C : AdaptiveFlagSoundProof.Ctx geo N g run S m :=
    ⟨F, G, hD, hInit, hLen, hg, hE, hslotsHor, htrace, hslotsS⟩
  have hunsh := AdaptiveFlagSoundProof.flagSound_core C (fun _ _ _ => 0) hflag
  have hr : BatchRunPremises geo.cfg geo.shapes N g run :=
    ⟨⟨hg, hE⟩, hslotsHor, hkeys, htrace, hunsh⟩
  refine ⟨⟨htrace.nodup, htrace.load, htrace.initNodup⟩, hunsh, ?_⟩
  intro words dummy
  have ht : Api.Implements c geo.cfg geo.shapes g run S words dummy
      (groups.flatMap PublicApi.Group.lanes) := by
    refine ⟨hi.length, ?_⟩
    intro t q s hq hs
    obtain ⟨hk, hp, he⟩ := hi.slot t q s hq hs
    refine ⟨hk, hp, ?_⟩
    rw [AdaptiveFoundProof.batchFoundFor_of_initLength geo F G hD N g run S
      (OnlineBatch.slots run).length m hLen le_rfl hr hslotsS words (fun _ _ _ => 0)
      dummy (fun _ _ => 0) t (List.getElem?_eq_some_iff.mp hs).1]
    exact he
  refine ⟨ht, ?_⟩
  apply ApiProof.apiCorrect c geo.cfg geo.shapes g run S words dummy _ ht
  intro t s hs hp
  exact BatchCorrectnessProof.correctnessFor_run_of_initLength geo F G hD N g run S
    (OnlineBatch.slots run).length m hLen le_rfl hr hslotsS hInit words dummy t s
    (List.getElem?_eq_some_iff.mp hs).1 hs hp

end RebuildBound.ApiStructuralProof

namespace RebuildBound
open Model Model.Hierarchy Model.Online Model.PublicApi Spec HierarchyInvariantProof

theorem ApiExecutionStructural : ApiExecutionStructural_statement := ApiStructuralProof.constructed

theorem ApiExecutionLive : ApiExecutionLive_statement := by
  intro geo hgeo c g S init groups m hInit hg hE hhor hv hfit hS hcap
  dsimp only
  have G := TopFacts.of_compatible hgeo.2
  have hLen : init.length ≤ geo.init.C / 2 * geo.init.T := by
    rw [G.initC, G.topC, G.initT]
    exact hInit.2.1.trans G.capacity
  have hc := ApiExecutionStructural geo hgeo c g S init groups m
    hInit.2.2.2 hInit.1 hLen hg hE hhor hv hS
  refine ⟨hc, ?_⟩
  have hi := (hc.2.2 (fun _ _ _ => 0) (fun _ _ => 0)).1
  exact HierarchyLivePopulations geo hgeo g _ c (groups.flatMap PublicApi.Group.lanes)
    hInit hE (RequesterLoweredFits c geo.cfg geo.shapes g S init groups hE hfit)
    hc.1 hc.2.1 hi.length (hc.2.2 (fun _ _ _ => 0) (fun _ _ => 0)).2.1 hcap

theorem ApiAdaptiveStructural : ApiAdaptiveStructural_statement := by
  intro geo hgeo c g S init m width batches choose
  dsimp only
  intro hInit hn hLen hg hE hhor hS words dummy
  have hf := ApiAdaptiveFrames width g.unitEntries batches
  rw [ApiAdaptiveInteraction c geo.cfg geo.shapes g S init m _ choose hf.1 words dummy]
  exact ApiExecutionStructural geo hgeo c g S init _ m hInit hn hLen hg hE
    (by simpa only [ApiAdaptiveCorrectnessProof.requests_length] using hhor)
    (hf.2.2 m choose _).1
    (by simpa only [ApiAdaptiveCorrectnessProof.requests_length] using hS)

theorem ApiAdaptiveLive : ApiAdaptiveLive_statement := by
  intro geo hgeo c g S init m width batches choose
  dsimp only
  intro hInit hg hE hhor hS hcap words dummy
  have hf := ApiAdaptiveFrames width g.unitEntries batches
  rw [ApiAdaptiveInteraction c geo.cfg geo.shapes g S init m _ choose hf.1 words dummy]
  exact ApiExecutionLive geo hgeo c g S init _ m hInit hg hE
    (by simpa only [ApiAdaptiveCorrectnessProof.requests_length] using hhor)
    (hf.2.2 m choose _).1 (hf.2.2 m choose _).2
    (by simpa only [ApiAdaptiveCorrectnessProof.requests_length] using hS) (hcap _)

end RebuildBound
