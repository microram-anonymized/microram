import RebuildBound.Spec.ApiContinuation
import RebuildBound.Proofs.ApiStructural
import RebuildBound.Proofs.ApiCapacity

namespace RebuildBound.ApiContinuationProof
open Spec Model Model.Hierarchy Model.Online Model.PublicApi Model.ApiContinuation
open BatchFreshProof

@[simp] theorem idle_lanes (extra : Nat) :
    (idleGroups extra).flatMap Group.lanes = List.replicate extra ⟨[], .read⟩ := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    simpa [idleGroups, List.replicate_succ, Group.lanes] using
      congrArg (List.cons (⟨[], .read⟩ : Api.Request)) ih

@[simp] theorem extend_lanes (groups : List (PublicApi.Group Api.Request)) (extra : Nat) :
    (extend groups extra).flatMap Group.lanes =
      ApiCapacity.idleExtend (groups.flatMap Group.lanes) extra := by
  simp [extend, ApiCapacity.idleExtend]

theorem idle_valid (extra : Nat) : ∀ group ∈ idleGroups extra, ApiExecution.Valid group := by
  intro group hg
  have he : group = .chunk [⟨[], .read⟩] := List.eq_of_mem_replicate hg
  subst group
  simp [ApiExecution.Valid, Api.Request.probes]

theorem idle_fit (entries extra position : Nat) : GroupsFit entries position (idleGroups extra) := by
  induction extra generalizing position with
  | zero => trivial
  | succ extra ih =>
    have hp : 0 < max 1 entries := by omega
    have hm := Nat.mod_lt position hp
    change 0 < 1 ∧ 1 ≤ unitRemaining entries position ∧ _
    exact ⟨by omega, by unfold unitRemaining; omega, ih _⟩

theorem fit_append {α : Type} (entries position : Nat) (first rest : List (PublicApi.Group α))
    (hf : GroupsFit entries position first)
    (hr : GroupsFit entries (position + (first.flatMap Group.lanes).length) rest) :
    GroupsFit entries position (first ++ rest) := by
  induction first generalizing position with
  | nil => simpa using hr
  | cons group first ih =>
    exact ⟨hf.1, hf.2.1, ih _ hf.2.2 (by
      simpa only [List.flatMap_cons, List.length_append, Nat.add_assoc] using hr)⟩

theorem extend_valid (groups : List (PublicApi.Group Api.Request)) (extra : Nat)
    (hv : ∀ group ∈ groups, ApiExecution.Valid group) :
    ∀ group ∈ extend groups extra, ApiExecution.Valid group := by
  intro group hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hv group hg
  · exact idle_valid extra group hg

theorem extend_fit (entries : Nat) (groups : List (PublicApi.Group Api.Request)) (extra : Nat)
    (hf : GroupsFit entries 0 groups) : GroupsFit entries 0 (extend groups extra) :=
  fit_append entries 0 groups (idleGroups extra) hf (idle_fit _ _ _)

@[simp] theorem complete_length (entries units : Nat) (groups : List (PublicApi.Group Api.Request))
    (hn : (groups.flatMap Group.lanes).length ≤ units * entries) :
    ((complete entries units groups).flatMap Group.lanes).length = units * entries := by
  simp only [complete, extend_lanes, ApiCapacity.idleExtend, List.length_append,
    List.length_replicate]
  omega

@[simp] theorem run_length (c : Api.Codec) cfg sh g S init groups :
    (OnlineBatch.slots (ApiExecution.run c cfg sh g S init groups)).length =
      (groups.flatMap Group.lanes).length := by
  rw [slots_eq, length_slotsL]
  change (List.map (fun op => op.lanes.length)
    (ApiExecution.operations c cfg sh g S init [] groups)).sum = _
  rw [ApiExecutionProof.operations_widths]
  simp [List.length_flatMap]

theorem append_slots (run : OnlineBatch.BatchRun) (rest : List OnlineBatch.Op) :
    OnlineBatch.slots ⟨run.ops ++ rest, run.init, run.unsh⟩ =
      OnlineBatch.slots run ++ slotsL rest run.ops.length := by
  simp only [slots_eq, slotsL_append, Nat.zero_add]

theorem extension_ops (c : Api.Codec) cfg sh g S init groups extra :
    ∃ rest, (ApiExecution.run c cfg sh g S init (extend groups extra)).ops =
      (ApiExecution.run c cfg sh g S init groups).ops ++ rest := by
  exact ⟨_, ApiAdaptiveProof.operations_append c cfg sh g S init [] groups (idleGroups extra)⟩

theorem append_observations (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (rest : List OnlineBatch.Op) (S : Schedule) (n m : Nat)
    (hg : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1) (hE : 0 < g.unitEntries)
    (hS : SchedulePremises cfg S n m) (words : Words) (dummy : Nat → Nat → Nat)
    (t : Nat) (ht : t < (OnlineBatch.slots run).length) (htn : t < n) :
    let extended : OnlineBatch.BatchRun := ⟨run.ops ++ rest, run.init, run.unsh⟩
    (Probe.batch cfg sh g run S words dummy t).found =
      (Probe.batch cfg sh g extended S words dummy t).found ∧
    ∀ i, OnlineBatch.touched cfg sh g run S words dummy t i =
      OnlineBatch.touched cfg sh g extended S words dummy t i := by
  let extended : OnlineBatch.BatchRun := ⟨run.ops ++ rest, run.init, run.unsh⟩
  obtain ⟨s, hs⟩ : ∃ s, (OnlineBatch.slots run)[t]? = some s :=
    ⟨_, List.getElem?_eq_getElem ht⟩
  have hs' : (OnlineBatch.slots extended)[t]? = some s := by
    rw [append_slots, List.getElem?_append_left ht, hs]
  obtain ⟨op, ho, _, _⟩ := slot_inv run hs
  have hop := (List.getElem?_eq_some_iff.mp ho).1
  refine ⟨?_, ?_⟩
  · exact (AdaptiveFoundProof.foundCausal cfg sh g run extended S n m words dummy
      t s s hg hE hS htn rfl rfl
      (List.take_append_of_le_length hop.le) hs hs' rfl rfl rfl
      (by simp [Probe.earlier, extended, List.getElem?_append_left hop])).symm
  · have hp : (⟨extended.ops.take run.ops.length, extended.init, extended.unsh⟩ :
        OnlineBatch.BatchRun) = run := by simp [extended]
    intro i
    have h := AdaptiveRowCausalityProof.rowCausality TracePrefix TraceUnitsPrefix
      cfg sh g extended S n m run.ops.length words dummy t i hg hE hS htn
      (by simpa only [hp] using ht)
    simpa only [hp] using h

theorem completed_snapshot (c : Api.Codec) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (requests : List Api.Request) (extra units : Nat)
    (hE : 0 < g.unitEntries)
    (hfit : RequesterCuts.WidthsFit g.unitEntries 0 (OnlineBatch.widths run))
    (hn : requests.length ≤ units * g.unitEntries)
    (hlen : (OnlineBatch.slots run).length = units * g.unitEntries)
    (hcorr : ∀ t, t ≤ (ApiCapacity.idleExtend requests extra).length →
      Api.stateOf c (Api.historyAt run t) =
        Api.stateAt (Api.stateOf c run.init) (ApiCapacity.idleExtend requests extra) t)
    (hext : (ApiCapacity.idleExtend requests extra).length = units * g.unitEntries) :
    CompletedApiSnapshot c g run requests units := by
  obtain ⟨hc, hf⟩ := RequesterCutsProof.boundary_state g run hE le_rfl
    (by rw [fs_length, hlen])
  refine ⟨hc, hf, ?_⟩
  intro n hncut
  have ht : RequesterCuts.traceCutSlots g run n = units * g.unitEntries := by
    simp only [RequesterCuts.traceCutSlots, hf, Nat.min_eq_right hncut]
  have hcuts := (RequesterTraceSaturatedCuts g run hE hfit n).2
  have hmap : Api.stateOf c (run.init ++ (List.range n).flatMap
      (fun i => DirectMasks.records ((OnlineBatch.traceOf g run).units i))) =
      Api.stateOf c (Api.historyAt run (units * g.unitEntries)) := by
    funext key
    unfold Api.stateOf Api.historyAt
    rw [OnlineCorrectnessProof.latest_append, OnlineCorrectnessProof.latest_append,
      hcuts key, ht]
  rw [hmap, hcorr _ (by omega), ApiCapacityProof.idle_state]
  simp only [Api.stateAt, List.take_of_length_le hn, List.take_length]

end RebuildBound.ApiContinuationProof

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Model.PublicApi Model.ApiContinuation
open ApiContinuationProof BatchFreshProof

theorem ApiIdleShape : ApiIdleShape_statement := by
  intro entries groups extra _ hv hf
  exact ⟨extend_lanes groups extra, extend_valid groups extra hv, extend_fit entries groups extra hf⟩

theorem ApiIdlePrefix : ApiIdlePrefix_statement := by
  intro c cfg sh g S init groups extra
  dsimp only
  obtain ⟨rest, he⟩ := extension_ops c cfg sh g S init groups extra
  have hr : ApiExecution.run c cfg sh g S init (extend groups extra) =
      ⟨(ApiExecution.run c cfg sh g S init groups).ops ++ rest, init, fun r => c.flag r.val⟩ := by
    exact congrArg (fun ops => (⟨ops, init, fun r => c.flag r.val⟩ : OnlineBatch.BatchRun)) he
  rw [hr]
  refine ⟨by simp, ?_, ?_⟩
  · simp only [slots_eq, slotsL_append, List.take_left]
  · intro j hj
    simp only [OnlineBatch.stateAt, List.take_append_of_le_length hj]

theorem ApiIdleObservations : ApiIdleObservations_statement := by
  intro c cfg sh g S init groups extra m hg hE hS
  dsimp only
  obtain ⟨rest, he⟩ := extension_ops c cfg sh g S init groups extra
  have hr : ApiExecution.run c cfg sh g S init (extend groups extra) =
      ⟨(ApiExecution.run c cfg sh g S init groups).ops ++ rest, init, fun r => c.flag r.val⟩ := by
    exact congrArg (fun ops => (⟨ops, init, fun r => c.flag r.val⟩ : OnlineBatch.BatchRun)) he
  intro words dummy t ht
  rw [hr]
  apply append_observations cfg sh g _ rest S _ m hg hE hS words dummy t ht
  rw [run_length] at ht
  simp only [extend_lanes, ApiCapacity.idleExtend, List.length_append, List.length_replicate]
  omega

theorem ApiIdleComplete : ApiIdleComplete_statement := by
  intro geo hgeo c g S init groups m units hInit hn hLen hg hE htarget hhor hv hfit hS
  dsimp only
  let extra := units * g.unitEntries - (groups.flatMap Group.lanes).length
  have hlength := complete_length g.unitEntries units groups htarget
  have hvalid := extend_valid groups extra hv
  have hfits := extend_fit g.unitEntries groups extra hfit
  have hcorrect := ApiExecutionStructural geo hgeo c g S init
    (complete g.unitEntries units groups) m hInit hn hLen hg hE
    (hlength ▸ hhor) hvalid (hlength ▸ hS)
  refine ⟨hcorrect, ?_⟩
  apply completed_snapshot c g _ (groups.flatMap Group.lanes) extra units hE
    (RequesterLoweredFits c geo.cfg geo.shapes g S init _ hE hfits) htarget
  · rw [run_length]
    exact hlength
  · simpa only [complete, extend_lanes] using
      (hcorrect.2.2 (fun _ _ _ => 0) (fun _ _ => 0)).2.1
  · simpa only [complete, extend_lanes] using hlength

theorem ApiIdleLive : ApiIdleLive_statement := by
  intro geo hgeo c g S init groups m units hInit hg hE htarget hhor hv hfit hS hcap
  dsimp only
  let extra := units * g.unitEntries - (groups.flatMap Group.lanes).length
  have hlength := complete_length g.unitEntries units groups htarget
  have hvalid := extend_valid groups extra hv
  have hfits := extend_fit g.unitEntries groups extra hfit
  have hc := (ApiCapacityExtension geo.keyCapacity (Api.stateOf c init)
    (init.map Rec.key) (groups.flatMap Group.lanes) extra hcap).1
  have hcorrect := ApiExecutionLive geo hgeo c g S init
    (complete g.unitEntries units groups) m hInit hg hE
    (hlength ▸ hhor) hvalid hfits (hlength ▸ hS)
    (by simpa only [complete, extend_lanes] using hc)
  refine ⟨hcorrect.1, hcorrect.2, ?_⟩
  apply completed_snapshot c g _ (groups.flatMap Group.lanes) extra units hE
    (RequesterLoweredFits c geo.cfg geo.shapes g S init _ hE hfits) htarget
  · rw [run_length]
    exact hlength
  · simpa only [complete, extend_lanes] using
      (hcorrect.1.2.2 (fun _ _ _ => 0) (fun _ _ => 0)).2.1
  · simpa only [complete, extend_lanes] using hlength

end RebuildBound
