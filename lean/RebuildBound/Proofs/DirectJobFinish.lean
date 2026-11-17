import RebuildBound.Spec.DirectJobFinish
import RebuildBound.Proofs.DirectJobA
import RebuildBound.Proofs.DirectJobContract
import RebuildBound.Proofs.S4b.Drain

namespace RebuildBound
open Model Model.DirectJob

theorem DirectJobFinishTopology : Spec.DirectJobFinishTopology_statement := by
  intro g hg hd
  obtain ⟨ha, hdi, hn⟩ := DirectJobALemmas.topology g hg hd
  have hsmall : g.outputHomes ≤ 2 ^ (g.K + 3) := by
    have hmax := hg.2.1
    have hout := hg.2.2.1
    rw [hout, Geometry.U, Nat.pow_add]
    norm_num
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right (2 ^ g.K) hmax
  cases hr : g.ranges with
  | direct =>
    simp only [Geometry.finishTopology, hr, SepGeom.Valid]
    exact ⟨⟨ha.1, by simpa [SepGeom.d] using ha.2.1,
      by change g.aTopology.N ≤ _; rw [hn]; exact hsmall⟩,
      hdi, hn, fun _ => rfl⟩
  | dfs i r p =>
    have henv : g.outputHomes ≤ 2 ^ (i + r) := by
      have h := hg.2.2.2.2.2.2
      simp only [hr] at h
      exact h.2.1
    simp only [Geometry.finishTopology, hr, SepGeom.Valid]
    exact ⟨⟨ha.1, by simpa [SepGeom.d] using ha.2.1,
      by change g.aTopology.N ≤ _; rw [hn]; exact henv⟩,
      hdi, hn, fun _ => rfl⟩

theorem DirectJobFinishDistribution : Spec.DirectJobFinishDistribution_statement := by
  intro g word pool hg hd
  cases hr : g.ranges with
  | direct =>
    -- one range: every home is below `2 ^ I`
    have hv := (DirectJobFinishTopology g hg hd).1
    have hz : ∀ x : Rec, sRange g.finishTopology word x = 0 := fun x =>
      Nat.div_eq_of_lt (lt_of_lt_of_le (S4b.sHome_lt hv word x)
        (by simpa [Geometry.finishTopology, hr] using hv.2.2))
    have h1 : g.finishTopology.rangeBits = 0 := by simp [Geometry.finishTopology, hr]
    simp only [sLeaves, SepGeom.ranges, distributeA, hr, h1, hz]
    simp
  | dfs i r p => simp only [sLeaves, SepGeom.ranges, Geometry.finishTopology, distributeA, hr]; rfl

namespace DirectJobFinishLemmas

theorem topology_U (g : Geometry) : g.finishTopology.U = g.U := by
  cases h : g.ranges <;> simp [Geometry.finishTopology, h, SepGeom.U, Geometry.aTopology, Geometry.U]

theorem topology_C (g : Geometry) : g.finishTopology.C = 64 := by
  cases h : g.ranges <;> simp [Geometry.finishTopology, h, Geometry.aTopology]

theorem topology_K (g : Geometry) : g.finishTopology.K = g.K := by
  cases h : g.ranges <;> simp [Geometry.finishTopology, h, Geometry.aTopology]

theorem topology_bTierPages (g : Geometry) : g.finishTopology.bTierPages = 1 := by
  cases h : g.ranges <;> simp [Geometry.finishTopology, h, Geometry.aTopology]

theorem topology_home (g : Geometry) (word : Model.LogicalKey → Nat) (x : Rec) :
    sHome g.finishTopology word x = g.home (word x.key) := by
  cases h : g.ranges <;> simp only [Geometry.finishTopology, h] <;> rfl

theorem insert_state (g : Geometry) (word : Model.LogicalKey → Nat) (b : Table)
    (ordinal : Nat) (st : SFin) (sources : List Nat) :
    (stepsAnalytical (finishTransition g word b) ordinal st sources).state =
      sources.foldl (fun st i => sInsertBucket g.finishTopology word b.bLanes i st) st := by
  induction sources generalizing ordinal st with
  | nil => rfl
  | cons i sources ih => simp only [stepsAnalytical, List.foldl_cons, finishTransition]; exact ih _ _

theorem firstFailure_append (a b : List CheckEvent) :
    firstFailure (a ++ b) = (firstFailure a).or (firstFailure b) := by
  exact List.find?_append

end DirectJobFinishLemmas

theorem DirectJobFinishInsertRefinement : Spec.DirectJobFinishInsertRefinement_statement := by
  intro g word b main leaves
  simp only [analyticalInsert, DirectJobFinishLemmas.insert_state, sFinish,
    DirectJobFinishLemmas.topology_U, finishInitial]

theorem DirectJobFinishInsertSimulation : Spec.DirectJobFinishInsertSimulation_statement := by
  intro g word b main leaves
  exact DirectJobALemmas.steps_simulation _ _ _ _

namespace DirectJobFinishLemmas

theorem drainEvents_append (g : Geometry) (a b : List (STest × Nat)) :
    drainEvents g (a ++ b) = drainEvents g a ++
      (b.zipIdx a.length).map fun p => ⟨⟨.drain, .outputTier, p.2⟩, p.1.2, g.outputCapacity⟩ := by
  simp [drainEvents, List.zipIdx_append]

theorem fold_events (g : Geometry) (records : List (Rec × Bool))
    (chunks : List (List (Rec × Bool))) (trace : List (STest × Nat)) :
    drainEvents g (chunks.foldl sDrainStep (records.map some, trace)).2 = drainEvents g trace ++
      (drainAnalytical .drain .outputTier g.outputCapacity trace.length records chunks).trace := by
  induction chunks generalizing records trace with
  | nil => simp [drainAnalytical]
  | cons chunk chunks ih =>
    rw [List.foldl_cons]
    have hs : sDrainStep (records.map some, trace) chunk =
        ((records ++ chunk).map some, trace ++ [(.drain, (records ++ chunk).length)]) := by
      simp only [sDrainStep, D4b.appendFill_full _ (D4b.free_map_some records),
        D4b.occupied_append, D4b.occupied_map_some, List.length_append, List.map_append]
    rw [hs, ih, drainEvents_append]
    simp [drainAnalytical, appendTransition, List.append_assoc]

theorem analytical_length {α : Type} (phase : Phase) (site : Site) (capacity ordinal : Nat)
    (state : List α) (chunks : List (List α)) :
    (drainAnalytical phase site capacity ordinal state chunks).trace.length = chunks.length := by
  induction chunks generalizing ordinal state with
  | nil => rfl
  | cons _ _ ih => simp [drainAnalytical, ih]

/-- The direct drain's chunks and resolution step replay `sDrain`: same lanes,
and the events are its numbered trace. -/
theorem drain_events (g : Geometry) (st : SFin) :
    let first := drainAnalytical .drain .outputTier g.outputCapacity 0 [] (finishChunks st)
    let last := finishDrainTransition g (finishChunks st).length st.ins (first.records.map some)
    last.1 = (sDrain st).1 ∧ first.trace ++ [last.2] = drainEvents g (sDrain st).2 := by
  have hf := (S4b.drain_fold (finishChunks st) [] [] rfl).1
  simp only [List.nil_append] at hf
  have hr := DirectJobDrainRecords (Rec × Bool) .drain .outputTier g.outputCapacity 0 []
    (finishChunks st)
  simp only [List.nil_append] at hr
  have ht := fold_events g [] (finishChunks st) []
  have he : drainEvents g [] = [] := rfl
  simp only [List.map_nil, List.length_nil, he, List.nil_append] at ht
  have hl : ((finishChunks st).foldl sDrainStep ([], [])).2.length = (finishChunks st).length := by
    have h := congrArg List.length ht
    simp only [drainEvents, List.length_map, List.length_zipIdx] at h
    rw [h, analytical_length]
  have hc : (st.leaves.map (fun L => L.map fun x => (x, true)) ++
      st.bcopy.map (fun L => L.map fun x => (x, false))) = finishChunks st := rfl
  simp only [finishDrainTransition, resolveLeftovers, sDrain, sDrainStep, hr, hc, hf]
  rw [drainEvents_append, ht, hl]
  simp

end DirectJobFinishLemmas

theorem DirectJobFinishDrainSimulation : Spec.DirectJobFinishDrainSimulation_statement := by
  intro g st
  obtain ⟨ht, he⟩ := DirectJobFinishLemmas.drain_events g st
  simp only [finishDrainBounded]
  rw [DirectJobDrainSimulation, ← he, ← ht, DirectJobFinishLemmas.firstFailure_append]
  cases h : firstFailure (drainAnalytical .drain .outputTier g.outputCapacity 0 []
    (finishChunks st)).trace with
  | some e => rfl
  | none =>
    simp only [Option.or]
    simp only [DirectJob.firstFailure, List.find?_cons, List.find?_nil]
    split <;> simp_all

theorem DirectJobFinishSimulation : Spec.DirectJobFinishSimulation_statement := by
  intro g word b main leaves
  unfold finishBounded analyticalFinish
  rw [DirectJobFinishInsertSimulation, DirectJobFinishLemmas.firstFailure_append]
  cases h : firstFailure (analyticalInsert g word b main leaves).trace with
  | some e => rfl
  | none =>
    simp only [Option.or]
    rw [DirectJobFinishDrainSimulation]
    cases firstFailure (drainEvents g (sDrain (analyticalInsert g word b main leaves).state).2) <;> rfl

theorem DirectJobFinishBLanes : Spec.DirectJobFinishBLanes_statement := by
  intro b h
  refine ⟨by simp [Table.bLanes], ?_, ?_⟩
  · intro bucket hb
    obtain ⟨rs, hrs, rfl⟩ := List.mem_map.mp hb
    have := h rs hrs
    simp only [List.length_append, List.length_map, List.length_replicate]
    omega
  · simp only [Table.bLanes, List.map_map]
    suffices hh : ∀ rs : List Rec, Bucket.recs (rs.map some ++ List.replicate (64 - rs.length) none) = rs by
      simpa only [Function.comp_def, hh] using List.map_id' b.main
    intro rs
    simp [Bucket.recs]
namespace DirectJobFinishLemmas

theorem finish_trace (g : Geometry) (word : Model.LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec)) :
    ∀ e ∈ (analyticalFinish g word b main leaves).trace,
      (e.id.phase = .finish ∧ e.id.site = .insertion ∧ e.capacity = g.insertionCapacity) ∨
      (e.id.phase = .drain ∧ e.id.site = .outputTier ∧ e.capacity = g.outputCapacity) := by
  intro e he
  simp only [analyticalFinish, List.mem_append] at he
  rcases he with he | he
  · left
    exact DirectJobALemmas.trace_property (finishTransition g word b)
      (fun e => e.id.phase = .finish ∧ e.id.site = .insertion ∧ e.capacity = g.insertionCapacity)
      (fun _ _ _ => ⟨rfl, rfl, rfl⟩) _ _ _ e he
  · right
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp he
    exact ⟨rfl, rfl, rfl⟩

end DirectJobFinishLemmas

theorem DirectJobFinishFailureCheck : Spec.DirectJobFinishFailureCheck_statement := by
  intro g word b main leaves e he
  rw [DirectJobFinishSimulation] at he
  cases hf : firstFailure (analyticalFinish g word b main leaves).trace with
  | none => simp [hf] at he
  | some event =>
    simp only [hf, Except.error.injEq] at he
    subst event
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    exact ⟨hm, by simpa [CheckEvent.passed] using hp,
      DirectJobFinishLemmas.finish_trace g word b main leaves e hm⟩

namespace DirectJobFinishLemmas

theorem appendFill_length {α : Type} (B : List (Option α)) (L : List α) :
    (appendFill B L).length = max B.length (occupied B + L.length) := by
  unfold appendFill
  rw [List.length_append, D1Lemmas.fill_length, List.length_map,
    D4b.fill_snd, List.length_drop]
  have h := D4b.countP_none_add_some B
  unfold occupied
  omega

theorem drainBounded_length {α : Type} (phase : Phase) (site : Site)
    (capacity ordinal : Nat) (state : List α) (chunks : List (List α))
    (records : List α) (hstate : state.length ≤ capacity)
    (hr : drainBounded phase site capacity ordinal state chunks = .ok records) :
    records.length ≤ capacity := by
  induction chunks generalizing ordinal state with
  | nil =>
    simp only [drainBounded, Except.ok.injEq] at hr
    simpa [← hr] using hstate
  | cons chunk chunks ih =>
    simp only [drainBounded] at hr
    split at hr
    · rename_i hp
      exact ih (ordinal + 1) (state ++ chunk)
        (by simpa [appendTransition, CheckEvent.passed] using hp) hr
    · cases hr


end DirectJobFinishLemmas

theorem DirectJobFinishDrainWidth : Spec.DirectJobFinishDrainWidth_statement := by
  intro g st tier hr
  unfold finishDrainBounded at hr
  cases hfirst : drainBounded .drain .outputTier g.outputCapacity 0 [] (finishChunks st) with
  | error e => simp [hfirst] at hr
  | ok first =>
    simp only [hfirst] at hr
    split at hr
    · rename_i hp
      have hfirstBound := DirectJobFinishLemmas.drainBounded_length .drain .outputTier g.outputCapacity
        0 [] (finishChunks st) first (by simp) hfirst
      have hlastBound : occupied (appendFill (resolveLeftovers st.ins (first.map some)).1
          ((resolveLeftovers st.ins (first.map some)).2.map fun x => (x, false))) ≤ g.outputCapacity := by
        exact of_decide_eq_true hp
      have hlen : (resolveLeftovers st.ins (first.map some)).1.length = first.length := by
        simp [resolveLeftovers]
      simp only [Except.ok.injEq] at hr
      rw [← hr]
      simp only [finishDrainTransition, List.length_map, DirectJobFinishLemmas.appendFill_length]
      rw [D4b.occupied_appendFill, List.length_map] at hlastBound
      rw [hlen]
      exact max_le hfirstBound hlastBound
    · cases hr

theorem DirectJobFinishOutputWidth : Spec.DirectJobFinishOutputWidth_statement := by
  intro g word b main leaves out ho
  unfold finishBounded at ho
  cases hi : insertBounded g word b main leaves with
  | error e => simp [hi] at ho
  | ok st =>
    simp only [hi] at ho
    cases hd : finishDrainBounded g st with
    | error e => simp [hd] at ho
    | ok tier =>
      have hw := DirectJobFinishDrainWidth g st tier hd
      simp only [hd, Except.ok.injEq] at ho
      rw [← ho]
      simp only [finishOutput, List.length_append, List.length_replicate]
      omega

end RebuildBound
