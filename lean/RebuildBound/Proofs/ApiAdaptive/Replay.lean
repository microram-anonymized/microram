import RebuildBound.Spec.ApiAdaptive
import RebuildBound.Proofs.ApiExecution.Construction
import RebuildBound.Proofs.AdaptiveReplay

namespace RebuildBound.ApiAdaptiveProof
open Spec Model Model.Hierarchy Model.Online Model.PublicApi Model.ApiAdaptive

@[simp] theorem count_nil : Adaptive.slotCount (shape []) = 0 := rfl

@[simp] theorem count_cons (frame : Frame) (fs : List Frame) :
    Adaptive.slotCount (shape (frame :: fs)) =
      frame.kind.width + Adaptive.slotCount (shape fs) := rfl

@[simp] theorem count_append (fs gs : List Frame) :
    Adaptive.slotCount (shape (fs ++ gs)) =
      Adaptive.slotCount (shape fs) + Adaptive.slotCount (shape gs) := by
  simp [Adaptive.slotCount, Adaptive.shapeWidths, shape, List.sum_append]

@[simp] theorem request_width_replay {m : Nat} (choose : Chooser m)
    (rows : List (Fin m → Nat)) (frame : Frame) :
    (requests choose rows frame).lanes.length = frame.kind.width := by
  cases h : frame.group <;>
    simp [requests, h, Group.map, Group.lanes, Frame.kind, Adaptive.Kind.width]

@[simp] theorem requests_take {m : Nat} (choose : Chooser m)
    (rows : List (Fin m → Nat)) (cut : Nat) (frame : Frame) (h : frame.start ≤ cut) :
    requests choose (rows.take cut) frame = requests choose rows frame := by
  simp only [requests, List.take_take, Nat.min_eq_left h]

theorem requestGroups_take {m : Nat} (choose : Chooser m)
    (rows : List (Fin m → Nat)) (cut : Nat) (fs : List Frame)
    (h : ∀ f ∈ fs, f.start ≤ cut) :
    requestGroups choose (rows.take cut) fs = requestGroups choose rows fs := by
  apply List.map_congr_left
  intro f hf
  exact requests_take choose rows cut f (h f hf)

theorem rowsOf_take {n m : Nat} (t : Fin n → Fin m → Nat) (s : Nat) (hs : s ≤ n) :
    (Adaptive.rowsOf t n).take s = Adaptive.rowsOf t s := by
  simp [Adaptive.rowsOf, ← List.map_take, hs]

variable (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
  (S : Schedule) (init : List Rec)

/-- Physical compilation is prefix preserving, including the physical flags. -/
theorem operations_append (pre : List OnlineBatch.Op)
    (first rest : List (PublicApi.Group Api.Request)) :
    ApiExecution.operations c cfg sh g S init pre (first ++ rest) =
      ApiExecution.operations c cfg sh g S init pre first ++
        ApiExecution.operations c cfg sh g S init
          (pre ++ ApiExecution.operations c cfg sh g S init pre first) rest := by
  induction first generalizing pre with
  | nil => simp [ApiExecution.operations]
  | cons group first ih =>
    simp [ApiExecution.operations, ih, List.append_assoc]

@[simp] theorem records_length (ops : List OnlineBatch.Op) :
    (records ops).length = ApiExecution.offset ops := by
  simp [records, ApiExecution.offset, List.length_flatMap]

theorem operation_read (pre : List OnlineBatch.Op) (op : OnlineBatch.Op)
    (rest : List OnlineBatch.Op) :
    (AdaptiveReplayProof.kindOf op).op (fun i =>
      (records (pre ++ op :: rest)).getD (ApiExecution.offset pre + i) default) = op := by
  have h := AdaptiveReplayProof.kindOf_op op (records pre) (records rest)
  rw [records_length] at h
  simpa only [records, List.flatMap_append, List.flatMap_cons,
    List.getD_eq_getElem?_getD, List.append_assoc] using h

@[simp] theorem operation_kind {m : Nat} (choose : Chooser m)
    (rows : List (Fin m → Nat)) (pre : List OnlineBatch.Op) (frame : Frame) :
    AdaptiveReplayProof.kindOf
      (ApiExecution.operation c cfg sh g S init pre (requests choose rows frame)) =
        frame.kind := by
  cases h : frame.group <;>
    simp [ApiExecution.operation, requests, h, Group.map, AdaptiveReplayProof.kindOf,
      Frame.kind, ApiExecutionProof.chunkRecords_length]

@[simp] theorem compiled_offset {m : Nat} (choose : Chooser m)
    (rows : List (Fin m → Nat)) (fs : List Frame) :
    ApiExecution.offset
      (ApiExecution.operations c cfg sh g S init [] (requestGroups choose rows fs)) =
      Adaptive.slotCount (shape fs) := by
  unfold ApiExecution.offset
  rw [ApiExecutionProof.operations_widths]
  simp only [requestGroups, List.map_map, Function.comp_def, request_width_replay]
  simp [Adaptive.slotCount, Adaptive.shapeWidths, shape, List.map_map, Function.comp_def]

/-- At an internal start, reconstructing from the available rows gives the
same physical operation as reconstructing from the completed transcript. -/
theorem client_operation {m : Nat} (choose : Chooser m) (rows : List (Fin m → Nat))
    (before : List Frame) (frame : Frame) (after : List Frame)
    (hs : Adaptive.slotCount (shape before) ≤ rows.length)
    (hbefore : ∀ f ∈ before, f.start ≤ Adaptive.slotCount (shape before))
    (hframe : frame.start ≤ Adaptive.slotCount (shape before)) :
    frame.kind.op (client c cfg sh g S init (before ++ frame :: after) choose
      (rows.take (Adaptive.slotCount (shape before)))) =
      ApiExecution.operation c cfg sh g S init
        (ApiExecution.operations c cfg sh g S init [] (requestGroups choose rows before))
        (requests choose rows frame) := by
  let cut := Adaptive.slotCount (shape before)
  let short := rows.take cut
  let pre := ApiExecution.operations c cfg sh g S init [] (requestGroups choose short before)
  let op := ApiExecution.operation c cfg sh g S init pre (requests choose short frame)
  let rest := ApiExecution.operations c cfg sh g S init (pre ++ [op])
    (requestGroups choose short after)
  have hcompile : (ApiExecution.run c cfg sh g S init
      (requestGroups choose short (before ++ frame :: after))).ops = pre ++ op :: rest := by
    simp only [ApiExecution.run, requestGroups, List.map_append, List.map_cons]
    rw [operations_append]
    simp only [List.nil_append, ApiExecution.operations]
    rfl
  have hread := operation_read pre op rest
  rw [operation_kind c cfg sh g S init choose short pre frame] at hread
  have hoff : ApiExecution.offset pre = cut := compiled_offset c cfg sh g S init choose short before
  have hlen : short.length = cut := List.length_take_of_le hs
  have hclient : frame.kind.op
      (client c cfg sh g S init (before ++ frame :: after) choose short) = op := by
    unfold client
    rw [hcompile, hlen, ← hoff]
    exact hread
  have hpre : pre = ApiExecution.operations c cfg sh g S init []
      (requestGroups choose rows before) := by
    dsimp only [pre, short]
    rw [requestGroups_take choose rows cut before hbefore]
  have hop : op = ApiExecution.operation c cfg sh g S init
      (ApiExecution.operations c cfg sh g S init [] (requestGroups choose rows before))
      (requests choose rows frame) := by
    dsimp only [op]
    rw [hpre, show requests choose short frame = requests choose rows frame from
      requests_take choose rows cut frame hframe]
  exact hclient.trans hop

/-- Induct over remaining frames while retaining the compiled physical prelude.
Earlier public batches are reconstructed from the same prefixes on every call. -/
theorem replay_aux {m : Nat} (fs : List Frame) (choose : Chooser m)
    (t : Fin (Adaptive.slotCount (shape fs)) → Fin m → Nat) :
    ∀ (rest before : List Frame), fs = before ++ rest →
      Causal (Adaptive.slotCount (shape before)) rest →
      (∀ f ∈ before, f.start ≤ Adaptive.slotCount (shape before)) →
      Adaptive.replayOps (client c cfg sh g S init fs choose) t
        (shape rest) (Adaptive.slotCount (shape before)) =
      ApiExecution.operations c cfg sh g S init
        (ApiExecution.operations c cfg sh g S init []
          (requestGroups choose (Adaptive.rowsOf t (Adaptive.slotCount (shape fs))) before))
        (requestGroups choose (Adaptive.rowsOf t (Adaptive.slotCount (shape fs))) rest) := by
  let rows := Adaptive.rowsOf t (Adaptive.slotCount (shape fs))
  intro rest
  induction rest with
  | nil => intro before _ _ _; rfl
  | cons frame rest ih =>
    intro before hfs hc hb
    obtain ⟨hstart, _, hc⟩ := hc
    have hbound : Adaptive.slotCount (shape before) ≤ rows.length := by
      simp only [rows, AdaptiveReplayProof.rowsOf_length]
      rw [hfs, count_append, count_cons]
      omega
    have hop := client_operation c cfg sh g S init choose rows before frame rest hbound hb hstart
    rw [← hfs] at hop
    have ht : rows.take (Adaptive.slotCount (shape before)) =
        Adaptive.rowsOf t (Adaptive.slotCount (shape before)) :=
      rowsOf_take t _ (by simpa only [rows, AdaptiveReplayProof.rowsOf_length] using hbound)
    rw [ht] at hop
    change frame.kind.op (client c cfg sh g S init fs choose
        (Adaptive.rowsOf t (Adaptive.slotCount (shape before)))) ::
      Adaptive.replayOps (client c cfg sh g S init fs choose) t (shape rest)
        (Adaptive.slotCount (shape before) + frame.kind.width) =
      ApiExecution.operation c cfg sh g S init
        (ApiExecution.operations c cfg sh g S init [] (requestGroups choose rows before))
        (requests choose rows frame) ::
      ApiExecution.operations c cfg sh g S init
        (ApiExecution.operations c cfg sh g S init [] (requestGroups choose rows before) ++
          [ApiExecution.operation c cfg sh g S init
            (ApiExecution.operations c cfg sh g S init [] (requestGroups choose rows before))
            (requests choose rows frame)]) (requestGroups choose rows rest)
    rw [hop]
    congr 1
    have hb' : ∀ f ∈ before ++ [frame],
        f.start ≤ Adaptive.slotCount (shape (before ++ [frame])) := by
      intro f hf
      simp only [count_append, count_cons, count_nil, Nat.add_zero]
      rcases List.mem_append.mp hf with hmem | hmem
      · exact Nat.le_trans (hb f hmem) (Nat.le_add_right _ _)
      · have hf : f = frame := by simpa using hmem
        subst f
        exact Nat.le_trans hstart (Nat.le_add_right _ _)
    have hi := ih (before ++ [frame]) (by simpa [List.append_assoc] using hfs)
      (by simpa only [count_append, count_cons, count_nil, Nat.add_zero] using hc) hb'
    have hpre : ApiExecution.operations c cfg sh g S init []
        (requestGroups choose rows (before ++ [frame])) =
      ApiExecution.operations c cfg sh g S init [] (requestGroups choose rows before) ++
        [ApiExecution.operation c cfg sh g S init
          (ApiExecution.operations c cfg sh g S init [] (requestGroups choose rows before))
          (requests choose rows frame)] := by
      simp only [requestGroups, List.map_append, List.map_cons, List.map_nil]
      rw [operations_append]
      simp [ApiExecution.operations]
    dsimp only [rows] at hpre
    rw [hpre] at hi
    simpa only [count_append, count_cons, count_nil, Nat.add_zero] using hi

theorem replay {m : Nat} (fs : List Frame) (choose : Chooser m) (hc : Causal 0 fs)
    (t : Fin (Adaptive.slotCount (shape fs)) → Fin m → Nat) :
    Adaptive.replay (run c cfg sh g S init fs choose) t =
      ApiExecution.run c cfg sh g S init
        (requestGroups choose (Adaptive.rowsOf t (Adaptive.slotCount (shape fs))) fs) := by
  have h := replay_aux c cfg sh g S init fs choose t fs [] (by simp) hc (by simp)
  simp only [count_nil, requestGroups, List.map_nil, ApiExecution.operations] at h
  unfold Adaptive.replay run ApiExecution.run
  rw [h]
  rfl

end RebuildBound.ApiAdaptiveProof

namespace RebuildBound
open Spec Model Model.ApiAdaptive

theorem ApiAdaptiveReplay : ApiAdaptiveReplay_statement := by
  intro c cfg sh g S init m fs choose hc t
  exact ApiAdaptiveProof.replay c cfg sh g S init fs choose hc t

theorem ApiAdaptiveInteraction : ApiAdaptiveInteraction_statement := by
  intro c cfg sh g S init m fs choose hc words dummy
  dsimp only
  rw [AdaptiveReplayProof.realized_eq_replay cfg sh g S
    (run c cfg sh g S init fs choose) (Adaptive.slotCount (shape fs)) rfl words dummy]
  exact ApiAdaptiveReplay c cfg sh g S init m fs choose hc _

end RebuildBound
