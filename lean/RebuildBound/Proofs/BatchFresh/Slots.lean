import RebuildBound.Spec.Model.OnlineBatch
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# BatchFresh: slots and operations

The slots of a run are its operations' lanes in order: operation `j`'s lanes
are the slots `[fs j, fs (j + 1))`, with `fs j` the total width of the first
`j` operations (`slot_at`, `slot_inv`). The first slot of a slot's operation is
`chunkStart` (`chunkStart_slot`).
-/

namespace RebuildBound.BatchFreshProof

open RebuildBound.Model RebuildBound.Model.OnlineBatch

/-- The slots of one operation at index `j`. -/
def opSlots (oj : Op × Nat) : List Slot :=
  oj.1.lanes.zipIdx.map fun rl => ⟨oj.2, rl.2, rl.1.1, rl.1.2⟩

/-- The slots of a list of operations, indexed from `k`. -/
def slotsL (ops : List Op) (k : Nat) : List Slot := (ops.zipIdx k).flatMap opSlots

theorem slots_eq (run : BatchRun) : slots run = slotsL run.ops 0 := rfl

theorem slotsL_nil (k : Nat) : slotsL [] k = [] := rfl

theorem slotsL_cons (o : Op) (ops : List Op) (k : Nat) :
    slotsL (o :: ops) k = opSlots (o, k) ++ slotsL ops (k + 1) := by
  simp [slotsL, List.zipIdx_cons]

theorem slotsL_append : ∀ (a b : List Op) (k : Nat),
    slotsL (a ++ b) k = slotsL a k ++ slotsL b (k + a.length)
  | [], b, k => by simp [slotsL]
  | o :: a, b, k => by
    rw [List.cons_append, slotsL_cons, slotsL_append a b (k + 1), slotsL_cons, List.append_assoc]
    simp only [List.length_cons]
    rw [show k + 1 + a.length = k + (a.length + 1) by omega]

theorem length_opSlots (oj : Op × Nat) : (opSlots oj).length = oj.1.lanes.length := by
  simp [opSlots]

theorem length_slotsL : ∀ (ops : List Op) (k : Nat),
    (slotsL ops k).length = (ops.map fun o => o.lanes.length).sum
  | [], _ => rfl
  | o :: ops, k => by
    rw [slotsL_cons, List.length_append, length_opSlots, length_slotsL ops (k + 1)]
    simp

theorem getElem?_opSlots (o : Op) (j l : Nat) :
    (opSlots (o, j))[l]? = o.lanes[l]?.map fun rp => (⟨j, l, rp.1, rp.2⟩ : Slot) := by
  simp only [opSlots, List.getElem?_map, List.getElem?_zipIdx, Option.map_map]
  cases o.lanes[l]? <;> simp

/-- The first slot of operation `j`. -/
def fs (run : BatchRun) (j : Nat) : Nat := ((widths run).take j).sum

theorem fs_eq (run : BatchRun) (j : Nat) : fs run j = (slotsL (run.ops.take j) 0).length := by
  rw [length_slotsL, fs, widths, List.map_take]

theorem fs_zero (run : BatchRun) : fs run 0 = 0 := by simp [fs]

theorem fs_succ (run : BatchRun) {j : Nat} {o : Op} (h : run.ops[j]? = some o) :
    fs run (j + 1) = fs run j + o.lanes.length := by
  obtain ⟨hj, e⟩ := List.getElem?_eq_some_iff.1 h
  have hj' : j < (widths run).length := by simpa [widths] using hj
  rw [fs, fs, List.sum_take_succ _ _ hj']
  simp [widths, e]

theorem fs_mono (run : BatchRun) {j j' : Nat} (h : j ≤ j') : fs run j ≤ fs run j' := by
  unfold fs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.sum_append]
  omega

theorem fs_length (run : BatchRun) : fs run run.ops.length = (slots run).length := by
  rw [fs_eq, List.take_length, slots_eq]

theorem slots_split (run : BatchRun) {j : Nat} (hj : j < run.ops.length) :
    slots run = slotsL (run.ops.take j) 0 ++
      (opSlots (run.ops[j], j) ++ slotsL (run.ops.drop (j + 1)) (j + 1)) := by
  conv_lhs => rw [slots_eq, ← List.take_append_drop j run.ops, List.drop_eq_getElem_cons hj]
  rw [slotsL_append, slotsL_cons]
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), Nat.zero_add]

/-- Lane `l` of operation `j` is the slot `fs j + l`. -/
theorem slot_at (run : BatchRun) {j l : Nat} {o : Op} {rp : Rec × Bool} (ho : run.ops[j]? = some o)
    (hl : o.lanes[l]? = some rp) : (slots run)[fs run j + l]? = some ⟨j, l, rp.1, rp.2⟩ := by
  obtain ⟨hj, e⟩ := List.getElem?_eq_some_iff.1 ho
  have hll : l < o.lanes.length := (List.getElem?_eq_some_iff.1 hl).1
  rw [slots_split run hj, List.getElem?_append_right (by rw [fs_eq]; exact Nat.le_add_right _ _), fs_eq, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [length_opSlots, e]; exact hll), getElem?_opSlots, e, hl]
  rfl

/-- Every slot `t` is a lane of its operation, at `t = fs op + lane`. -/
theorem slot_inv (run : BatchRun) {t : Nat} {s : Slot} (hs : (slots run)[t]? = some s) :
    ∃ o, run.ops[s.op]? = some o ∧ o.lanes[s.lane]? = some (s.record, s.probes) ∧
      t = fs run s.op + s.lane := by
  have ht : t < fs run run.ops.length := by
    rw [fs_length]; exact (List.getElem?_eq_some_iff.1 hs).1
  have key : ∀ J, J ≤ run.ops.length → t < fs run J →
      ∃ j, j < J ∧ fs run j ≤ t ∧ t < fs run (j + 1) := by
    intro J
    induction J with
    | zero => intro _ h; rw [fs_zero] at h; omega
    | succ J ih =>
      intro hJ h
      by_cases h' : t < fs run J
      · obtain ⟨j, h1, h2, h3⟩ := ih (by omega) h'
        exact ⟨j, by omega, h2, h3⟩
      · exact ⟨J, by omega, by omega, h⟩
  obtain ⟨j, hj, h1, h2⟩ := key _ (Nat.le_refl _) ht
  have ho : run.ops[j]? = some run.ops[j] := List.getElem?_eq_getElem hj
  rw [fs_succ run ho] at h2
  have hl : t - fs run j < run.ops[j].lanes.length := by omega
  have hat := slot_at run ho (List.getElem?_eq_getElem hl)
  rw [Nat.add_sub_cancel' h1, hs] at hat
  cases hat
  exact ⟨run.ops[j], ho, by simp [List.getElem?_eq_getElem hl], by dsimp only; omega⟩

theorem chunkStart_le : ∀ (ws : List Nat) (t : Nat), chunkStart ws t ≤ t
  | [], t => by simp [chunkStart]
  | w :: ws, t => by
    unfold chunkStart
    split_ifs with h
    · exact Nat.zero_le _
    · have := chunkStart_le ws (t - w); omega

theorem chunkStart_take : ∀ (ws : List Nat) (j t : Nat), (ws.take j).sum ≤ t →
    (∀ h : j < ws.length, t < (ws.take j).sum + ws[j]) → j < ws.length →
    chunkStart ws t = (ws.take j).sum
  | [], _, _, _, _, h => by simp at h
  | w :: ws, 0, t, _, h2, _ => by
    have := h2 (by simp)
    simp only [List.take_zero, List.sum_nil, Nat.zero_add, List.getElem_cons_zero] at this
    simp [chunkStart, this]
  | w :: ws, j + 1, t, h1, h2, h3 => by
    simp only [List.take_succ_cons, List.sum_cons] at h1 h2 ⊢
    have h4 := h2 (by simpa using h3)
    simp only [List.getElem_cons_succ] at h4
    unfold chunkStart
    rw [if_neg (by omega), chunkStart_take ws j (t - w) (by omega) (fun _ => by omega)
      (by simpa using h3)]

/-- The first slot of a slot's operation. -/
theorem chunkStart_slot (run : BatchRun) {t : Nat} {s : Slot} (hs : (slots run)[t]? = some s) :
    chunkStart (widths run) t = fs run s.op := by
  obtain ⟨o, ho, hl, ht⟩ := slot_inv run hs
  have hll := (List.getElem?_eq_some_iff.1 hl).1
  obtain ⟨hj, e⟩ := List.getElem?_eq_some_iff.1 ho
  refine chunkStart_take _ _ _ (by rw [← fs]; omega) (fun h => ?_) (by simpa [widths] using hj)
  rw [← fs]
  simp only [widths, List.getElem_map, e]
  omega

/-- Slots in order have operations in order. -/
theorem op_mono (run : BatchRun) {t t' : Nat} {s s' : Slot} (hs : (slots run)[t]? = some s)
    (hs' : (slots run)[t']? = some s') (h : t < t') : s.op ≤ s'.op := by
  obtain ⟨o, ho, hl, ht⟩ := slot_inv run hs
  obtain ⟨o', ho', hl', ht'⟩ := slot_inv run hs'
  by_contra hc
  have h1 := fs_mono run (show s'.op + 1 ≤ s.op by omega)
  have h2 := fs_succ run ho'
  have := (List.getElem?_eq_some_iff.1 hl').1
  omega

/-- A slot of an earlier operation lies before the later operation's first slot. -/
theorem lt_fs (run : BatchRun) {t : Nat} {s : Slot} (hs : (slots run)[t]? = some s) {j : Nat}
    (h : s.op < j) : t < fs run j := by
  obtain ⟨o, ho, hl, ht⟩ := slot_inv run hs
  have h1 := fs_mono run (show s.op + 1 ≤ j by omega)
  have h2 := fs_succ run ho
  have := (List.getElem?_eq_some_iff.1 hl).1
  omega

theorem fs_le (run : BatchRun) {t : Nat} {s : Slot} (hs : (slots run)[t]? = some s) :
    fs run s.op ≤ t := by
  obtain ⟨o, ho, hl, ht⟩ := slot_inv run hs
  omega

/-- Two lanes of one operation with the same key: the later one is a duplicate. -/
theorem duplicate_of (run : BatchRun) {t t' : Nat} {s s' : Slot} (hs : (slots run)[t]? = some s)
    (hs' : (slots run)[t']? = some s') (hop : s.op = s'.op) (h : t < t')
    (hk : s.record.key = s'.record.key) : duplicate run s' = true := by
  obtain ⟨o, ho, hl, ht⟩ := slot_inv run hs
  obtain ⟨o', ho', hl', ht'⟩ := slot_inv run hs'
  rw [hop, ho'] at ho
  cases ho
  have hll : s.lane < s'.lane := by rw [hop] at ht; omega
  unfold duplicate
  rw [ho']
  simp only [Option.map_some, Option.getD_some, List.any_eq_true, beq_iff_eq]
  refine ⟨(s.record, s.probes), ?_, hk⟩
  refine List.mem_of_getElem? (i := s.lane) ?_
  rw [List.getElem?_take, if_pos hll, hl]

end RebuildBound.BatchFreshProof
