import RebuildBound.Proofs.BatchFresh.Requester
import RebuildBound.Proofs.OnlineCorrectness.Slices

/-!
# AdaptiveFlagSound: where a stored record came from

The converse of `BatchFreshProof.inv_stateAt`: every record in a frozen unit
`u` of the requester is the record of a slot in `[u E, (u + 1) E)`, and every
record of the current unit the record of a slot since the last freeze
(`prov_stateAt`). So a record of the trace's slice `[a, b)` is the record of a
slot in `[a P, b P)` (`traceSlice_slot`), with `P = E r0` the slots of one
prefix.
-/

namespace RebuildBound.AdaptiveFlagSoundProof

open RebuildBound.Model RebuildBound.Model.OnlineBatch
open RebuildBound.Model.Online (OnlineGeom)
open RebuildBound.BatchFreshProof RebuildBound.OnlineCorrectnessProof

/-- The record of slot `i`. -/
def slotRec (run : BatchRun) (i : Nat) : Option Rec := (slots run)[i]?.map Slot.record

/-- Provenance after the first `F` slots. -/
structure Prov (E : Nat) (run : BatchRun) (F : Nat) (st : Requester.State) : Prop where
  len : st.frozen.length * E + st.current.length = F
  cur : st.current.length < E
  frozen : ∀ u (hu : u < st.frozen.length) x, some x ∈ st.frozen[u] →
    ∃ i, u * E ≤ i ∧ i < (u + 1) * E ∧ slotRec run i = some x
  current : ∀ x, some x ∈ st.current →
    ∃ i, st.frozen.length * E ≤ i ∧ i < F ∧ slotRec run i = some x

theorem prov_insert {E : Nat} {run : BatchRun} {F : Nat} {st : Requester.State} {l : Option Rec}
    (hE : 0 < E) (hP : Prov E run F st) (hl : ∀ y, l = some y → slotRec run F = some y) :
    Prov E run (F + 1) (Requester.insert E st l) := by
  obtain ⟨hlen, hcur, hfr, hcu⟩ := hP
  unfold Requester.insert
  split_ifs with h
  · simp only [List.length_append, List.length_singleton] at h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton, List.length_nil, Nat.add_zero,
        Nat.succ_mul]
      omega
    · simpa using hE
    · intro u hu x hx
      simp only [List.length_append, List.length_singleton] at hu
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · rw [List.getElem_append_left hu] at hx
        exact hfr u hu x hx
      · subst hu
        rw [List.getElem_append_right (le_refl _)] at hx
        simp only [Nat.sub_self, List.getElem_singleton, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hx
        · obtain ⟨i, h1, h2, h3⟩ := hcu x hx
          exact ⟨i, h1, by rw [Nat.succ_mul]; omega, h3⟩
        · exact ⟨F, by omega, by rw [Nat.succ_mul]; omega, hl x hx.symm⟩
    · intro x hx
      simp at hx
  · simp only [List.length_append, List.length_singleton] at h
    refine ⟨by simp only [List.length_append, List.length_singleton]; omega,
      by simp only [List.length_append, List.length_singleton]; omega, hfr, ?_⟩
    intro x hx
    dsimp only at hx ⊢
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨i, h1, h2, h3⟩ := hcu x hx
      exact ⟨i, h1, by omega, h3⟩
    · rw [List.mem_singleton] at hx
      exact ⟨F, by omega, by omega, hl x hx.symm⟩

theorem prov_cur {E : Nat} {run : BatchRun} {F : Nat} {st : Requester.State} {f : Bucket → Bucket}
    (hP : Prov E run F st) (hlen : (f st.current).length = st.current.length)
    (hsub : ∀ x, some x ∈ f st.current → some x ∈ st.current) :
    Prov E run F ⟨st.frozen, f st.current⟩ :=
  ⟨by dsimp only; rw [hlen]; exact hP.len, by dsimp only; rw [hlen]; exact hP.cur, hP.frozen,
    fun x hx => hP.current x (hsub x hx)⟩

theorem mem_of_clearKey {k : LogicalKey} {cur : Bucket} {x : Rec} (h : some x ∈ Requester.clearKey k cur) :
    some x ∈ cur := by
  unfold Requester.clearKey at h
  obtain ⟨y, hy, e⟩ := List.mem_map.1 h
  cases y with
  | none => simp at e
  | some y =>
    have : y = x := by
      by_cases hk : (y.key != k) = true
      · simpa [Option.filter, hk] using e
      · simp [Option.filter, hk] at e
    rw [← this]; exact hy

theorem mem_of_foldl_clear (L : List Rec) :
    ∀ (cur : Bucket) {x : Rec}, some x ∈ L.foldl (fun u r => Requester.clearKey r.key u) cur →
      some x ∈ cur := by
  induction L with
  | nil => intro cur x h; exact h
  | cons a L ih =>
    intro cur x h
    exact mem_of_clearKey (ih _ h)

theorem prov_stateAt (g : OnlineGeom) (run : BatchRun) (hE : 0 < g.unitEntries) :
    ∀ j, j ≤ run.ops.length → Prov g.unitEntries run (fs run j) (stateAt g run j) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [stateAt_zero, fs_zero]
    exact ⟨by simp, by simpa using hE, fun u hu => by simp at hu, fun x hx => by simp at hx⟩
  | succ j ih =>
    intro hj
    have hjl : j < run.ops.length := hj
    have ho : run.ops[j]? = some run.ops[j] := List.getElem?_eq_getElem hjl
    rw [stateAt_succ g run ho]
    have hP := ih (Nat.le_of_lt hjl)
    generalize run.ops[j] = o at ho
    have access : ∀ (r : Rec) (b : Bool), o.lanes = [(r, b)] →
        Prov g.unitEntries run (fs run (j + 1))
          (Requester.step g.unitEntries (stateAt g run j) (.access r true)) := by
      intro r b hl
      have hfs : fs run (j + 1) = fs run j + 1 := by rw [fs_succ run ho, hl]; rfl
      have hat : (slots run)[fs run j]? = some ⟨j, 0, r, b⟩ := by
        have := slot_at run ho (l := 0) (rp := (r, b)) (by rw [hl]; rfl)
        simpa using this
      rw [hfs]
      simp only [Requester.step, ite_true]
      refine prov_insert hE (prov_cur (f := Requester.clearKey r.key) hP
        (by simp [Requester.clearKey]) (fun x hx => mem_of_clearKey hx)) ?_
      intro y hy
      cases hy
      simp [slotRec, hat]
    cases o with
    | probe r => exact access r true rfl
    | blind r => exact access r false rfl
    | batch lanes =>
      have hfs : fs run (j + 1) = fs run j + lanes.length := by
        rw [fs_succ run ho]; simp [Op.lanes]
      have hat : ∀ l (h : l < lanes.length),
          (slots run)[fs run j + l]? = some ⟨j, l, lanes[l], true⟩ := by
        intro l h
        exact slot_at run ho (rp := (lanes[l], true)) (by simp [Op.lanes, h])
      change Prov g.unitEntries run (fs run (j + 1))
        (Requester.step g.unitEntries (stateAt g run j) (.batch lanes))
      rw [step_batch, hfs]
      have h0 : Prov g.unitEntries run (fs run j)
          ⟨(stateAt g run j).frozen,
            lanes.foldl (fun u r => Requester.clearKey r.key u) (stateAt g run j).current⟩ :=
        prov_cur (f := fun c => lanes.foldl (fun u r => Requester.clearKey r.key u) c) hP (length_foldl_clear lanes _) (fun x hx => mem_of_foldl_clear lanes _ hx)
      have := foldl_idx (bstep g.unitEntries lanes)
        (fun i σ => Prov g.unitEntries run (fs run j + i) σ) lanes.zipIdx 0 _ (by simpa using h0)
        (by
          intro i hi σ hσ
          have hi' : i < lanes.length := by simpa using hi
          have hz : lanes.zipIdx[i] = (lanes[i], i) := by simp
          simp only [Nat.zero_add] at hσ ⊢
          rw [hz, show fs run j + (i + 1) = (fs run j + i) + 1 by omega]
          refine prov_insert hE hσ ?_
          intro y hy
          split_ifs at hy with hs
          cases hy
          show slotRec run (fs run j + i) = some lanes[i]
          simp [slotRec, hat i hi'])
      simpa using this

/-! ### Trace slices -/

theorem traceSlice_mem {tr : Hierarchy.Trace} {a b : Nat} {x : Rec}
    (h : x ∈ traceSlice tr a b) :
    ∃ p, a ≤ p ∧ p < b ∧ x ∈ DirectMasks.records (tr.units p) := by
  unfold traceSlice at h
  obtain ⟨p, hp, hx⟩ := List.mem_flatMap.1 h
  rw [List.mem_range'] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact ⟨a + 1 * i, by omega, by omega, hx⟩

theorem mem_traceSlice {tr : Hierarchy.Trace} {a b p : Nat} {x : Rec} (h1 : a ≤ p) (h2 : p < b)
    (hx : x ∈ DirectMasks.records (tr.units p)) : x ∈ traceSlice tr a b := by
  unfold traceSlice
  refine List.mem_flatMap.2 ⟨p, ?_, hx⟩
  rw [List.mem_range']
  exact ⟨p - a, by omega, by omega⟩

/-- A record of the trace's slice `[a, b)` is the record of a slot in `[a P, b P)`. -/
theorem traceSlice_slot (g : OnlineGeom) (run : BatchRun) (hE : 0 < g.unitEntries)
    {a b : Nat} {x : Rec} (h : x ∈ traceSlice (traceOf g run) a b) :
    ∃ i, a * (g.unitEntries * g.unitsPerPrefix) ≤ i ∧
      i < b * (g.unitEntries * g.unitsPerPrefix) ∧ slotRec run i = some x := by
  obtain ⟨p, hp1, hp2, hx⟩ := traceSlice_mem h
  change x ∈ DirectMasks.records ((((stateAt g run run.ops.length).frozen.drop
    (p * g.unitsPerPrefix)).take g.unitsPerPrefix)) at hx
  unfold DirectMasks.records at hx
  obtain ⟨U, hU, hxU⟩ := List.mem_flatMap.1 hx
  obtain ⟨q, hq, e⟩ := List.getElem_of_mem hU
  simp only [List.length_take, List.length_drop] at hq
  rw [List.getElem_take, List.getElem_drop] at e
  have hP := prov_stateAt g run hE run.ops.length (le_refl _)
  have hu : p * g.unitsPerPrefix + q < (stateAt g run run.ops.length).frozen.length := by omega
  have hmem : some x ∈ (stateAt g run run.ops.length).frozen[p * g.unitsPerPrefix + q] := by
    rw [e]
    unfold Bucket.recs at hxU
    exact (List.mem_filterMap.1 hxU).elim fun y hy => by
      obtain ⟨hy1, hy2⟩ := hy
      simp only [id] at hy2
      rw [← hy2]; exact hy1
  obtain ⟨i, h1, h2, h3⟩ := hP.frozen _ hu x hmem
  have hq' : q < g.unitsPerPrefix := by omega
  refine ⟨i, ?_, ?_, h3⟩
  · have : a * g.unitsPerPrefix ≤ p * g.unitsPerPrefix + q :=
      (Nat.mul_le_mul_right _ hp1).trans (Nat.le_add_right _ _)
    calc a * (g.unitEntries * g.unitsPerPrefix) = a * g.unitsPerPrefix * g.unitEntries := by ring
      _ ≤ (p * g.unitsPerPrefix + q) * g.unitEntries := Nat.mul_le_mul_right _ this
      _ ≤ i := h1
  · have : p * g.unitsPerPrefix + q + 1 ≤ b * g.unitsPerPrefix := by
      have := Nat.mul_le_mul_right g.unitsPerPrefix (show p + 1 ≤ b by omega)
      rw [Nat.succ_mul] at this
      omega
    calc i < (p * g.unitsPerPrefix + q + 1) * g.unitEntries := h2
      _ ≤ b * g.unitsPerPrefix * g.unitEntries := Nat.mul_le_mul_right _ this
      _ = b * (g.unitEntries * g.unitsPerPrefix) := by ring

/-- A record of a final frozen unit of prefix `[a, b)` lies in the trace's slice. -/
theorem traceSlice_of_unit (g : OnlineGeom) (run : BatchRun) {a b u : Nat} {x : Rec}
    (hu : u < (stateAt g run run.ops.length).frozen.length)
    (h1 : a * g.unitsPerPrefix ≤ u) (h2 : u < b * g.unitsPerPrefix)
    (hx : some x ∈ (stateAt g run run.ops.length).frozen[u]) :
    x ∈ traceSlice (traceOf g run) a b := by
  have hr : 0 < g.unitsPerPrefix := by
    rcases Nat.eq_zero_or_pos g.unitsPerPrefix with h | h
    · rw [h] at h2; omega
    · exact h
  have hp1 : a ≤ u / g.unitsPerPrefix := (Nat.le_div_iff_mul_le hr).2 h1
  have hp2 : u / g.unitsPerPrefix < b := (Nat.div_lt_iff_lt_mul hr).2 h2
  refine mem_traceSlice hp1 hp2 ?_
  change x ∈ DirectMasks.records ((((stateAt g run run.ops.length).frozen.drop
    (u / g.unitsPerPrefix * g.unitsPerPrefix)).take g.unitsPerPrefix))
  unfold DirectMasks.records
  have hdm := Nat.div_add_mod u g.unitsPerPrefix
  have hq : u % g.unitsPerPrefix < g.unitsPerPrefix := Nat.mod_lt _ hr
  refine List.mem_flatMap.2 ⟨(stateAt g run run.ops.length).frozen[u], ?_, ?_⟩
  · apply List.mem_iff_getElem.2
    refine ⟨u % g.unitsPerPrefix, ?_, ?_⟩
    · simp only [List.length_take, List.length_drop]
      have : u / g.unitsPerPrefix * g.unitsPerPrefix + u % g.unitsPerPrefix = u := by
        rw [Nat.mul_comm]; exact hdm
      omega
    · rw [List.getElem_take, List.getElem_drop]
      congr 1
      rw [Nat.mul_comm]; exact hdm
  · unfold Bucket.recs
    exact List.mem_filterMap.2 ⟨some x, hx, rfl⟩

end RebuildBound.AdaptiveFlagSoundProof
