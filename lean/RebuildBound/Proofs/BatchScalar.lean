import RebuildBound.Spec.ObliviousBatch

/-! The scalar model is the batch model without chunks: every operation of
`ofScalar run` is one lane, so slot `t` is operation `t`, the plans are the
schedule itself, and the requester states, traces and views agree. -/

namespace RebuildBound.BatchScalarProof

open Model Model.Hierarchy Model.Online Model.OnlineBatch

theorem chunkStart_ones (n t : Nat) : chunkStart (List.replicate n 1) t = t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, chunkStart, ih]
    split <;> omega

theorem widths_ofScalar (run : OnlineRun) :
    widths (ofScalar run) = List.replicate run.ops.length 1 := by
  simp only [widths, ofScalar, List.map_map]
  rw [List.eq_replicate_iff]
  refine ⟨by simp, ?_⟩
  intro b hb
  simp only [List.mem_map, Function.comp_apply] at hb
  obtain ⟨o, _, rfl⟩ := hb
  cases o <;> rfl

theorem slotSchedule_ofScalar (run : OnlineRun) (S : Schedule) :
    slotSchedule (widths (ofScalar run)) S = S := by
  funext t
  simp only [slotSchedule, widths_ofScalar, chunkStart_ones]

/-- A scalar operation as its one slot. -/
def scalarSlot (oj : Online.Op × Nat) : Slot := ⟨oj.2, 0, oj.1.record, oj.1.probes⟩

theorem flatMap_ofScalar (l : List Online.Op) (n : Nat) :
    ((l.map Op.ofScalar).zipIdx n).flatMap (fun oj =>
        oj.1.lanes.zipIdx.map fun rl => (⟨oj.2, rl.2, rl.1.1, rl.1.2⟩ : Slot)) =
      (l.zipIdx n).map scalarSlot := by
  induction l generalizing n with
  | nil => rfl
  | cons o l ih =>
    simp only [List.map_cons, List.zipIdx_cons, List.flatMap_cons, ih]
    cases o <;> rfl

theorem slots_getElem? (run : OnlineRun) (t : Nat) :
    (slots (ofScalar run))[t]? = run.ops[t]?.map fun o => ⟨t, 0, o.record, o.probes⟩ := by
  simp only [slots, ofScalar, flatMap_ofScalar, List.getElem?_map, List.getElem?_zipIdx,
    Option.map_map]
  cases run.ops[t]? <;> simp [scalarSlot]

theorem stateAt_ofScalar (g : OnlineGeom) (run : OnlineRun) (j : Nat) :
    OnlineBatch.stateAt g (ofScalar run) j = Online.stateAt g run j := by
  simp only [OnlineBatch.stateAt, Online.stateAt, ofScalar, ← List.map_take, List.map_map]
  congr 2
  funext o
  cases o <;> rfl

theorem length_ofScalar (run : OnlineRun) : (ofScalar run).ops.length = run.ops.length := by
  simp [ofScalar]

theorem traceOf_ofScalar (g : OnlineGeom) (run : OnlineRun) :
    OnlineBatch.traceOf g (ofScalar run) = Online.traceOf g run := by
  simp only [OnlineBatch.traceOf, Online.traceOf, length_ofScalar, stateAt_ofScalar]
  rfl

theorem probePattern_ofScalar (run : OnlineRun) :
    OnlineBatch.probePattern (ofScalar run) = Online.probePattern run := by
  funext t
  simp only [OnlineBatch.probePattern, Online.probePattern, slots_getElem?, Option.map_map]
  rfl

theorem duplicate_lane0 (run : BatchRun) (j : Nat) (r : Rec) (b : Bool) :
    duplicate run ⟨j, 0, r, b⟩ = false := by
  simp [duplicate]

theorem denseKeys_ofScalar (cfg : Config) (g : OnlineGeom) (run : OnlineRun) (S : Schedule)
    (t : Nat) (o : Online.Op) (h : run.ops[t]? = some o) :
    OnlineBatch.denseKeys cfg g (ofScalar run) S t = Online.denseKeys cfg g run S t := by
  simp only [OnlineBatch.denseKeys, Online.denseKeys, OnlineBatch.denseRecords, Online.denseRecords, slots_getElem?, h, Option.map_some,
    stateAt_ofScalar, slotSchedule_ofScalar]

theorem tableKeys_ofScalar (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineRun)
    (words : Words) :
    OnlineBatch.tableKeys cfg sh g (ofScalar run) words = Online.tableKeys cfg sh g run words := by
  funext ℓ v
  simp only [OnlineBatch.tableKeys, Online.tableKeys, traceOf_ofScalar]

theorem isReal_ofScalar (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineRun)
    (S : Schedule) (words : Words) (t i : Nat) :
    OnlineBatch.isReal cfg sh g (ofScalar run) S words t i =
      Online.isReal cfg sh g run S words t i := by
  cases h : run.ops[t]? with
  | none =>
    simp only [OnlineBatch.isReal, Online.isReal, slots_getElem?, h, Option.map_none]
  | some o =>
    simp only [OnlineBatch.isReal, Online.isReal, slots_getElem?, h, Option.map_some,
      duplicate_lane0, denseKeys_ofScalar cfg g run S t o h, slotSchedule_ofScalar,
      tableKeys_ofScalar, Bool.not_false, Bool.and_true]

theorem touched_ofScalar (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineRun)
    (S : Schedule) (words : Words) (dummy : Nat → Nat → Nat) (t i : Nat) :
    OnlineBatch.touched cfg sh g (ofScalar run) S words dummy t i =
      Online.touched cfg sh g run S words dummy t i := by
  simp only [OnlineBatch.touched, Online.touched, slots_getElem?, slotSchedule_ofScalar,
    isReal_ofScalar]
  cases run.ops[t]? <;> cases (S t).tables[i]? <;> simp only [Option.map_none, Option.map_some]

end RebuildBound.BatchScalarProof

namespace RebuildBound

open BatchScalarProof

theorem BatchScalar : Spec.BatchScalar_statement := by
  intro cfg sh g run S n m words dummy
  refine ⟨traceOf_ofScalar g run, slotSchedule_ofScalar run S, probePattern_ofScalar run, ?_⟩
  funext t i
  exact touched_ofScalar cfg sh g run S words dummy t i

end RebuildBound
