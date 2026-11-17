import RebuildBound.Spec.AdaptiveSteps
import RebuildBound.Proofs.BatchFresh.Requester
import RebuildBound.Proofs.OnlineCorrectness.Composition

/-!
# AdaptiveRowCausality: rows and complete units are fixed by the operations issued

**TraceUnitsPrefix.** Frozen units only grow (`frozen_prefix`). After the
first `j` operations the requester holds `|frozen| · E + |cur| = fs j` with
`|cur| < E` (`inv_stateAt`), and `cp_1 = E · r`, so `(i + 1) · cp_1 ≤ fs j`
gives `(i + 1) · r ≤ |frozen|` (`consumed_frozen` with seed `0`): unit `i` is
complete at operation `j`, and the same on the prefix run and the whole run.

**RowCausality.** A slot `t` of the prefix run of `j` operations belongs to an
operation `s.op < j`, so the slot, its operation's first slot `J = fs s.op`,
its plan `S J`, its duplicate flag and its dense prefix (the requester state at
`s.op`) are the same on both runs. Every plan table `c` has
`time c · cp_1 = (window c).2 ≤ consumed · cp_1 ≤ s_1 · cp_1 + J` (the tiling
and `SchedulePremises.consumed`), so every unit `u` with `s_1 + u + 1 ≤ time c`
has `(u + 1) · cp_1 ≤ J ≤ fs j`: it is the same on both traces
(TraceUnitsPrefix), and TracePrefix gives the same table.
-/

namespace RebuildBound.AdaptiveRowCausalityProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.OnlineBatch RebuildBound.Spec
open RebuildBound.Model.Online (OnlineGeom pos window)
open RebuildBound.BatchFreshProof
open RebuildBound.OnlineFreshProof (tiles_bounds window_snd)
open RebuildBound.OnlineCorrectnessProof (consumed_frozen time_cp)

/-- The run of the first `j` operations. -/
abbrev prefixRun (run : BatchRun) (j : Nat) : BatchRun := ⟨run.ops.take j, run.init, run.unsh⟩

theorem stateAt_prefix (g : OnlineGeom) (run : BatchRun) {j k : Nat} (h : k ≤ j) :
    stateAt g (prefixRun run j) k = stateAt g run k := by
  simp only [stateAt, List.take_take, Nat.min_eq_left h]

theorem all_congr_mem {α : Type} : ∀ {L : List α} {f f' : α → Bool},
    (∀ x ∈ L, f x = f' x) → L.all f = L.all f'
  | [], _, _, _ => rfl
  | a :: L, f, f', h => by
    rw [List.all_cons, List.all_cons, h a (List.mem_cons_self ..),
      all_congr_mem (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem traceUnitsPrefix : TraceUnitsPrefix_statement := by
  intro cfg g run j i hgeom hE hle
  rcases Nat.le_total run.ops.length j with hj | hj
  · have e : run.ops.take j = run.ops := List.take_of_length_le hj
    simp only [e]
  · have hlen : (run.ops.take j).length = j := by simp [hj]
    have hinv := inv_stateAt g run hE j hj
    have hfro : (i + 1) * g.unitsPerPrefix ≤ (stateAt g run j).frozen.length := by
      have := consumed_frozen (seed := 0) (c := i + 1) hgeom hE hinv.len hinv.cur
        (Nat.zero_le _) (by simpa [fs] using hle)
      simpa using this
    obtain ⟨tail, htail⟩ := frozen_prefix g run (j := j) run.ops.length hj le_rfl
    show (((stateAt g (prefixRun run j) (run.ops.take j).length).frozen.drop
        (i * g.unitsPerPrefix)).take g.unitsPerPrefix) =
      (((stateAt g run run.ops.length).frozen.drop (i * g.unitsPerPrefix)).take g.unitsPerPrefix)
    rw [hlen, stateAt_prefix g run le_rfl, ← htail,
      List.drop_append_of_le_length (by rw [Nat.add_mul] at hfro; omega),
      List.take_append_of_le_length (by rw [List.length_drop]; rw [Nat.add_mul] at hfro; omega)]

theorem rowCausality (hTP : TracePrefix_statement) (hTU : TraceUnitsPrefix_statement) :
    RowCausality_statement := by
  intro cfg sh g run S n m j words dummy t i hgeom hE hS htn htj
  -- The slot is the same on both runs.
  have hslots : slots run = slots (prefixRun run j) ++
      slotsL (run.ops.drop j) (0 + (run.ops.take j).length) := by
    have e := slotsL_append (run.ops.take j) (run.ops.drop j) 0
    rw [List.take_append_drop] at e
    exact e
  obtain ⟨s, hs⟩ : ∃ s, (slots (prefixRun run j))[t]? = some s :=
    ⟨_, List.getElem?_eq_getElem htj⟩
  have hs' : (slots run)[t]? = some s := by
    rw [hslots, List.getElem?_append_left htj, hs]
  obtain ⟨o, ho, -, -⟩ := slot_inv _ hs
  have hop : s.op < j := by
    have := (List.getElem?_eq_some_iff.1 ho).1
    simp only [List.length_take] at this
    omega
  -- The plan is the same.
  have hfs : fs (prefixRun run j) s.op = fs run s.op := by
    simp only [fs, widths, List.map_take, List.take_take, Nat.min_eq_left hop.le]
  have hplan : slotSchedule (widths (prefixRun run j)) S t = slotSchedule (widths run) S t := by
    simp only [slotSchedule, chunkStart_slot _ hs, chunkStart_slot _ hs', hfs]
  have hplan' : slotSchedule (widths run) S t = S (fs run s.op) := by
    simp only [slotSchedule, chunkStart_slot _ hs']
  -- The duplicate flag and the dense prefix are the same.
  have hdup : duplicate (prefixRun run j) s = duplicate run s := by
    have e : (run.ops.take j)[s.op]? = run.ops[s.op]? := by simp [hop]
    simp only [duplicate, e]
  have hdense : denseKeys cfg g (prefixRun run j) S t = denseKeys cfg g run S t := by
    simp only [denseKeys, denseRecords, hs, hs', hplan, stateAt_prefix g run hop.le]
  -- Every plan table is the same.
  have hJ : fs run s.op < n := lt_of_le_of_lt (fs_le run hs') htn
  have htab : ∀ c ∈ (S (fs run s.op)).tables,
      tableKeys cfg sh g (prefixRun run j) words c.1 c.2 = tableKeys cfg sh g run words c.1 c.2 := by
    intro c hc
    have hunits : ∀ u, cfg.seed 1 + u + 1 ≤ time cfg c.1 c.2 →
        (traceOf g (prefixRun run j)).units u = (traceOf g run).units u := by
      intro u hu
      apply hTU cfg g run j u hgeom hE
      have hwe : (window cfg c.1 c.2).2 ≤ (S (fs run s.op)).consumed * cfg.carryPositions 1 :=
        (tiles_bounds (hS.tile _ hJ) c hc).2.2
      rw [window_snd, ← time_cp] at hwe
      have hcons := (hS.consumed _ hJ).2
      unfold pos at hcons
      have hmono : fs run s.op ≤ fs run j := fs_mono run hop.le
      have h1 : (u + 1) * cfg.carryPositions 1 + cfg.seed 1 * cfg.carryPositions 1 ≤
          time cfg c.1 c.2 * cfg.carryPositions 1 := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      show _ ≤ fs run j
      omega
    simp only [tableKeys, (hTP cfg sh (traceOf g (prefixRun run j)) (traceOf g run) words
      (time cfg c.1 c.2) rfl rfl hunits).1 c.1 c.2 le_rfl]
  have hreal : isReal cfg sh g (prefixRun run j) S words t i = isReal cfg sh g run S words t i := by
    simp only [isReal, hs, hs', hdup, hdense, hplan]
    rw [all_congr_mem (L := ((slotSchedule (widths run) S t).tables.take i)) (fun c hc => by
      rw [htab c (by rw [← hplan']; exact List.mem_of_mem_take hc)])]
  unfold touched
  rw [hs, hs', hplan, hreal]

end RebuildBound.AdaptiveRowCausalityProof

namespace RebuildBound

theorem RowCausalityStep : Spec.RowCausalityStep_statement :=
  fun hTP hTU => AdaptiveRowCausalityProof.rowCausality hTP hTU

theorem TraceUnitsPrefix : Spec.TraceUnitsPrefix_statement :=
  AdaptiveRowCausalityProof.traceUnitsPrefix

end RebuildBound
