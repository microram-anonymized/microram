import RebuildBound.Spec.RequesterCuts
import RebuildBound.Proofs.BatchCorrectness.Requester
import RebuildBound.Proofs.ApiExecution.Construction

/-! Every unit boundary of a cut-safe run is also an operation boundary. At
that point requester history has no uncommitted suffix; frozen-prefix
immutability then transports its exact record semantics to the final run.
No key range, population limit, or successful-execution premise is used. -/
namespace RebuildBound.RequesterCutsProof
open Model Model.Online Model.OnlineBatch Model.RequesterCuts
open BatchFreshProof OnlineCorrectnessProof

/-- An aligned operation cannot step over any subsequent whole-unit cut. -/
theorem next_le_boundary {entries position width cut : Nat}
    (hE : 0 < entries) (hwidth : width ≤ entries - position % entries)
    (hpos : position < cut) (hcut : entries ∣ cut) :
    position + width ≤ cut := by
  have hdiv : position / entries < cut / entries :=
    (Nat.div_lt_iff_lt_mul hE).mpr (by rwa [Nat.div_mul_cancel hcut])
  have hmod := Nat.mod_lt position hE
  have hdecomp := Nat.mod_add_div position entries
  calc
    position + width ≤ position + (entries - position % entries) :=
      Nat.add_le_add_left hwidth _
    _ = (position / entries + 1) * entries := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (position / entries) entries]
      omega
    _ ≤ (cut / entries) * entries := Nat.mul_le_mul_right _ (by omega)
    _ = cut := Nat.div_mul_cancel hcut

/-- Every whole-unit position reached by a safe public shape is a sum of
complete operation widths. This covers zero and the final completed unit. -/
theorem boundary_prefix {entries : Nat} (hE : 0 < entries)
    (widths : List Nat) (position cut : Nat)
    (hfit : WidthsFit entries position widths) (hpos : position ≤ cut)
    (hend : cut ≤ position + widths.sum) (hcut : entries ∣ cut) :
    ∃ j, j ≤ widths.length ∧ position + (widths.take j).sum = cut := by
  induction widths generalizing position with
  | nil => exact ⟨0, by simp, by simpa using Nat.le_antisymm hpos hend⟩
  | cons width widths ih =>
    by_cases heq : position = cut
    · exact ⟨0, by simp, by simpa using heq⟩
    · obtain ⟨hwpos, hwfit, hrest⟩ := hfit
      have hnext := next_le_boundary hE hwfit (by omega) hcut
      obtain ⟨j, hj, he⟩ := ih (position + width) hrest hnext
        (by simpa only [List.sum_cons, Nat.add_assoc] using hend)
      refine ⟨j + 1, by simp only [List.length_cons]; omega, ?_⟩
      simpa only [List.take_succ_cons, List.sum_cons, Nat.add_assoc] using he

/-- A cut-safe run has a completed operation at every final frozen-unit cut. -/
theorem operation_boundary (g : OnlineGeom) (run : BatchRun)
    (hE : 0 < g.unitEntries) (hfit : WidthsFit g.unitEntries 0 (widths run))
    (units : Nat) (hu : units ≤ (stateAt g run run.ops.length).frozen.length) :
    ∃ j, j ≤ run.ops.length ∧ fs run j = units * g.unitEntries := by
  have hI := inv_stateAt g run hE run.ops.length le_rfl
  have hend : units * g.unitEntries ≤ (widths run).sum := by
    have hm := Nat.mul_le_mul_right g.unitEntries hu
    have he : fs run run.ops.length = (widths run).sum := by
      rw [fs, widths, ← List.map_take, List.take_length]
    have hlen := hI.len
    rw [he] at hlen
    omega
  obtain ⟨j, hj, he⟩ := boundary_prefix hE (widths run) 0
    (units * g.unitEntries) hfit (Nat.zero_le _) (by simpa using hend)
    (Nat.dvd_mul_left _ _)
  exact ⟨j, by simpa [widths] using hj, by simpa [fs] using he⟩

/-- A completed operation at a whole-unit position has no current-unit suffix. -/
theorem boundary_state (g : OnlineGeom) (run : BatchRun)
    (hE : 0 < g.unitEntries) {j units : Nat} (hj : j ≤ run.ops.length)
    (hfs : fs run j = units * g.unitEntries) :
    (stateAt g run j).current = [] ∧ (stateAt g run j).frozen.length = units := by
  have hI := inv_stateAt g run hE j hj
  have hmod := congrArg (fun n => n % g.unitEntries) hI.len
  have hc : (stateAt g run j).current.length = 0 := by
    simpa [hfs, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hI.cur] using hmod
  refine ⟨List.eq_nil_of_length_eq_zero hc, ?_⟩
  apply Nat.eq_of_mul_eq_mul_right hE
  simpa [hc, hfs] using hI.len

/-- Public group lengths and physical operation widths have the same cut law. -/
theorem groups_fit_widths {α : Type} {entries : Nat} (hE : 0 < entries)
    (groups : List (PublicApi.Group α)) (position : Nat)
    (hfit : PublicApi.GroupsFit entries position groups) :
    WidthsFit entries position (groups.map fun group => group.lanes.length) := by
  induction groups generalizing position with
  | nil => trivial
  | cons group groups ih =>
    obtain ⟨hpos, hwidth, hrest⟩ := hfit
    refine ⟨hpos, ?_, ih _ hrest⟩
    simpa [PublicApi.unitRemaining, max_eq_right (by omega : 1 ≤ entries)] using hwidth

end RebuildBound.RequesterCutsProof

namespace RebuildBound
open Spec Model Model.Online Model.OnlineBatch Model.RequesterCuts
open RequesterCutsProof BatchFreshProof OnlineCorrectnessProof

theorem RequesterUnitCuts : RequesterUnitCuts_statement := by
  intro g run hE hfit units hu key
  obtain ⟨j, hj, hfs⟩ := operation_boundary g run hE hfit units hu
  obtain ⟨hc, hf⟩ := boundary_state g run hE hj hfs
  rw [frozen_take_prefix (BatchFreshProof.frozen_prefix g run run.ops.length hj le_rfl)
    units (by omega), ← hf, List.take_length]
  have hhistory := BatchCorrectnessProof.requester_history_slots g run j key
  simpa only [hc, Bucket.recs, List.filterMap_nil, List.append_nil, hfs, hf] using hhistory

theorem RequesterTraceSaturatedCuts : RequesterTraceSaturatedCuts_statement := by
  intro g run hE hfit n
  have hbound := Nat.min_le_right (n * g.unitsPerPrefix)
    (stateAt g run run.ops.length).frozen.length
  refine ⟨?_, ?_⟩
  · have hI := inv_stateAt g run hE run.ops.length le_rfl
    have hm := Nat.mul_le_mul_right g.unitEntries hbound
    have he := hI.len
    rw [fs_length] at he
    unfold traceCutSlots
    omega
  · intro key
    have hg := congrArg (List.flatMap Bucket.recs)
      (grouped_prefix (stateAt g run run.ops.length).frozen g.unitsPerPrefix n)
    simp [List.flatMap_assoc, List.range'_eq_map_range] at hg
    change (List.range n).flatMap (fun i => DirectMasks.records ((traceOf g run).units i)) =
      ((stateAt g run run.ops.length).frozen.take (n * g.unitsPerPrefix)).flatMap Bucket.recs at hg
    rw [hg]
    have htake : (stateAt g run run.ops.length).frozen.take (n * g.unitsPerPrefix) =
        (stateAt g run run.ops.length).frozen.take
          (min (n * g.unitsPerPrefix) (stateAt g run run.ops.length).frozen.length) := by
      rw [← List.take_take, List.take_length]
    rw [htake]
    exact RequesterUnitCuts g run hE hfit _ hbound key

/-- Compatibility at cuts that are completely supplied by the run. -/
theorem RequesterTraceCuts : RequesterTraceCuts_statement := by
  intro g run hE hfit n hn key
  simpa only [traceCutSlots, Nat.min_eq_left hn] using
    (RequesterTraceSaturatedCuts g run hE hfit n).2 key

theorem RequesterLoweredFits : RequesterLoweredFits_statement := by
  intro c cfg sh g S init groups hE hfit
  change WidthsFit g.unitEntries 0
    ((ApiExecution.operations c cfg sh g S init [] groups).map fun op => op.lanes.length)
  rw [ApiExecutionProof.operations_widths]
  exact groups_fit_widths hE groups 0 hfit

end RebuildBound
