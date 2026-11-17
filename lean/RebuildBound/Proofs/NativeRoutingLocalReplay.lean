import RebuildBound.Spec.NativeRouting.LocalReplay
import RebuildBound.Proofs.NativeRoutingLocalTable

namespace RebuildBound.NativeRoutingLocalReplayProof
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual NativeRoutingLocalTable NativeRoutingLocalReplay
open NativeRoutingLocalTableProof ReadTree

lemma reads_bind {Q α β : Type} (tape : Q → Word64) (tree : ReadTree Q α)
    (next : α → ReadTree Q β) :
    reads tape (bind tree next) = reads tape tree ++ reads tape (next (evaluate tape tree)) := by
  induction tree with
  | done result => rfl
  | read query resume ih => simp only [NativeRoutingLocalTable.bind, reads, evaluate, ih, List.cons_append]

lemma evaluate_sequence {Q α : Type} (tape : Q → Word64) (programs : List (ReadTree Q α)) :
    evaluate tape (sequence programs) = programs.map (evaluate tape) := by
  induction programs with
  | nil => rfl
  | cons program programs ih => simp only [NativeRoutingLocalReplay.sequence, evaluate_bind, evaluate, ih, List.map_cons]

lemma reads_sequence {Q α : Type} (tape : Q → Word64) (programs : List (ReadTree Q α)) :
    reads tape (sequence programs) = programs.flatMap (reads tape) := by
  induction programs with
  | nil => rfl
  | cons program programs ih => simp only [NativeRoutingLocalReplay.sequence, reads_bind, reads, ih, List.append_nil, List.flatMap_cons]

lemma evaluate_tables (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (coordinates : List (Nat × Nat)) (tape : IdealKey.Tape) :
    evaluate tape (tablesProgram cfg sh g run coordinates) =
      coordinates.map fun c => table cfg sh (traceOf g run) (IdealHierarchy.words tape) c.1 c.2 := by
  simp only [tablesProgram, evaluate_sequence, List.map_map, Function.comp_def, table_evaluate]

lemma real_tables (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (S : Schedule) (words : Words) (t i : Nat) :
    realFromTables cfg g run S
      ((slotSchedule (widths run) S t).tables.map fun c => table cfg sh (traceOf g run) words c.1 c.2) t i =
      isReal cfg sh g run S words t i := by
  simp only [realFromTables, OnlineBatch.isReal, ← List.map_take, List.all_map, OnlineBatch.tableKeys, Function.comp_def]
  rfl

lemma entry_evaluate (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (S : Schedule) (tape : IdealKey.Tape) (t i : Nat) :
    evaluate tape (entryProgram cfg g run S
      ((slotSchedule (widths run) S t).tables.map fun c =>
        table cfg sh (traceOf g run) (IdealHierarchy.words tape) c.1 c.2) t i) =
      touched cfg sh g run S (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) t i := by
  unfold entryProgram OnlineBatch.touched
  cases hs : (slots run)[t]? with
  | none => rfl
  | some slot =>
    cases hc : (slotSchedule (widths run) S t).tables[i]? with
    | none => rfl
    | some coordinate =>
      simp only [real_tables]
      by_cases hp : slot.probes = true
      · simp [hp, evaluate]
        split <;> rfl
      · simp [hp, evaluate]

lemma lane_evaluate (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (S : Schedule) (tape : IdealKey.Tape) (t m : Nat) :
    evaluate tape (laneProgram cfg sh g run S t m) =
      fun i : Fin m => touched cfg sh g run S (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) t i.val := by
  unfold laneProgram
  cases hs : (slots run)[t]? with
  | none => simp [evaluate, OnlineBatch.touched, hs]
  | some slot =>
    by_cases hp : slot.probes = true
    · simp only [hp, ↓reduceIte, evaluate_bind, evaluate_tables, evaluate_sequence,
        List.map_map, Function.comp_def, entry_evaluate, evaluate]
      funext i
      simp [List.getD_eq_getElem?_getD, i.isLt]
    · funext i
      simp only [hp, Bool.false_eq_true, ↓reduceIte, evaluate, OnlineBatch.touched, hs]
      cases hc : (slotSchedule (widths run) S t).tables[i.val]? <;> simp [hp]

lemma tables_reads (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (coordinates : List (Nat × Nat)) (tape : IdealKey.Tape) :
    (reads tape (tablesProgram cfg sh g run coordinates)).map Prod.fst =
      coordinates.flatMap fun c =>
        (reads tape (tableProgram cfg sh (traceOf g run) c.1 c.2)).map Prod.fst := by
  simp only [tablesProgram, reads_sequence, List.flatMap_map, List.map_flatMap]

lemma entry_reads (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (S : Schedule) (tape : IdealKey.Tape) (t i : Nat) (slot : OnlineBatch.Slot)
    (hs : (slots run)[t]? = some slot) (hp : slot.probes = true) :
    (reads tape (entryProgram cfg g run S
      ((slotSchedule (widths run) S t).tables.map fun c =>
        table cfg sh (traceOf g run) (IdealHierarchy.words tape) c.1 c.2) t i)).map Prod.fst =
      (((slotSchedule (widths run) S t).tables[i]?).map fun c =>
        if isReal cfg sh g run S (IdealHierarchy.words tape) t i then
          Sum.inl (familyOf cfg c.1 c.2, slot.record.key) else Sum.inr (t, i)).toList := by
  simp only [entryProgram, hs]
  cases hc : (slotSchedule (widths run) S t).tables[i]? with
  | none => rfl
  | some coordinate => simp only [hp, ↓reduceIte, real_tables, reads, List.map_cons,
      List.map_nil, Option.map_some, Option.toList_some]

lemma lane_reads (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (S : Schedule) (tape : IdealKey.Tape) (t m : Nat) :
    (reads tape (laneProgram cfg sh g run S t m)).map Prod.fst =
      constructionQueries cfg sh g run S tape t ++
        probeQueries cfg sh g run S (IdealHierarchy.words tape) t m := by
  unfold laneProgram constructionQueries probeQueries
  cases hs : (slots run)[t]? with
  | none => rfl
  | some slot =>
    by_cases hp : slot.probes = true
    · simp only [hp, ↓reduceIte, reads_bind, reads, List.append_nil, List.map_append,
        tables_reads, evaluate_tables, reads_sequence, List.flatMap_map, List.map_flatMap]
      rw [List.filterMap_eq_flatMap_toList]
      congr 1
      apply congrArg List.flatten
      apply List.map_congr_left
      intro i hi
      exact entry_reads cfg sh g run S tape t i slot hs hp
    · simp [hp, reads]

lemma issue_evaluate (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) (acc : Acc m) (kind : Kind) (tape : IdealKey.Tape) :
    evaluate tape (issueProgram cfg sh g S a acc kind) =
      issue cfg sh g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) acc kind := by
  simp only [issueProgram, evaluate_bind, evaluate_sequence, List.map_map,
    Function.comp_def, lane_evaluate, evaluate, issue]

lemma stages_evaluate (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) (kinds : List Kind) (acc : Acc m) (tape : IdealKey.Tape) :
    evaluate tape (NativeRoutingLocalReplay.stages cfg sh g S a kinds acc) =
      kinds.foldl (issue cfg sh g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)) acc := by
  induction kinds generalizing acc with
  | nil => rfl
  | cons kind kinds ih => simp only [NativeRoutingLocalReplay.stages, evaluate_bind,
      issue_evaluate, ih, List.foldl_cons]
end RebuildBound.NativeRoutingLocalReplayProof

namespace RebuildBound
open Spec NativeRoutingLocalReplayProof

theorem NativeRoutingLocalReplayLane : Spec.NativeRoutingLocalReplayLane_statement := lane_evaluate

theorem NativeRoutingLocalReplayReads : Spec.NativeRoutingLocalReplayReads_statement := lane_reads

theorem NativeRoutingLocalReplayIssue : Spec.NativeRoutingLocalReplayIssue_statement := issue_evaluate

theorem NativeRoutingLocalReplayEvaluate : Spec.NativeRoutingLocalReplayEvaluate_statement := by
  intro cfg sh g S m a tape
  exact stages_evaluate cfg sh g S a a.shape ([], []) tape
end RebuildBound
