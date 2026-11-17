import RebuildBound.Spec.NativeRouting.LocalTable

/-! Sparse logical-routing replay. Each newly issued probing lane reconstructs
only its scheduled tables, then reads one real or dummy coordinate for each
present public entry. Blind lanes read nothing. The reader chooses requests
from earlier returned rows and never consults normalization values or global
capacity/event diagnostics. Completed-input stability, local native diagnostics,
uniform read budgets and unconditional marginal laws are separate obligations. -/
namespace RebuildBound.Spec.NativeRoutingLocalReplay
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive
open NativeRoutingActual NativeRoutingLocalTable

/-- Sequence a finite list of readers in order, retaining their results. -/
def sequence {Q α : Type} : List (ReadTree Q α) → ReadTree Q (List α)
  | [] => .done []
  | program :: programs => bind program fun result =>
      bind (sequence programs) fun results => .done (result :: results)

/-- Reconstruct just the tables of the current public plan. -/
def tablesProgram (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : BatchRun) (coordinates : List (Nat × Nat)) : ReadTree IdealKey.Coord (List Output) :=
  sequence (coordinates.map fun c => tableProgram cfg sh (traceOf g run) c.1 c.2)

/-- The exact found state before an entry, computed from the returned tables.
The current plan order, requester prefix and same-frame duplicates are retained. -/
def realFromTables (cfg : Config) (g : OnlineGeom) (run : BatchRun) (S : Schedule)
    (tables : List Output) (t i : Nat) : Bool :=
  match (slots run)[t]? with
  | none => false
  | some slot =>
      slot.probes && !duplicate run slot && !(denseKeys cfg g run S t).contains slot.record.key &&
        (tables.take i).all fun output => !(output.records.map Rec.key).contains slot.record.key

/-- One actual address read. Missing entries and blind lanes have no read. -/
def entryProgram (cfg : Config) (g : OnlineGeom) (run : BatchRun) (S : Schedule)
    (tables : List Output) (t i : Nat) : ReadTree IdealKey.Coord Nat :=
  match (slots run)[t]?, (slotSchedule (widths run) S t).tables[i]? with
  | some slot, some coordinate =>
      if slot.probes then
        let query := if realFromTables cfg g run S tables t i then
          Sum.inl (familyOf cfg coordinate.1 coordinate.2, slot.record.key)
          else Sum.inr (t, i)
        .read query fun word => .done (bucket cfg coordinate.1 coordinate.2 word.val)
      else .done 0
  | _, _ => .done 0

/-- One row of the current operation. A blind lane skips table reconstruction
as well as real/dummy probing. Reconstructing completed tables repeatedly is
permitted; family support must be deduplicated in the pair-count argument. -/
def laneProgram (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (S : Schedule) (t m : Nat) : ReadTree IdealKey.Coord (Fin m → Nat) :=
  match (slots run)[t]? with
  | none => .done (fun _ => 0)
  | some slot => if slot.probes then
      bind (tablesProgram cfg sh g run (slotSchedule (widths run) S t).tables) fun tables =>
        bind (sequence ((List.range m).map fun i => entryProgram cfg g run S tables t i))
          fun values => .done (fun i => values.getD i.val 0)
    else .done (fun _ => 0)

/-- Issue the client-chosen records before gathering their address rows. -/
def issueProgram (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) (acc : Acc m) (kind : Kind) : ReadTree IdealKey.Coord (Acc m) :=
  let ops := acc.1 ++ [kind.op (a.client acc.2)]
  let run : BatchRun := ⟨ops, a.init, a.unsh⟩
  bind (sequence ((List.range kind.width).map fun lane =>
    laneProgram cfg sh g run S (acc.2.length + lane) m)) fun rows =>
      .done (ops, acc.2 ++ rows)

/-- Every client decision depends only on earlier returned routing rows. -/
def stages (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) : List Kind → Acc m → ReadTree IdealKey.Coord (Acc m)
  | [], acc => .done acc
  | kind :: rest, acc => bind (issueProgram cfg sh g S a acc kind) fun next =>
      stages cfg sh g S a rest next

def readProgram (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) : ReadTree IdealKey.Coord (Acc m) :=
  stages cfg sh g S a a.shape ([], [])

/-- Exactly the real/dummy coordinates of the lane's address reads, after its
tables have been reconstructed. Missing public entries contribute nothing. -/
def probeQueries (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (S : Schedule) (words : Words) (t m : Nat) : List IdealKey.Coord :=
  match (slots run)[t]? with
  | none => []
  | some slot => if slot.probes then
      (List.range m).filterMap fun i =>
        ((slotSchedule (widths run) S t).tables[i]?).map fun coordinate =>
          if isReal cfg sh g run S words t i then
            Sum.inl (familyOf cfg coordinate.1 coordinate.2, slot.record.key)
          else Sum.inr (t, i)
    else []

/-- The only construction reads of a lane are the sparse programs for its
current scheduled tables. No configured horizon or potential job list occurs. -/
def constructionQueries (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun)
    (S : Schedule) (tape : IdealKey.Tape) (t : Nat) : List IdealKey.Coord :=
  match (slots run)[t]? with
  | none => []
  | some slot => if slot.probes then
      (slotSchedule (widths run) S t).tables.flatMap fun coordinate =>
        (ReadTree.reads tape (tableProgram cfg sh (traceOf g run) coordinate.1 coordinate.2)).map Prod.fst
    else []
end RebuildBound.Spec.NativeRoutingLocalReplay

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive
open NativeRoutingActual

/-- Every sparse lane returns exactly the existing address row on every tape,
including overflow continuations and arbitrary repeated keys. -/
def NativeRoutingLocalReplayLane_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun) (S : Schedule)
    (tape : IdealKey.Tape) (t m : Nat),
    ReadTree.evaluate tape (NativeRoutingLocalReplay.laneProgram cfg sh g run S t m) =
      fun i : Fin m => touched cfg sh g run S (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) t i.val

/-- The complete lane read list consists exactly of current-table construction
reads followed by its selected real/dummy probes. Blind lanes have neither. -/
def NativeRoutingLocalReplayReads_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : BatchRun) (S : Schedule)
    (tape : IdealKey.Tape) (t m : Nat),
    (ReadTree.reads tape (NativeRoutingLocalReplay.laneProgram cfg sh g run S t m)).map Prod.fst =
      NativeRoutingLocalReplay.constructionQueries cfg sh g run S tape t ++
        NativeRoutingLocalReplay.probeQueries cfg sh g run S (IdealHierarchy.words tape) t m

/-- Each operation agrees at its next adaptive client decision boundary. -/
def NativeRoutingLocalReplayIssue_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (a : AdaptiveRun m) (acc : Acc m) (kind : Kind) (tape : IdealKey.Tape),
    ReadTree.evaluate tape (NativeRoutingLocalReplay.issueProgram cfg sh g S a acc kind) =
      issue cfg sh g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) acc kind

/-- Full adaptive reference replay has no Cartesian reader or global memo.
This is a deterministic identity, not a native marginal/coupling theorem. -/
def NativeRoutingLocalReplayEvaluate_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (a : AdaptiveRun m) (tape : IdealKey.Tape),
    ReadTree.evaluate tape (NativeRoutingLocalReplay.readProgram cfg sh g S a) =
      interact cfg sh g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
end RebuildBound.Spec
