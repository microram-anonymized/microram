import RebuildBound.Spec.Adaptive.Semantics
import RebuildBound.Spec.ProbeCorrectness

/-! Generic selected-record causality and the local flag contract. No concrete configuration or failure budget is imported. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive

/-- **BatchFoundCausal**: the record slot `t` selects depends only on the
initialization, the flag, the operations before its own, its key and probe
bit, and the earlier lanes of its own operation. -/
def BatchFoundCausal_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run run' : OnlineBatch.BatchRun) (S : Schedule)
    (n m : Nat) (words : Words) (dummy : Nat → Nat → Nat) (t : Nat) (s s' : OnlineBatch.Slot),
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg S n m → t < n →
    run'.init = run.init → run'.unsh = run.unsh → run'.ops.take s.op = run.ops.take s.op →
    (OnlineBatch.slots run)[t]? = some s → (OnlineBatch.slots run')[t]? = some s' →
    s'.op = s.op → s'.record.key = s.record.key → s'.probes = s.probes →
    Probe.earlier run' s' = Probe.earlier run s →
    (Probe.batch cfg sh g run' S words dummy t).found =
      (Probe.batch cfg sh g run S words dummy t).found

/-- The engine's flag rule (`NoOlderLiveCopy`) on a batch run, with the
selected records taken under the words `words`: every flagged slot record is a
tombstone of a probing lane whose selected record is absent or a flagged
tombstone. -/
def FlagRule (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineBatch.BatchRun)
    (S : Schedule) (words : Words) : Prop :=
  ∀ t (s : OnlineBatch.Slot), (OnlineBatch.slots run)[t]? = some s → run.unsh s.record = true →
    s.record.tomb = true ∧ s.probes = true ∧
    ∀ f, (Probe.batch cfg sh g run S words (fun _ _ => 0) t).found = some f →
      f.tomb = true ∧ run.unsh f = true

end RebuildBound.Spec
