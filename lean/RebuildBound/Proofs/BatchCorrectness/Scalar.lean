import RebuildBound.Proofs.BatchScalar
import RebuildBound.Spec.Model.Probe

/-! A run without batch chunks has exactly the scalar probe result, including
both the selected record and the complete address list. -/
namespace RebuildBound.BatchCorrectnessProof

open Model Model.Hierarchy Model.Online Model.OnlineBatch
open BatchScalarProof

theorem denseRecords_ofScalar (cfg : Config) (g : OnlineGeom) (run : OnlineRun)
    (S : Schedule) (t : Nat) (o : Online.Op) (h : run.ops[t]? = some o) :
    OnlineBatch.denseRecords cfg g (ofScalar run) S t =
      Online.denseRecords cfg g run S t := by
  simp only [OnlineBatch.denseRecords, Online.denseRecords, slots_getElem?, h,
    Option.map_some, stateAt_ofScalar, slotSchedule_ofScalar]

/-- Every effective batch probe in a scalar run is the scalar probe itself. -/
theorem probe_ofScalar (cfg : Config) (sh : Shapes) (g : OnlineGeom) (run : OnlineRun)
    (S : Schedule) (words : Words) (dummy : Nat → Nat → Nat) (t : Nat) :
    Probe.batch cfg sh g (ofScalar run) S words dummy t =
      Probe.scalar cfg sh g run S words dummy t := by
  simp only [Probe.batch, Probe.scalar, slots_getElem?, slotSchedule_ofScalar,
    traceOf_ofScalar]
  cases h : run.ops[t]? with
  | none => rfl
  | some o =>
    simp only [Option.map_some, Probe.earlier, List.take_zero, List.map_nil]
    rw [denseRecords_ofScalar cfg g run S t o h]
    rfl

end RebuildBound.BatchCorrectnessProof
