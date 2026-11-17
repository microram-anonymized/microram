import RebuildBound.Spec.ObliviousBatch
import RebuildBound.Spec.Model.Probe

/-!
# Deterministic probe correctness

The supplied records define the reference history. Each probing operation
returns the preceding history's latest value, with tombstones interpreted as
absence. The actual bucket scans also realize the online model's address view.
These statements quantify over arbitrary routing and dummy words and do not
assume capacity success: the reference continuations retain overflow records.
Operation semantics and correspondence to bounded native execution are separate.
-/
namespace RebuildBound.Spec

open Model Model.Hierarchy Model.Online

/-- Scalar answers and addresses at a configuration, under the existing setting. -/
def OnlineCorrectnessFor (geo : HierarchyGeometry) : Prop :=
  ∀ N g run S n m, OnlineSettingFor geo N g run S n m →
    ∀ (words : Words) (dummy : Nat → Nat → Nat) j o, j < n →
      run.ops[j]? = some o → o.probes = true →
      let result := Probe.scalar geo.cfg geo.shapes g run S words dummy j
      Probe.decode result.found =
          Probe.latestValue o.record.key (run.init ++ (run.ops.take j).map Op.record) ∧
        ∀ i, result.addresses.getD i 0 =
          touched geo.cfg geo.shapes g run S words dummy j i

/-- Effective batch-lane answers include earlier lanes of the current chunk. -/
def BatchCorrectnessFor (geo : HierarchyGeometry) : Prop :=
  ∀ N g run S n m, BatchSettingFor geo N g run S n m →
    ∀ (words : Words) (dummy : Nat → Nat → Nat) t s, t < n →
      (OnlineBatch.slots run)[t]? = some s → s.probes = true →
      let result := Probe.batch geo.cfg geo.shapes g run S words dummy t
      Probe.decode result.found = Probe.latestValue s.record.key
          (run.init ++ ((OnlineBatch.slots run).take t).map OnlineBatch.Slot.record) ∧
        ∀ i, result.addresses.getD i 0 =
          OnlineBatch.touched geo.cfg geo.shapes g run S words dummy t i

end RebuildBound.Spec
