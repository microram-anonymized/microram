import RebuildBound.Spec.ProbeCorrectness
import RebuildBound.Proofs.OnlineCorrectness.Composition
import RebuildBound.Proofs.OnlineCorrectness.Requester
import RebuildBound.Proofs.OnlineCorrectness.Addresses
import RebuildBound.Proofs.HierarchyHorizonFree
import RebuildBound.Proofs.HierarchyInvariantChunks

/-! A scalar probe returns the latest preceding supplied value and realizes the
existing address view, for every word tape and every valid schedule. -/
namespace RebuildBound.OnlineCorrectnessProof
open Model Model.Hierarchy Model.Online Model.DirectPrefix Spec
open HierarchyInvariantProof OnlineFreshProof

/-- Lookup for either start, with the run agreeing with its initialization mode. -/
theorem correctnessFor_run (geo : HierarchyGeometry)
    (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hD : geo.cfg.topDigit = geo.top.D)
    (N : Nat) (g : OnlineGeom) (run : OnlineRun) (S : Schedule) (n m : Nat)
    (hsetting : OnlineSettingFor geo N g run S n m)
    (hInit : geo.cfg.initialized = false → run.init = []) :
    ∀ (words : Words) (dummy : Nat → Nat → Nat) j o, j < n →
      run.ops[j]? = some o → o.probes = true →
      let result := Probe.scalar geo.cfg geo.shapes g run S words dummy j
      Probe.decode result.found =
          Probe.latestValue o.record.key (run.init ++ (run.ops.take j).map Op.record) ∧
        ∀ i, result.addresses.getD i 0 = touched geo.cfg geo.shapes g run S words dummy j i := by
  intro words dummy j o hj ho hp
  obtain ⟨hN, hn, hR, hP⟩ := hsetting
  have hjlen : j ≤ run.ops.length := (Nat.le_of_lt hj).trans hn
  have hcons := hP.consumed j hj
  have hstate := inv_stateAt g run hR.geom.2 j hjlen
  have hcomplete : ((S j).consumed - geo.cfg.seed 1) * g.unitsPerPrefix ≤
      (stateAt g run j).frozen.length :=
    consumed_frozen hR.geom.1 hR.geom.2 hstate.len hstate.cur hcons.1 hcons.2
  have hpartition : traceSlice (traceOf g run) 0
      (positionUnit geo.cfg ((S j).consumed * geo.cfg.carryPositions 1)) ++
      denseRecords geo.cfg g run S j = requesterRecords (stateAt g run j) := by
    rw [positionUnit_mul F, unitEnd_one]
    simpa [traceSlice, denseRecords, List.append_assoc] using
      requester_partition g run j ((S j).consumed - geo.cfg.seed 1) hjlen hcomplete
  have hhorizon : (S j).consumed * geo.cfg.carryPositions 1 ≤
      geo.cfg.seed 1 * geo.cfg.carryPositions 1 + geo.cfg.horizon :=
    hcons.2.trans (Nat.add_le_add_left (hjlen.trans hR.horizon) _)
  have hcoords : ∀ c ∈ (S j).tables, Published geo.cfg c := hP.coords j hj
  have hscan : ∀ c ∈ (S j).tables, Probe.scan o.record.key
      (table geo.cfg geo.shapes (traceOf g run) words c.1 c.2)
      (bucket geo.cfg c.1 c.2 (jobWord geo.cfg words c.1 c.2 o.record.key)) =
      latest o.record.key (table geo.cfg geo.shapes (traceOf g run) words c.1 c.2).records :=
    fun c hc => plan_scanFor geo F G hD hN hR.trace hR.unsh words (hcoords c hc)
      (coordinate_horizon F (hcoords c hc)
        ((tiles_bounds (hP.tile j hj) c hc).2.2.trans hhorizon)) o.record.key
  refine ⟨?_, scalar_addresses ho hp hscan⟩
  simp only [Probe.scalar, ho, hp, ite_true]
  rw [hierarchy_historyFor geo F G hD hN hR.trace hInit hR.unsh words (dummy j) o.record.key
    (S j).tables ((S j).consumed * geo.cfg.carryPositions 1)
    (Nat.mul_le_mul_right _ hcons.1) (hP.tile j hj) hcoords (hP.oneTop j hj) hhorizon,
    List.append_assoc, hpartition]
  unfold Probe.latestValue
  rw [latest_append, latest_append]
  change Probe.decode ((latest o.record.key (requesterRecords (stateAt g run j))).orElse
    (fun _ => latest o.record.key run.init)) = _
  unfold requesterRecords
  rw [requester_history]

/-- Existing positive-seed interface, as a corollary of the common run proof. -/
theorem correctnessFor (geo : HierarchyGeometry)
    (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hD : geo.cfg.topDigit = geo.top.D) (hsL : 0 < geo.cfg.seed geo.cfg.levels) : OnlineCorrectnessFor geo := by
  intro N g run S n m hsetting
  apply correctnessFor_run geo F G hD N g run S n m hsetting
  intro hInit
  simp [Config.seed, hInit] at hsL

end RebuildBound.OnlineCorrectnessProof
