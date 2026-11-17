import RebuildBound.Spec.ProbeCorrectness
import RebuildBound.Proofs.OnlineCorrectness.Composition
import RebuildBound.Proofs.OnlineCorrectness.Addresses
import RebuildBound.Proofs.BatchCorrectness.Requester

namespace RebuildBound.BatchCorrectnessProof

open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.DirectPrefix Spec
open HierarchyInvariantProof OnlineCorrectnessProof BatchFreshProof

/-- Effective batch answers use the completed operation history plus the
latest matching earlier lane of their own chunk. -/
theorem correctnessFor_run_of_initLength (geo : HierarchyGeometry)
    (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hD : geo.cfg.topDigit = geo.top.D)
    (N : Nat) (g : OnlineGeom) (run : BatchRun) (S : Schedule) (n m : Nat)
    (hInitLen : run.init.length ≤ geo.init.C / 2 * geo.init.T)
    (hn : n ≤ (slots run).length)
    (hR : BatchRunPremises geo.cfg geo.shapes N g run)
    (hS : SchedulePremises geo.cfg S n m)
    (hInit : geo.cfg.initialized = false → run.init = []) :
    ∀ (words : Words) (dummy : Nat → Nat → Nat) t s, t < n →
      (slots run)[t]? = some s → s.probes = true →
      let result := Probe.batch geo.cfg geo.shapes g run S words dummy t
      Probe.decode result.found = Probe.latestValue s.record.key
          (run.init ++ ((slots run).take t).map Slot.record) ∧
        ∀ i, result.addresses.getD i 0 = OnlineBatch.touched geo.cfg geo.shapes g run S words dummy t i := by
  intro words dummy t s ht hs hp
  obtain ⟨o, ho, hl, hslot⟩ := slot_inv run hs
  have hj : s.op ≤ run.ops.length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp ho).1
  have hstart : fs run s.op < n := lt_of_le_of_lt (fs_le run hs) ht
  have hplan : slotSchedule (widths run) S t = S (fs run s.op) := by
    simp only [slotSchedule, chunkStart_slot run hs]
  have hcons := hS.consumed (fs run s.op) hstart
  have hinv := inv_stateAt g run hR.geom.2 s.op hj
  have hfrozen := consumed_frozen hR.geom.1 hR.geom.2 hinv.len hinv.cur hcons.1 hcons.2
  have hseed : geo.cfg.seed 1 * geo.cfg.carryPositions 1 ≤
      (S (fs run s.op)).consumed * geo.cfg.carryPositions 1 :=
    Nat.mul_le_mul_right _ hcons.1
  have hhorizon : (S (fs run s.op)).consumed * geo.cfg.carryPositions 1 ≤
      geo.cfg.seed 1 * geo.cfg.carryPositions 1 + geo.cfg.horizon := by
    have hbound := hR.horizon
    have hle := fs_le run hs
    unfold pos at hcons
    omega
  have hcoords := hS.coords (fs run s.op) hstart
  have htile := hS.tile (fs run s.op) hstart
  refine ⟨?_, ?_⟩
  · have hstored :
        traceSlice (OnlineBatch.traceOf g run) 0 ((S (fs run s.op)).consumed - geo.cfg.seed 1) ++
          OnlineBatch.denseRecords geo.cfg g run S t =
            requesterRecords (OnlineBatch.stateAt g run s.op) := by
      simpa only [traceSlice, Nat.sub_zero, OnlineBatch.denseRecords, hs, hplan,
        List.append_assoc] using
        requester_partition g run s.op ((S (fs run s.op)).consumed - geo.cfg.seed 1) hj hfrozen
    have hH := hierarchy_historyFor_of_initLength geo F G hD hInitLen hR.trace hInit hR.unsh words (dummy t) s.record.key
      (S (fs run s.op)).tables ((S (fs run s.op)).consumed * geo.cfg.carryPositions 1)
      hseed htile hcoords (hS.oneTop (fs run s.op) hstart) hhorizon
      (OnlineBatch.denseRecords geo.cfg g run S t ++ Probe.earlier run s)
    rw [positionUnit_mul F, unitEnd_one] at hH
    have hcombine :
        ((OnlineBatch.traceOf g run).init ++
          traceSlice (OnlineBatch.traceOf g run) 0 ((S (fs run s.op)).consumed - geo.cfg.seed 1)) ++
          (OnlineBatch.denseRecords geo.cfg g run S t ++ Probe.earlier run s) =
        (run.init ++ requesterRecords (OnlineBatch.stateAt g run s.op)) ++ Probe.earlier run s := by
      rw [← hstored]
      simp only [OnlineBatch.traceOf, List.append_assoc]
    rw [hcombine] at hH
    have hrhist := requester_history_slots g run s.op s.record.key
    change latest s.record.key (requesterRecords (OnlineBatch.stateAt g run s.op)) = _ at hrhist
    have href : latest s.record.key
        ((run.init ++ requesterRecords (OnlineBatch.stateAt g run s.op)) ++ Probe.earlier run s) =
        latest s.record.key (run.init ++ ((slots run).take t).map Slot.record) := by
      rw [latest_append s.record.key _ (Probe.earlier run s),
        latest_append s.record.key run.init (requesterRecords (OnlineBatch.stateAt g run s.op)),
        hrhist,
        ← latest_append s.record.key run.init (((slots run).take (fs run s.op)).map Slot.record)]
      exact forwarding_history_init run.init run s.record.key hs
    simp only [Probe.batch, hs, hp, ite_true]
    rw [hplan, ← latest_append]
    exact hH.trans (congrArg Probe.decode href)
  · intro i
    apply batch_addresses hs hp (i := i)
    intro c hc
    rw [hplan] at hc
    exact plan_scanFor_of_initLength geo F G hD hInitLen hR.trace hR.unsh words (hcoords c hc)
      (coordinate_horizon F (hcoords c hc) ((OnlineFreshProof.tiles_bounds htile c hc).2.2.trans
        hhorizon)) s.record.key

/-- Compatibility interface deriving initialization size from the old key bound. -/
theorem correctnessFor_run (geo : HierarchyGeometry)
    (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hD : geo.cfg.topDigit = geo.top.D)
    (N : Nat) (g : OnlineGeom) (run : BatchRun) (S : Schedule) (n m : Nat)
    (hsetting : BatchSettingFor geo N g run S n m)
    (hInit : geo.cfg.initialized = false → run.init = []) :
    ∀ (words : Words) (dummy : Nat → Nat → Nat) t s, t < n →
      (slots run)[t]? = some s → s.probes = true →
      let result := Probe.batch geo.cfg geo.shapes g run S words dummy t
      Probe.decode result.found = Probe.latestValue s.record.key
          (run.init ++ ((slots run).take t).map Slot.record) ∧
        ∀ i, result.addresses.getD i 0 = OnlineBatch.touched geo.cfg geo.shapes g run S words dummy t i := by
  obtain ⟨hN, hn, hR, hS⟩ := hsetting
  exact correctnessFor_run_of_initLength geo F G hD N g run S n m
    (init_lenFor geo G hR.trace hN) hn hR hS hInit

/-- Existing positive-seed interface, as a corollary of the common run proof. -/
theorem correctnessFor (geo : HierarchyGeometry)
    (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hD : geo.cfg.topDigit = geo.top.D) (hsL : 0 < geo.cfg.seed geo.cfg.levels) : BatchCorrectnessFor geo := by
  intro N g run S n m hsetting
  apply correctnessFor_run geo F G hD N g run S n m hsetting
  intro hInit
  simp [Config.seed, hInit] at hsL

end RebuildBound.BatchCorrectnessProof
