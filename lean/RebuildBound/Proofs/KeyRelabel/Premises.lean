import RebuildBound.Proofs.KeyRelabel.Hierarchy
import RebuildBound.Proofs.KeyRelabel.Online.Basic
import RebuildBound.Proofs.KeyRelabel.Universe
import RebuildBound.Spec.KeyRelabel

namespace RebuildBound.KeyRelabel
open Spec Model Model.Hierarchy Model.Online

theorem online_run_premises (cfg : Config) (sh : Shapes) (U : Finset LogicalKey)
    (g : OnlineGeom) (run : OnlineRun) (hs : UniverseOnlineRunPremises cfg sh U g run) :
    OnlineRunPremises cfg sh U.card g (onlineRun (compression U) run) := by
  refine ⟨hs.geom, ?_, ?_, ?_, ?_⟩
  · simpa using hs.horizon
  · intro o ho
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
    simpa only [onlineOp_record, slot_record, rec_key] using
      (compression_lt U p.record.key).2 (hs.keys p hp)
  · rw [online_traceOf]
    exact tracePremises_rename (compression U) cfg U U.card _
      (fun k hk => (compression_lt U k).2 hk) hs.trace
  · rw [online_traceOf]
    exact unshPromise_rename (compression U) cfg sh _ hs.unsh

theorem batch_run_premises (cfg : Config) (sh : Shapes) (U : Finset LogicalKey)
    (g : OnlineGeom) (run : OnlineBatch.BatchRun)
    (hs : UniverseBatchRunPremises cfg sh U g run) :
    BatchRunPremises cfg sh U.card g (batchRun (compression U) run) := by
  refine ⟨hs.geom, ?_, ?_, ?_, ?_⟩
  · simpa using hs.horizon
  · intro s hs'
    rw [batch_slots] at hs'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs'
    simpa only [onlineOp_record, slot_record, rec_key] using
      (compression_lt U p.record.key).2 (hs.keys p hp)
  · rw [batch_traceOf]
    exact tracePremises_rename (compression U) cfg U U.card _
      (fun k hk => (compression_lt U k).2 hk) hs.trace
  · rw [batch_traceOf]
    exact unshPromise_rename (compression U) cfg sh _ hs.unsh

/-- All original scalar premises hold after the single fixed compression. -/
theorem online_setting (geo : HierarchyGeometry) (U : Finset LogicalKey) (g : OnlineGeom)
    (run : OnlineRun) (S : Schedule) (n m : Nat)
    (hs : UniverseOnlineSetting geo U g run S n m) :
    OnlineSettingFor geo U.card g (onlineRun (compression U) run) S n m := by
  exact ⟨hs.2.1, by simpa using hs.2.2.1,
    online_run_premises geo.cfg geo.shapes U g run hs.2.2.2.1, hs.2.2.2.2⟩

/-- The same conversion covers effective batch lanes and their duplicate keys. -/
theorem batch_setting (geo : HierarchyGeometry) (U : Finset LogicalKey) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (n m : Nat)
    (hs : UniverseBatchSetting geo U g run S n m) :
    BatchSettingFor geo U.card g (batchRun (compression U) run) S n m := by
  exact ⟨hs.2.1, by simpa using hs.2.2.1,
    batch_run_premises geo.cfg geo.shapes U g run hs.2.2.2.1, hs.2.2.2.2⟩

end RebuildBound.KeyRelabel
