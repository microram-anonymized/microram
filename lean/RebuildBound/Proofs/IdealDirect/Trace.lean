import RebuildBound.Proofs.AdaptiveRequester

/-! Requester unit shape and load hold without initialization, key ranges,
capacity, flag soundness, or successful earlier rebuilds. -/
namespace RebuildBound.IdealDirectProof
open Model Model.Hierarchy Model.Online Spec

/-- Frozen requester units are unique and have their public record load. -/
theorem trace_units (cfg : Config) (g : OnlineGeom) (run : OnlineBatch.BatchRun)
    (hgeom : g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1)
    (hE : 0 < g.unitEntries) :
    (∀ i, ∀ u ∈ (OnlineBatch.traceOf g run).units i, (u.recs.map Rec.key).Nodup) ∧
    (∀ i, (DirectMasks.records ((OnlineBatch.traceOf g run).units i)).length ≤
      cfg.load * cfg.carry1) := by
  have hunits : ∀ i, ∀ u ∈ (OnlineBatch.traceOf g run).units i,
      u ∈ (OnlineBatch.stateAt g run run.ops.length).frozen := by
    intro i u hu
    exact List.mem_of_mem_drop (List.mem_of_mem_take hu)
  have huniq : Requester.Unique (OnlineBatch.stateAt g run run.ops.length) :=
    RequesterUnique _ _ _ ⟨by simp, by simp [Bucket.recs]⟩
  have hshape := RequesterShape g.unitEntries ⟨[], []⟩
    ((run.ops.take run.ops.length).map OnlineBatch.Op.requester) hE
      (by simp) (by simpa using hE)
  change (∀ u ∈ (OnlineBatch.stateAt g run run.ops.length).frozen,
      u.length = g.unitEntries) ∧ _ at hshape
  refine ⟨fun i u hu => huniq.1 u (hunits i u hu), ?_⟩
  intro i
  have hlen : ((OnlineBatch.traceOf g run).units i).length ≤ g.unitsPerPrefix :=
    List.length_take_le _ _
  calc (DirectMasks.records ((OnlineBatch.traceOf g run).units i)).length
      ≤ ((OnlineBatch.traceOf g run).units i).length * g.unitEntries :=
        AdaptiveRequesterProof.records_length_le _ _
          (fun u hu => hshape.1 u (hunits i u hu))
    _ ≤ g.unitsPerPrefix * g.unitEntries := Nat.mul_le_mul_right _ hlen
    _ = cfg.load * cfg.carry1 := by
      rw [Nat.mul_comm, hgeom]
      simp [Config.carryPositions, Config.carry]

end RebuildBound.IdealDirectProof
