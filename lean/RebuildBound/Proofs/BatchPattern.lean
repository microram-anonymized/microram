import RebuildBound.Spec.ObliviousBatch
import RebuildBound.Proofs.OnlinePattern

/-!
# BatchPattern

The batch
version of `OnlinePattern`: the real/dummy pattern does not depend on the
words.

The batch `isReal` reads the words only through the key sets of the tables
strictly before the entry in slot `t`'s plan `S (chunkStart (widths run) t)`.
The schedule premises hold at `chunkStart (widths run) t ≤ t < n`
(`chunkStart_le`), so the top is the plan's last entry (`top_last`) and the
earlier tables lie below it, where the record sets are tape-invariant
(`HierarchyInvariantProof.low_recs`, generic over the trace).
-/

namespace RebuildBound.BatchPatternProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online
open RebuildBound.Model.OnlineBatch RebuildBound.Spec
open RebuildBound.HierarchyInvariantProof RebuildBound.OnlinePatternProof

/-- An operation's first slot is at or before the slot. -/
theorem chunkStart_le : ∀ (ws : List Nat) (t : Nat), chunkStart ws t ≤ t
  | [], t => by simp [chunkStart]
  | w :: ws, t => by
    unfold chunkStart
    split
    · omega
    · have := chunkStart_le ws (t - w)
      omega

/-- Key membership in a table below the top does not depend on the words. -/
theorem tableKeys_memFor (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct) {N : Nat}
    {g : OnlineGeom} {run : BatchRun} (hT : TracePremises geo.cfg N (OnlineBatch.traceOf g run))
    (words words' : Words) {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ < geo.cfg.levels) (v : Nat) (k : LogicalKey) :
    k ∈ OnlineBatch.tableKeys geo.cfg geo.shapes g run words ℓ v ↔
      k ∈ OnlineBatch.tableKeys geo.cfg geo.shapes g run words' ℓ v := by
  have e := low_recsFor geo F hT words words' ℓ h1 hL v
  unfold OnlineBatch.tableKeys
  simp only [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : x ∈ (table geo.cfg geo.shapes (OnlineBatch.traceOf g run) words' ℓ v).records.toFinset := by
      rw [← e]; exact List.mem_toFinset.2 hx
    exact ⟨x, List.mem_toFinset.1 this, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have : x ∈ (table geo.cfg geo.shapes (OnlineBatch.traceOf g run) words ℓ v).records.toFinset := by
      rw [e]; exact List.mem_toFinset.2 hx
    exact ⟨x, List.mem_toFinset.1 this, rfl⟩

/-- The pattern at any configuration with the invariant's facts. -/
theorem patternFor (geo : HierarchyGeometry) (F : LowFacts geo.cfg geo.rows geo.direct) :
    BatchPatternFor geo := by
  intro N g run S n m hS words words' t i ht hi
  obtain ⟨-, -, hR, hP⟩ := hS
  have hcp : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ geo.cfg.levels → 0 < geo.cfg.carryPositions ℓ :=
    fun ℓ a b => carryPositions_posFor F a b
  set j := chunkStart (widths run) t with hjdef
  have hj : j < n := lt_of_le_of_lt (chunkStart_le _ t) ht
  have hsch : slotSchedule (widths run) S t = S j := rfl
  rw [hsch] at hi
  have hlow : ∀ c ∈ (S j).tables.take i, c.1 < geo.cfg.levels :=
    top_last hcp (S j).tables 0 _ (hP.tile j hj)
      (fun c hc => ⟨(hP.coords j hj c hc).1, (hP.coords j hj c hc).2.1, (hP.coords j hj c hc).2.2.1⟩)
      (hP.oneTop j hj) i hi
  unfold OnlineBatch.isReal
  split
  · rfl
  · rename_i s _
    congr 1
    rw [hsch, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall_congr' fun c => imp_congr_right fun hc => ?_
    have h1 : 1 ≤ c.1 := (hP.coords j hj c (List.mem_of_mem_take hc)).1
    have hk := tableKeys_memFor geo F hR.trace words words' h1 (hlow c hc) c.2 s.record.key
    simpa using not_congr hk

/-- Original selected-geometry interface. -/
theorem tableKeys_mem {cfg : Config} {rows : List (SepGeom × Nat)} (F : Facts cfg rows) {N : Nat}
    {g : OnlineGeom} {run : BatchRun} (hT : TracePremises cfg N (OnlineBatch.traceOf g run))
    (words words' : Words) {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels) (v : Nat) (k : LogicalKey) :
    k ∈ OnlineBatch.tableKeys cfg (hierarchyShapes cfg rows) g run words ℓ v ↔
      k ∈ OnlineBatch.tableKeys cfg (hierarchyShapes cfg rows) g run words' ℓ v :=
  tableKeys_memFor (HierarchyGeometry.selected cfg rows) F.lowFacts hT words words' h1 hL v k

/-- Original selected-geometry interface. -/
theorem patternAt {cfg : Config} {rows : List (SepGeom × Nat)} (F : Facts cfg rows) :
    BatchPatternAt cfg rows :=
  patternFor (HierarchyGeometry.selected cfg rows) F.lowFacts

end RebuildBound.BatchPatternProof

open RebuildBound.HierarchyInvariantProof RebuildBound.BatchPatternProof in
/-- **BatchPattern.** -/
theorem RebuildBound.BatchPattern : RebuildBound.Spec.BatchPattern_statement := by
  intro h _
  exact ⟨patternAt (facts_horizon HierarchyHorizonFree uniformFacts (h * 2 ^ 32)),
    patternAt (facts_horizon HierarchyHorizonFree halfFanoutFacts (h * 2 ^ 32))⟩
