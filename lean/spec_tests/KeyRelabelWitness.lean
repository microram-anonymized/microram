import spec_tests.FixtureKeys
import RebuildBound.Proofs.KeyRelabel

/-! Fully discharged fixed-universe witnesses near the largest 64-bit key.
The scalar history queries initialized, dense live, and dense tombstone records.
The mixed batch history exercises duplicate forwarding and a tombstone followed
by reinsertion. Correctness holds for arbitrary routing and dummy words. -/

open MeasureTheory ProbabilityTheory
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
  RebuildBound.Model.Online

namespace KeyRelabelWitness

abbrev high : Nat := 2 ^ 64 - 1000
def U : Finset LogicalKey := fixtureKeys (Finset.Ico high (high + 100))
abbrev c1 : Config := (geometry31.chunk 1).cfg
def g : OnlineGeom := ⟨64, 8⟩
abbrev m0 : Nat := c1.levels

theorem U_card : U.card = 100 := by decide +kernel

theorem U_64 : ∀ k ∈ U, LogicalKey.toNat k < 2 ^ 64 := by
  intro k hk
  simp only [U, mem_fixtureKeys, Finset.mem_Ico] at hk
  norm_num [high] at hk ⊢
  omega

example : 2 ^ 31 < high ∧ high + 99 < 2 ^ 64 := by decide +kernel
theorem empty_compression :
    (∅ : Finset LogicalKey).map (KeyRelabel.compression ∅).toEmbedding = KeyIndex.range 0 := by
  simpa using KeyRelabel.compression_map (∅ : Finset LogicalKey)

def run : OnlineRun :=
  ⟨[.probe ⟨LogicalKey.ofNat (high), 10, false⟩, .probe ⟨LogicalKey.ofNat (high), 11, true⟩, .probe ⟨LogicalKey.ofNat (high), 12, false⟩],
    [⟨LogicalKey.ofNat (high), 9000, false⟩], fun _ => false⟩

theorem frozen : (stateAt g run run.ops.length).frozen = [] := by decide +kernel

theorem trace : UniverseTracePremises c1 U (traceOf g run) where
  nodup := by intro i u hu; simp [traceOf, frozen] at hu
  load := by intro i; simp [traceOf, frozen, DirectMasks.records]
  keys := by intro i x hx; simp [traceOf, frozen, DirectMasks.records] at hx
  initNodup := by simp [traceOf, run]
  initKeys := by
    intro x hx
    simp only [traceOf, run, List.mem_singleton] at hx
    subst x
    decide +kernel
theorem unsh (sh : Shapes) : UnshPromise c1 sh (traceOf g run) := by
  intro words o _ r _ h
  simp [earlyDrop, traceOf, run] at h

theorem setting : UniverseOnlineSetting (geometry31.chunk 1) U g run (syncSchedule c1) 3 m0 := by
  refine ⟨U_64, ?_, by decide +kernel, ⟨⟨by decide +kernel, by decide +kernel⟩, by decide +kernel, ?_, trace, unsh _⟩, ?_⟩
  · rw [U_card]; decide +kernel
  · intro o ho
    have : run.ops.all (fun o => decide (o.record.key ∈ U)) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp this o ho)
  · exact SyncSchedule31 1 3 le_rfl

/-- Actual high keys index the ideal tape; no maximum numeric key sizes its domain. -/
def words0 (ω : UniverseTape c1 U) : Words := fun l v k =>
  if h : (l, v) ∈ c1.coordinates.toFinset then
    if hk : k ∈ U then ((ω ⟨(l, v), h⟩ ⟨k, hk⟩ : Fin (2 ^ 64)) : Nat) else 0
  else 0

abbrev Ω0 := UniverseTape c1 U × DummyTape 3 m0
noncomputable abbrev μ0 : Measure Ω0 := uniformOn (Set.univ : Set Ω0)

theorem tape : UniverseOnlineTapePremises c1 U 3 m0 μ0 Prod.fst Prod.snd
    (fun ω => words0 ω.1) where
  measurable := by
    have h : (fun ω : Ω0 => (ω.1, ω.2)) = id := rfl
    rw [h]; exact measurable_id
  uniform := by
    have h : (fun ω : Ω0 => (ω.1, ω.2)) = id := rfl
    rw [h, Measure.map_id]
  agree := by
    intro ω p k
    obtain ⟨⟨a, b⟩, hp⟩ := p
    simp [words0, hp]

/-- Exact address law with every premise instantiated on the actual-key tape. -/
theorem exactLaw :
    μ0.map (fun ω : Ω0 => view c1 (geometry31.chunk 1).shapes g run (syncSchedule c1)
      3 m0 (words0 ω.1) (dummyOf ω.2)) = simLaw c1 (syncSchedule c1) (probePattern run) 3 m0 := by
  exact GenericOnlineExact31 1 le_rfl U g run (syncSchedule c1) 3 m0 setting
    μ0 Prod.fst Prod.snd (fun ω => words0 ω.1) tape

/-- Both failure comparisons apply to a concrete, measurable observation. -/
theorem failureLaw (A : Set (Fin 3 → Fin m0 → Nat)) :
    let obs : Ω0 → (Fin 3 → Fin m0 → Nat) := fun ω =>
      view c1 (geometry31.chunk 1).shapes g run (syncSchedule c1) 3 m0
        (words0 ω.1) (dummyOf ω.2)
    μ0 (obs ⁻¹' A) ≤ (simLaw c1 (syncSchedule c1) (probePattern run) 3 m0).map id A +
      μ0 {ω | Fails c1 (geometry31.chunk 1).shapes (traceOf g run) (words0 ω.1)} ∧
    (simLaw c1 (syncSchedule c1) (probePattern run) 3 m0).map id A ≤ μ0 (obs ⁻¹' A) +
      μ0 {ω | Fails c1 (geometry31.chunk 1).shapes (traceOf g run) (words0 ω.1)} := by
  intro obs
  exact GenericOnlineFailure31 1 le_rfl U g run (syncSchedule c1) 3 m0 setting
    μ0 Prod.fst Prod.snd (fun ω => words0 ω.1) tape obs id
    (measurable_of_countable _) measurable_id (fun _ _ => rfl) A MeasurableSet.of_discrete

/-- Agreement is required only on success: this observation returns 7 on failure. -/
theorem oblivious_junk (A : Set (Fin 3 → Fin m0 → Nat)) :
    let obs : Ω0 → (Fin 3 → Fin m0 → Nat) := fun ω => by
      classical
      exact if Fails c1 (geometry31.chunk 1).shapes (traceOf g run) (words0 ω.1)
        then fun _ _ => 7 else view c1 (geometry31.chunk 1).shapes g run
          (syncSchedule c1) 3 m0 (words0 ω.1) (dummyOf ω.2)
    μ0 (obs ⁻¹' A) ≤ (simLaw c1 (syncSchedule c1) (probePattern run) 3 m0).map id A +
        ENNReal.ofReal ((1 : ℝ) / 2 ^ 64) ∧
      (simLaw c1 (syncSchedule c1) (probePattern run) 3 m0).map id A ≤
        μ0 (obs ⁻¹' A) + ENNReal.ofReal ((1 : ℝ) / 2 ^ 64) := by
  intro obs
  simpa only [Nat.cast_one, one_mul] using GenericOnlineOblivious31 1 le_rfl U g run
    (syncSchedule c1) 3 m0 setting μ0 Prod.fst Prod.snd (fun ω => words0 ω.1) tape
    obs id (measurable_of_countable _) measurable_id (fun ω h => by simp [obs, h])
    A MeasurableSet.of_discrete

/-- The initialized top supplies a real first query for every routing tape. -/
theorem scalar_init (w : Words) (dummy : Nat → Nat → Nat) :
    Probe.decode (Probe.scalar c1 (geometry31.chunk 1).shapes g run (syncSchedule c1)
      w dummy 0).found = some 9000 := by
  have h := GenericOnlineCorrectness31 1 le_rfl U g run (syncSchedule c1) 3 m0 setting
    w dummy 0 (.probe ⟨LogicalKey.ofNat (high), 10, false⟩) (by decide +kernel) rfl rfl
  have hist : Probe.latestValue (LogicalKey.ofNat high) (run.init ++ (run.ops.take 0).map Op.record) = some 9000 := by
    decide +kernel
  exact h.1.trans hist

/-- A repeated dense key supplies its value and produces the model's exact addresses. -/
theorem scalar_dense (w : Words) (dummy : Nat → Nat → Nat) :
    Probe.decode (Probe.scalar c1 (geometry31.chunk 1).shapes g run (syncSchedule c1)
      w dummy 1).found = some 10 ∧
    ∀ i, (Probe.scalar c1 (geometry31.chunk 1).shapes g run (syncSchedule c1) w dummy 1).addresses.getD i 0 =
      touched c1 (geometry31.chunk 1).shapes g run (syncSchedule c1) w dummy 1 i := by
  have h := GenericOnlineCorrectness31 1 le_rfl U g run (syncSchedule c1) 3 m0 setting
    w dummy 1 (.probe ⟨LogicalKey.ofNat (high), 11, true⟩) (by decide +kernel) rfl rfl
  have hist : Probe.latestValue (LogicalKey.ofNat high) (run.init ++ (run.ops.take 1).map Op.record) = some 10 := by decide +kernel
  exact ⟨h.1.trans hist, h.2⟩

theorem scalar_tombstone (w : Words) (dummy : Nat → Nat → Nat) :
    Probe.decode (Probe.scalar c1 (geometry31.chunk 1).shapes g run (syncSchedule c1)
      w dummy 2).found = none := by
  have h := GenericOnlineCorrectness31 1 le_rfl U g run (syncSchedule c1) 3 m0 setting
    w dummy 2 (.probe ⟨LogicalKey.ofNat (high), 12, false⟩) (by decide +kernel) rfl rfl
  have hist : Probe.latestValue (LogicalKey.ofNat high) (run.init ++ (run.ops.take 2).map Op.record) = none := by decide +kernel
  exact h.1.trans hist

theorem real0 (w : Words) : isReal c1 (geometry31.chunk 1).shapes g run (syncSchedule c1) w 0 0 = true := by
  simp [isReal, run, denseKeys, denseRecords, stateAt, Requester.run, Op.probes, Op.record, Bucket.recs]

theorem dummy1 (w : Words) (i : Nat) :
    isReal c1 (geometry31.chunk 1).shapes g run (syncSchedule c1) w 1 i = false := by
  have hd : (denseKeys c1 g run (syncSchedule c1) 1).contains (LogicalKey.ofNat high) = true := by decide +kernel
  have hop : run.ops[1]? = some (.probe ⟨LogicalKey.ofNat (high), 11, true⟩) := rfl
  unfold isReal
  rw [hop]
  simp only [Op.record, Op.probes, hd, Bool.not_true, Bool.true_and, Bool.false_and]

/-- Real/dummy classifications are identical for any two family tapes. -/
theorem pattern (w w' : Words) (j i : Nat) (hj : j < 3)
    (hi : i < (syncSchedule c1 j).tables.length) :
    isReal c1 (geometry31.chunk 1).shapes g run (syncSchedule c1) w j i =
      isReal c1 (geometry31.chunk 1).shapes g run (syncSchedule c1) w' j i :=
  GenericOnlinePattern31 1 le_rfl U g run (syncSchedule c1) 3 m0 setting w w' j i hj hi

/-- The real initial query uses an actual high key and an admitted family. -/
theorem fresh_first (w : Words) :
    ∃ c o, (syncSchedule c1 0).tables[0]? = some c ∧ run.ops[0]? = some o ∧
      familyOf c1 c.1 c.2 ∈ c1.coordinates ∧ o.record.key ∈ U := by
  exact (GenericOnlineFresh31 1 le_rfl U g run (syncSchedule c1) 3 m0 setting w).1
    0 0 (by decide +kernel) (by decide +kernel) (real0 w)

namespace Batch
open OnlineBatch

def run0 : BatchRun :=
  ⟨[.probe ⟨LogicalKey.ofNat (high + 3), 0, false⟩,
    .batch [⟨LogicalKey.ofNat (high + 5), 1, false⟩, ⟨LogicalKey.ofNat (high + 7), 2, false⟩,
      ⟨LogicalKey.ofNat (high + 5), 3, true⟩, ⟨LogicalKey.ofNat (high + 5), 4, false⟩],
    .blind ⟨LogicalKey.ofNat (high + 7), 5, false⟩,
    .batch [⟨LogicalKey.ofNat (high + 3), 6, false⟩, ⟨LogicalKey.ofNat (high + 3), 7, true⟩]],
    [⟨LogicalKey.ofNat (high + 3), 90, false⟩], fun _ => false⟩

example : run0.init ≠ [] := by decide +kernel
example : ((slots run0).filter (OnlineBatch.duplicate run0)).length = 3 := by decide +kernel

theorem frozen0 : (OnlineBatch.stateAt g run0 run0.ops.length).frozen = [] := by decide +kernel

theorem trace0 : UniverseTracePremises c1 U (OnlineBatch.traceOf g run0) where
  nodup := by intro i u hu; simp [OnlineBatch.traceOf, frozen0] at hu
  load := by intro i; simp [OnlineBatch.traceOf, frozen0, DirectMasks.records]
  keys := by intro i x hx; simp [OnlineBatch.traceOf, frozen0, DirectMasks.records] at hx
  initNodup := by simp [OnlineBatch.traceOf, run0]
  initKeys := by
    intro x hx
    simp only [OnlineBatch.traceOf, run0, List.mem_singleton] at hx
    subst x
    decide +kernel
theorem unsh0 (sh : Shapes) : UnshPromise c1 sh (OnlineBatch.traceOf g run0) := by
  intro words o _ r _ h
  simp [earlyDrop, OnlineBatch.traceOf, run0] at h

theorem setting0 :
    UniverseBatchSetting (geometry31.chunk 1) U g run0 (syncSchedule c1) 8 m0 := by
  refine ⟨U_64, ?_, by decide +kernel, ⟨⟨by decide +kernel, by decide +kernel⟩, by decide +kernel, ?_, trace0, unsh0 _⟩, ?_⟩
  · rw [U_card]; decide +kernel
  · intro s hs
    have : (slots run0).all (fun s => decide (s.record.key ∈ U)) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp this s hs)
  · exact SyncSchedule31 1 8 le_rfl

abbrev ΩB := UniverseTape c1 U × DummyTape 8 m0
noncomputable abbrev μB : Measure ΩB := uniformOn (Set.univ : Set ΩB)

theorem tape0 : UniverseOnlineTapePremises c1 U 8 m0 μB Prod.fst Prod.snd
    (fun ω => words0 ω.1) where
  measurable := by
    have h : (fun ω : ΩB => (ω.1, ω.2)) = id := rfl
    rw [h]; exact measurable_id
  uniform := by
    have h : (fun ω : ΩB => (ω.1, ω.2)) = id := rfl
    rw [h, Measure.map_id]
  agree := by
    intro ω p k
    obtain ⟨⟨a, b⟩, hp⟩ := p
    simp [words0, hp]

theorem exactLaw :
    μB.map (fun ω : ΩB => OnlineBatch.view c1 (geometry31.chunk 1).shapes g run0 (syncSchedule c1)
      8 m0 (words0 ω.1) (dummyOf ω.2)) =
      simLaw c1 (slotSchedule (widths run0) (syncSchedule c1)) (OnlineBatch.probePattern run0) 8 m0 := by
  exact GenericBatchExact31 1 le_rfl U g run0 (syncSchedule c1) 8 m0 setting0
    μB Prod.fst Prod.snd (fun ω => words0 ω.1) tape0

theorem failureLaw (A : Set (Fin 8 → Fin m0 → Nat)) :
    let obs : ΩB → (Fin 8 → Fin m0 → Nat) := fun ω =>
      OnlineBatch.view c1 (geometry31.chunk 1).shapes g run0 (syncSchedule c1) 8 m0
        (words0 ω.1) (dummyOf ω.2)
    μB (obs ⁻¹' A) ≤
      (simLaw c1 (slotSchedule (widths run0) (syncSchedule c1))
        (OnlineBatch.probePattern run0) 8 m0).map id A +
      μB {ω | Fails c1 (geometry31.chunk 1).shapes (OnlineBatch.traceOf g run0) (words0 ω.1)} ∧
    (simLaw c1 (slotSchedule (widths run0) (syncSchedule c1))
        (OnlineBatch.probePattern run0) 8 m0).map id A ≤ μB (obs ⁻¹' A) +
      μB {ω | Fails c1 (geometry31.chunk 1).shapes (OnlineBatch.traceOf g run0) (words0 ω.1)} := by
  intro obs
  exact GenericBatchFailure31 1 le_rfl U g run0 (syncSchedule c1) 8 m0 setting0
    μB Prod.fst Prod.snd (fun ω => words0 ω.1) tape0 obs id
    (measurable_of_countable _) measurable_id (fun _ _ => rfl) A MeasurableSet.of_discrete

theorem applied (A : Set (Fin 8 → Fin m0 → Nat)) :
    let obs : ΩB → (Fin 8 → Fin m0 → Nat) := fun ω =>
      OnlineBatch.view c1 (geometry31.chunk 1).shapes g run0 (syncSchedule c1) 8 m0
        (words0 ω.1) (dummyOf ω.2)
    μB (obs ⁻¹' A) ≤
        (simLaw c1 (slotSchedule (widths run0) (syncSchedule c1))
          (OnlineBatch.probePattern run0) 8 m0).map id A +
            ENNReal.ofReal ((1 : ℝ) / 2 ^ 64) ∧
      (simLaw c1 (slotSchedule (widths run0) (syncSchedule c1))
          (OnlineBatch.probePattern run0) 8 m0).map id A ≤
        μB (obs ⁻¹' A) + ENNReal.ofReal ((1 : ℝ) / 2 ^ 64) := by
  intro obs
  simpa only [Nat.cast_one, one_mul] using GenericBatchOblivious31 1 le_rfl U g run0
    (syncSchedule c1) 8 m0 setting0 μB Prod.fst Prod.snd (fun ω => words0 ω.1)
    tape0 obs id (measurable_of_countable _) measurable_id (fun _ _ => rfl) A MeasurableSet.of_discrete

/-- A superseded tombstone lane still reads the earlier live duplicate. -/
theorem duplicate (w : Words) (dummy : Nat → Nat → Nat) :
    Probe.decode (Probe.batch c1 (geometry31.chunk 1).shapes g run0
        (syncSchedule c1) w dummy 3).found = some 1 ∧
      ∀ i, (Probe.batch c1 (geometry31.chunk 1).shapes g run0
        (syncSchedule c1) w dummy 3).addresses.getD i 0 =
          OnlineBatch.touched c1 (geometry31.chunk 1).shapes g run0 (syncSchedule c1) w dummy 3 i := by
  have h := GenericBatchCorrectness31 1 le_rfl U g run0 (syncSchedule c1) 8 m0 setting0
    w dummy 3 (⟨1, 2, ⟨LogicalKey.ofNat (high + 5), 3, true⟩, true⟩ : OnlineBatch.Slot)
      (by decide +kernel) rfl rfl
  have hist : Probe.latestValue (LogicalKey.ofNat (high + 5))
      (run0.init ++ ((OnlineBatch.slots run0).take 3).map OnlineBatch.Slot.record) = some 1 := by decide +kernel
  exact ⟨h.1.trans hist, h.2⟩

/-- The reinsertion lane sees the earlier tombstone as absence. -/
theorem tombstone (w : Words) (dummy : Nat → Nat → Nat) :
    Probe.decode (Probe.batch c1 (geometry31.chunk 1).shapes g run0
      (syncSchedule c1) w dummy 4).found = none := by
  have h := GenericBatchCorrectness31 1 le_rfl U g run0 (syncSchedule c1) 8 m0 setting0
    w dummy 4 (⟨1, 3, ⟨LogicalKey.ofNat (high + 5), 4, false⟩, true⟩ : OnlineBatch.Slot)
      (by decide +kernel) rfl rfl
  have hist : Probe.latestValue (LogicalKey.ofNat (high + 5))
      (run0.init ++ ((OnlineBatch.slots run0).take 4).map OnlineBatch.Slot.record) = none := by decide +kernel
  exact h.1.trans hist

theorem pattern (w w' : Words) (t i : Nat) (ht : t < 8)
    (hi : i < (slotSchedule (widths run0) (syncSchedule c1) t).tables.length) :
    OnlineBatch.isReal c1 (geometry31.chunk 1).shapes g run0 (syncSchedule c1) w t i =
      OnlineBatch.isReal c1 (geometry31.chunk 1).shapes g run0 (syncSchedule c1) w' t i :=
  GenericBatchPattern31 1 le_rfl U g run0 (syncSchedule c1) 8 m0 setting0 w w' t i ht hi

theorem real0 (w : Words) :
    OnlineBatch.isReal c1 (geometry31.chunk 1).shapes g run0 (syncSchedule c1) w 0 0 = true := by
  rfl

theorem fresh_first (w : Words) :
    ∃ c s, (slotSchedule (widths run0) (syncSchedule c1) 0).tables[0]? = some c ∧
      (slots run0)[0]? = some s ∧ familyOf c1 c.1 c.2 ∈ c1.coordinates ∧ s.record.key ∈ U := by
  exact (GenericBatchFresh31 1 le_rfl U g run0 (syncSchedule c1) 8 m0 setting0 w).1
    0 0 (by decide +kernel) (by decide +kernel) (real0 w)

end Batch

abbrev ΩH := UniverseTape c1 U
noncomputable abbrev μH : Measure ΩH := uniformOn (Set.univ : Set ΩH)

theorem hierarchyTape : UniverseTapePremises c1 U μH id words0 where
  measurable := measurable_id
  uniform := by rw [Measure.map_id]
  agree := by
    intro ω p k
    obtain ⟨⟨a, b⟩, hp⟩ := p
    simp [words0, hp]

theorem hierarchyWindows :
    μH {ω | Fails (chunkConfig config31 1) (geometry31.chunk 1).shapes (traceOf g run) (words0 ω)} ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 64) := by
  have h := GenericHierarchyWindows31 1 U (traceOf g run) le_rfl U_64
    (by rw [U_card]; decide +kernel) trace (unsh _) μH id words0 hierarchyTape
  simpa only [Nat.cast_one, one_mul] using h

theorem hierarchyChunk :
    μH {ω | ChunkFails config31 (geometry31.chunk 1).shapes (traceOf g run) (words0 ω) 0} ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 64) := by
  exact GenericHierarchyChunk31 0 U (traceOf g run) U_64 (by rw [U_card]; decide +kernel)
    trace (unsh _) μH id words0 hierarchyTape

end KeyRelabelWitness

#print axioms KeyRelabelWitness.exactLaw
#print axioms KeyRelabelWitness.failureLaw
#print axioms KeyRelabelWitness.oblivious_junk
#print axioms KeyRelabelWitness.scalar_init
#print axioms KeyRelabelWitness.scalar_dense
#print axioms KeyRelabelWitness.scalar_tombstone
#print axioms KeyRelabelWitness.Batch.exactLaw
#print axioms KeyRelabelWitness.Batch.failureLaw
#print axioms KeyRelabelWitness.Batch.applied
#print axioms KeyRelabelWitness.Batch.duplicate
#print axioms KeyRelabelWitness.Batch.tombstone
#print axioms KeyRelabelWitness.hierarchyWindows
#print axioms KeyRelabelWitness.hierarchyChunk

#print axioms KeyRelabelWitness.pattern
#print axioms KeyRelabelWitness.fresh_first
#print axioms KeyRelabelWitness.Batch.pattern
#print axioms KeyRelabelWitness.Batch.fresh_first
