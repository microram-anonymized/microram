import RebuildBound.Proofs.OnlineOblivious31
import RebuildBound.Proofs.BatchOblivious31
import RebuildBound.Proofs.ProbeCorrectness31

/-! Nonvacuity at capacity 2^31. All premises are discharged. Nonempty
initialization and keys strictly above 2^27 exercise the enlarged universe.
Only small histories and online states are evaluated; hierarchy tables remain symbolic. -/

open MeasureTheory ProbabilityTheory
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
  RebuildBound.Model.Online

set_option maxRecDepth 200000

namespace Online31Witness

abbrev N0 : Nat := 2 ^ 31
abbrev high : Nat := 2 ^ 27 + 1000
abbrev c1 : Config := (geometry31.chunk 1).cfg
def g : OnlineGeom := ⟨64, 8⟩
def ops : List Op := (List.range 520).map fun j => .probe ⟨LogicalKey.ofNat (high + j % 100), j, false⟩
def init0 : List Rec := [⟨LogicalKey.ofNat (high), 9000, false⟩]
def run : OnlineRun := ⟨ops, init0, fun _ => false⟩
abbrev n0 : Nat := 520
abbrev m0 : Nat := c1.levels

theorem len_ops : run.ops.length = 520 := by simp [run, ops]

theorem frozen_len : (stateAt g run 520).frozen.length = 8 := by decide +kernel

theorem frozen_nodup : ∀ u ∈ (stateAt g run 520).frozen, (u.recs.map Rec.key).Nodup := by
  decide +kernel

theorem frozen_keys : ∀ x ∈ DirectMasks.records (stateAt g run 520).frozen, LogicalKey.toNat x.key < N0 := by
  decide +kernel

theorem frozen_load : (DirectMasks.records (stateAt g run 520).frozen).length ≤ 512 := by
  decide +kernel

theorem units_eq (i : Nat) :
    (traceOf g run).units i = if i = 0 then (stateAt g run 520).frozen else [] := by
  simp only [traceOf, len_ops]
  split
  · subst_vars
    have h8 : g.unitsPerPrefix = (stateAt g run 520).frozen.length := by rw [frozen_len]; rfl
    rw [Nat.zero_mul, List.drop_zero, h8, List.take_length]
  · have : (stateAt g run 520).frozen.length ≤ i * g.unitsPerPrefix := by
      rw [frozen_len]; simp [g]; omega
    simp [List.drop_eq_nil_of_le this]

theorem trace : TracePremises c1 N0 (traceOf g run) where
  nodup := by
    intro i u hu
    rw [units_eq] at hu
    split at hu
    · exact frozen_nodup u hu
    · simp at hu
  load := by
    intro i
    rw [units_eq]
    split
    · simpa [c1, HierarchyGeometry.chunk, geometry31, chunkConfig, config31] using frozen_load
    · simp [DirectMasks.records]
  keys := by
    intro i x hx
    rw [units_eq] at hx
    split at hx
    · exact frozen_keys x hx
    · simp [DirectMasks.records] at hx
  initNodup := by simp [traceOf, run, init0]
  initKeys := by
    intro x hx
    simp only [traceOf, run, init0, List.mem_singleton] at hx
    subst x
    decide +kernel
theorem unsh : UnshPromise c1 ((geometry31.chunk 1).shapes) (traceOf g run) := by
  intro words o _ r _ h
  simp [earlyDrop, traceOf, run] at h

theorem runPremises : OnlineRunPremises c1 ((geometry31.chunk 1).shapes) N0 g run where
  geom := by decide +kernel
  horizon := by rw [len_ops]; decide +kernel
  keys := by
    intro o ho
    simp only [run, ops, List.mem_map, List.mem_range] at ho
    obtain ⟨j, _, rfl⟩ := ho
    change LogicalKey.toNat (LogicalKey.ofNat (high + j % 100)) < 2 ^ 31
    rw [LogicalKey.toNat_ofNat]
    have := Nat.mod_lt j (by omega : 0 < 100)
    dsimp [high]
    omega
  trace := trace
  unsh := unsh

theorem schedule : SchedulePremises c1 (syncSchedule c1) n0 m0 :=
  SyncSchedule31 1 n0 le_rfl

theorem setting : OnlineSettingFor (geometry31.chunk 1) N0 g run (syncSchedule c1) n0 m0 :=
  ⟨by decide +kernel, by rw [len_ops], runPremises, schedule⟩

/-! The joint ideal tape. -/

abbrev Ω0 : Type := FamilyTape c1 N0 × DummyTape n0 m0

def words0 (ω : FamilyTape c1 N0) : Words := fun ℓ v k =>
  if h : (ℓ, v) ∈ c1.coordinates.toFinset then
    if hk : LogicalKey.toNat k < N0 then ((ω ⟨(ℓ, v), h⟩ ⟨k, hk⟩ : Fin (2 ^ 64)) : Nat) else 0
  else 0

noncomputable abbrev μ0 : Measure Ω0 := uniformOn (Set.univ : Set Ω0)

theorem tape : OnlineTapePremises c1 N0 n0 m0 μ0 Prod.fst Prod.snd (fun ω => words0 ω.1) where
  measurable := by
    have : (fun ω : Ω0 => (ω.1, ω.2)) = id := funext fun _ => rfl
    rw [this]; exact measurable_id
  uniform := by
    have : (fun ω : Ω0 => (ω.1, ω.2)) = id := funext fun _ => rfl
    rw [this, Measure.map_id]
  agree := by
    intro ω p k hk
    obtain ⟨⟨a, b⟩, hp⟩ := p
    simp [words0, hp, hk]

/-! Apply the theorem with the identity observation and with an observation
that is arbitrary on the failure event. -/

theorem applied (A : Set (Fin n0 → Fin m0 → Nat)) :
    μ0 ((fun ω : Ω0 => view c1 ((geometry31.chunk 1).shapes) g run (syncSchedule c1) n0 m0
        (words0 ω.1) (dummyOf ω.2)) ⁻¹' A) ≤
      simLaw c1 (syncSchedule c1) (probePattern run) n0 m0 A +
        ENNReal.ofReal ((1 : ℝ) / 2 ^ 64) := by
  have := (OnlineOblivious31 1 le_rfl N0 g run
    (syncSchedule c1) n0 m0 setting μ0 Prod.fst Prod.snd (fun ω => words0 ω.1) tape
    (fun ω => view c1 ((geometry31.chunk 1).shapes) g run (syncSchedule c1) n0 m0
        (words0 ω.1) (dummyOf ω.2)) id (measurable_of_countable _) measurable_id
    (fun _ _ => rfl) A (MeasurableSet.of_discrete)).1
  rw [Measure.map_id] at this
  simpa only [Nat.cast_one, one_mul] using this

theorem applied_junk (A : Set (Fin n0 → Fin m0 → Nat)) :
    let obs : Ω0 → (Fin n0 → Fin m0 → Nat) := fun ω => by
      classical
      exact if Fails c1 ((geometry31.chunk 1).shapes) (traceOf g run) (words0 ω.1) then
        fun _ _ => 7 else
        view c1 ((geometry31.chunk 1).shapes) g run (syncSchedule c1) n0 m0 (words0 ω.1)
          (dummyOf ω.2)
    μ0 (obs ⁻¹' A) ≤ simLaw c1 (syncSchedule c1) (probePattern run) n0 m0 A +
        ENNReal.ofReal ((1 : ℝ) / 2 ^ 64) := by
  intro obs
  have := (OnlineOblivious31 1 le_rfl N0 g run
    (syncSchedule c1) n0 m0 setting μ0 Prod.fst Prod.snd (fun ω => words0 ω.1) tape
    obs id (measurable_of_countable _) measurable_id
    (fun ω h => by simp [obs, h]) A (MeasurableSet.of_discrete)).1
  rw [Measure.map_id] at this
  simpa only [Nat.cast_one, one_mul] using this

/-- The key universe is exercised above the old capacity. -/
example : 2 ^ 27 < high ∧ high + 99 < N0 := by decide +kernel
example : run.init ≠ [] := by decide +kernel

/-- The first prefix is consumed before operation 512. -/
example : (syncSchedule c1 512).tables.head? = some (1, config31.seed 1 + 1) := by
  decide +kernel

/-- Operation 512 sees operation 412's latest value after crossing a prefix. -/
theorem scalar512 (words : Words) (dummy : Nat → Nat → Nat) :
    Probe.decode (Probe.scalar c1 (geometry31.chunk 1).shapes g run
        (syncSchedule c1) words dummy 512).found = some 412 ∧
      ∀ i, (Probe.scalar c1 (geometry31.chunk 1).shapes g run
        (syncSchedule c1) words dummy 512).addresses.getD i 0 =
          touched c1 (geometry31.chunk 1).shapes g run (syncSchedule c1) words dummy 512 i := by
  have h := OnlineCorrectness31 1 le_rfl N0 g run (syncSchedule c1) n0 m0 setting
    words dummy 512 (.probe ⟨LogicalKey.ofNat (high + 12), 512, false⟩) (by decide +kernel) rfl rfl
  have history : Probe.latestValue (LogicalKey.ofNat (high + 12))
      (run.init ++ (run.ops.take 512).map Op.record) = some 412 := by decide +kernel
  simpa only [Op.record, history] using h

/-- The nonempty initialized top supplies the first answer. -/
theorem scalar_init (words : Words) (dummy : Nat → Nat → Nat) :
    Probe.decode (Probe.scalar c1 (geometry31.chunk 1).shapes g run
      (syncSchedule c1) words dummy 0).found = some 9000 := by
  have h := OnlineCorrectness31 1 le_rfl N0 g run (syncSchedule c1) n0 m0 setting
    words dummy 0 (.probe ⟨LogicalKey.ofNat (high), 0, false⟩) (by decide +kernel) rfl rfl
  have history : Probe.latestValue (LogicalKey.ofNat high)
      (run.init ++ (run.ops.take 0).map Op.record) = some 9000 := by decide +kernel
  simpa only [Op.record, history] using h.1

/-- The first published low table receives a real query at the prefix boundary. -/
theorem dense512 : denseKeys c1 g run (syncSchedule c1) 512 = [] := by decide +kernel

theorem real512 (words : Words) :
    isReal c1 (geometry31.chunk 1).shapes g run (syncSchedule c1) words 512 0 = true := by
  unfold isReal
  rw [dense512]
  simp [run, ops, Op.probes]

/-- Repeated high keys inside the dense prefix use dummy table addresses. -/
theorem dense112_hit : (denseKeys c1 g run (syncSchedule c1) 112).contains (LogicalKey.ofNat (high + 12)) = true := by
  decide +kernel

theorem dummy112 (words : Words) (i : Nat) :
    isReal c1 (geometry31.chunk 1).shapes g run (syncSchedule c1) words 112 i = false := by
  unfold isReal
  have : (run.ops[112]?) = some (.probe ⟨LogicalKey.ofNat (high + 12), 112, false⟩) := rfl
  rw [this]
  simp only [Op.record, Op.probes, dense112_hit, Bool.not_true, Bool.true_and, Bool.false_and]

namespace Batch
open OnlineBatch

/-- Mixed scalar operations and chunks, including duplicate keys, a tombstone,
and reinsertion after the tombstone in the same chunk. -/
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

theorem trace0 : TracePremises c1 N0 (OnlineBatch.traceOf g run0) where
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
    BatchSettingFor (geometry31.chunk 1) N0 g run0 (syncSchedule c1) 8 c1.levels := by
  refine ⟨by decide +kernel, by decide +kernel, ⟨⟨by decide +kernel, by decide +kernel⟩, by decide +kernel, ?_, trace0, unsh0 _⟩, ?_⟩
  · intro s hs
    have : (slots run0).all (fun s => decide (LogicalKey.toNat s.record.key < N0)) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp this s hs)
  · exact SyncSchedule31 1 8 le_rfl

abbrev ΩB := FamilyTape c1 N0 × DummyTape 8 c1.levels
noncomputable abbrev μB : Measure ΩB := uniformOn (Set.univ : Set ΩB)

theorem tape0 : OnlineTapePremises c1 N0 8 c1.levels μB Prod.fst Prod.snd
    (fun ω => words0 ω.1) where
  measurable := by
    have : (fun ω : ΩB => (ω.1, ω.2)) = id := rfl
    rw [this]; exact measurable_id
  uniform := by
    have : (fun ω : ΩB => (ω.1, ω.2)) = id := rfl
    rw [this, Measure.map_id]
  agree := by
    intro ω p k hk
    obtain ⟨⟨a, b⟩, hp⟩ := p
    simp [words0, hp, hk]

/-- Both numerical inequalities apply with every premise discharged. -/
theorem applied (A : Set (Fin 8 → Fin c1.levels → Nat)) (hA : MeasurableSet A) :
    let obs : ΩB → (Fin 8 → Fin c1.levels → Nat) := fun ω =>
      OnlineBatch.view c1 (geometry31.chunk 1).shapes g run0 (syncSchedule c1) 8 c1.levels
        (words0 ω.1) (dummyOf ω.2)
    μB (obs ⁻¹' A) ≤
        (simLaw c1 (slotSchedule (widths run0) (syncSchedule c1))
          (OnlineBatch.probePattern run0) 8 c1.levels).map id A +
            ENNReal.ofReal ((1 : ℝ) / 2 ^ 64) ∧
      (simLaw c1 (slotSchedule (widths run0) (syncSchedule c1))
          (OnlineBatch.probePattern run0) 8 c1.levels).map id A ≤
        μB (obs ⁻¹' A) + ENNReal.ofReal ((1 : ℝ) / 2 ^ 64) := by
  intro obs
  simpa only [Nat.cast_one, one_mul] using BatchOblivious31 1 le_rfl N0 g run0
    (syncSchedule c1) 8 c1.levels setting0 μB Prod.fst Prod.snd (fun ω => words0 ω.1)
    tape0 obs id (measurable_of_countable _) measurable_id (fun _ _ => rfl) A hA

/-- A superseded tombstone lane reads the earlier live lane; its addresses
still equal the batch model's address view. -/
theorem duplicate (words : Words) (dummy : Nat → Nat → Nat) :
    Probe.decode (Probe.batch c1 (geometry31.chunk 1).shapes g run0
        (syncSchedule c1) words dummy 3).found = some 1 ∧
      ∀ i, (Probe.batch c1 (geometry31.chunk 1).shapes g run0
        (syncSchedule c1) words dummy 3).addresses.getD i 0 =
          OnlineBatch.touched c1 (geometry31.chunk 1).shapes g run0
            (syncSchedule c1) words dummy 3 i := by
  have h := BatchCorrectness31 1 le_rfl N0 g run0 (syncSchedule c1) 8 c1.levels setting0
    words dummy 3 (⟨1, 2, ⟨LogicalKey.ofNat (high + 5), 3, true⟩, true⟩ : OnlineBatch.Slot)
      (by decide +kernel) rfl rfl
  have history : Probe.latestValue (LogicalKey.ofNat (high + 5))
      (run0.init ++ ((OnlineBatch.slots run0).take 3).map OnlineBatch.Slot.record) =
        some 1 := by decide +kernel
  simpa only [history] using h

/-- The effective reinsertion lane sees the earlier tombstone as absence. -/
theorem tombstone (words : Words) (dummy : Nat → Nat → Nat) :
    Probe.decode (Probe.batch c1 (geometry31.chunk 1).shapes g run0
      (syncSchedule c1) words dummy 4).found = none := by
  have h := BatchCorrectness31 1 le_rfl N0 g run0 (syncSchedule c1) 8 c1.levels setting0
    words dummy 4 (⟨1, 3, ⟨LogicalKey.ofNat (high + 5), 4, false⟩, true⟩ : OnlineBatch.Slot)
      (by decide +kernel) rfl rfl
  have history : Probe.latestValue (LogicalKey.ofNat (high + 5))
      (run0.init ++ ((OnlineBatch.slots run0).take 4).map OnlineBatch.Slot.record) =
        none := by decide +kernel
  simpa only [history] using h.1


/-- The same public shape as `run0`, with distinct keys within each chunk. -/
def run1 : BatchRun :=
  ⟨[.probe ⟨LogicalKey.ofNat (high + 3), 0, false⟩,
    .batch [⟨LogicalKey.ofNat (high + 5), 1, false⟩, ⟨LogicalKey.ofNat (high + 7), 2, false⟩,
      ⟨LogicalKey.ofNat (high + 11), 3, true⟩, ⟨LogicalKey.ofNat (high + 9), 4, false⟩],
    .blind ⟨LogicalKey.ofNat (high + 7), 5, false⟩,
    .batch [⟨LogicalKey.ofNat (high + 3), 6, false⟩, ⟨LogicalKey.ofNat (high + 13), 7, true⟩]],
    [⟨LogicalKey.ofNat (high + 3), 90, false⟩], fun _ => false⟩

example : ((slots run1).filter (OnlineBatch.duplicate run1)).length = 0 := by decide +kernel

theorem setting1 :
    BatchSettingFor (geometry31.chunk 1) N0 g run1 (syncSchedule c1) 8 c1.levels := by
  have frozen1 : (OnlineBatch.stateAt g run1 run1.ops.length).frozen = [] := by decide +kernel
  refine ⟨by decide +kernel, by decide +kernel, ⟨⟨by decide +kernel, by decide +kernel⟩, by decide +kernel, ?_, ?_, ?_⟩, ?_⟩
  · intro s hs
    have : (slots run1).all (fun s => decide (LogicalKey.toNat s.record.key < N0)) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp this s hs)
  · exact { nodup := by intro i u hu; simp [OnlineBatch.traceOf, frozen1] at hu
            load := by intro i; simp [OnlineBatch.traceOf, frozen1, DirectMasks.records]
            keys := by intro i x hx; simp [OnlineBatch.traceOf, frozen1, DirectMasks.records] at hx
            initNodup := by simp [OnlineBatch.traceOf, run1]
            initKeys := by
              intro x hx
              simp only [OnlineBatch.traceOf, run1, List.mem_singleton] at hx
              subst x
              decide +kernel }
  · intro words o _ r _ h
    simp [earlyDrop, OnlineBatch.traceOf, run1] at h
  · exact SyncSchedule31 1 8 le_rfl

/-- Duplicate keys do not change the simulator's public inputs. -/
theorem sim_same (S : Schedule) (n m : Nat) :
    simLaw c1 (slotSchedule (widths run0) S) (OnlineBatch.probePattern run0) n m =
      simLaw c1 (slotSchedule (widths run1) S) (OnlineBatch.probePattern run1) n m := by
  have hw : widths run0 = widths run1 := by decide +kernel
  have hp : (slots run0).map Slot.probes = (slots run1).map Slot.probes := by decide +kernel
  have : OnlineBatch.probePattern run0 = OnlineBatch.probePattern run1 := by
    funext t
    have := congrArg (fun l => l[t]?) hp
    simp only [List.getElem?_map] at this
    simp [OnlineBatch.probePattern, this]
  rw [hw, this]

/-- Runs with three duplicate lanes and none have the same public shape and
are within twice the geometry-31 error bound on every measurable view event. -/
theorem dup_hidden (A : Set (Fin 8 → Fin c1.levels → Nat)) (hA : MeasurableSet A) :
    let obs := fun (run : BatchRun) (ω : ΩB) =>
      OnlineBatch.view c1 (geometry31.chunk 1).shapes g run (syncSchedule c1) 8 c1.levels
        (words0 ω.1) (dummyOf ω.2)
    μB (obs run0 ⁻¹' A) ≤ μB (obs run1 ⁻¹' A) +
      2 * ENNReal.ofReal ((1 : ℝ) / 2 ^ 64) := by
  intro obs
  have h0 := (BatchOblivious31 1 le_rfl N0 g run0 (syncSchedule c1) 8 c1.levels
    setting0 μB Prod.fst Prod.snd (fun ω => words0 ω.1) tape0 (obs run0) id
    (measurable_of_countable _) measurable_id (fun _ _ => rfl) A hA).1
  have h1 := (BatchOblivious31 1 le_rfl N0 g run1 (syncSchedule c1) 8 c1.levels
    setting1 μB Prod.fst Prod.snd (fun ω => words0 ω.1) tape0 (obs run1) id
    (measurable_of_countable _) measurable_id (fun _ _ => rfl) A hA).2
  rw [sim_same] at h0
  simp only [Nat.cast_one, one_mul] at h0 h1
  set ε := ENNReal.ofReal ((1 : ℝ) / 2 ^ 64)
  set M := (simLaw c1 (slotSchedule (widths run1) (syncSchedule c1))
    (OnlineBatch.probePattern run1) 8 c1.levels).map id A
  calc μB (obs run0 ⁻¹' A) ≤ M + ε := h0
    _ ≤ (μB (obs run1 ⁻¹' A) + ε) + ε := by gcongr
    _ = μB (obs run1 ⁻¹' A) + 2 * ε := by rw [add_assoc, two_mul]

end Batch
end Online31Witness

#print axioms Online31Witness.applied
#print axioms Online31Witness.applied_junk
#print axioms Online31Witness.scalar512
#print axioms Online31Witness.scalar_init
#print axioms Online31Witness.Batch.applied
#print axioms Online31Witness.Batch.duplicate
#print axioms Online31Witness.Batch.tombstone

#print axioms Online31Witness.real512
#print axioms Online31Witness.dummy112

#print axioms Online31Witness.Batch.sim_same
#print axioms Online31Witness.Batch.dup_hidden
