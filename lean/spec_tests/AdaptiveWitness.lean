import spec_tests.FixtureKeys
import RebuildBound.Proofs.Adaptive

/-!
# Non-vacuity of the adaptive setting at `geometry31.chunk 1`

A client over six slots near the largest 64-bit key: an absent key (a real
top probe), then a chunk whose first and third lanes take a key chosen by the
parity of the first observed bucket (so the third lane is a duplicate), with
a tombstone of the initialized key between them, a blind write and a repeated
key (a dense hit, so a dummy probe). Under two word tapes the client issues
different runs. The kernel evaluates the interaction, row causality, the
replay identity and the real/dummy pattern on this instance, and
`AdaptiveSetting` holds for every candidate transcript: the headline premises
are satisfiable by a client that actually adapts. On the canonical joint
uniform tape, `AdaptiveExact31`, `AdaptiveWindows31` and `AdaptiveOblivious31`
then apply with every premise discharged.

No unit freezes in six slots, so the trace premises hold by computation;
`AdaptiveAdmissible` covers longer runs. Every plan below 512 slots is the top
alone, so this instance exposes the top family only; `spec_tests/Adaptive.lean`
runs a tiny configuration whose plans hold level-one tables.
-/

open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.OnlineBatch RebuildBound.Model.Adaptive

namespace AdaptiveWitness

abbrev high : Nat := 2 ^ 64 - 1000
def U : Finset LogicalKey := fixtureKeys (Finset.Ico high (high + 100))
abbrev c1 : Config := (geometry31.chunk 1).cfg
def g : OnlineGeom := ⟨64, 8⟩
abbrev m0 : Nat := c1.levels
abbrev n0 : Nat := 6

/-- The second operation's keys depend on the parity of the first bucket. -/
def client : Client m0 := fun rows i =>
  let b := (rows.headD fun _ => 0) ⟨0, by decide +kernel⟩ % 2
  match rows.length, i with
  | 0, _ => ⟨LogicalKey.ofNat (high + 50), 1, false⟩
  | 1, 0 => ⟨LogicalKey.ofNat (high + 1 + b), 2, false⟩
  | 1, 1 => ⟨LogicalKey.ofNat (high), 3, true⟩
  | 1, _ => ⟨LogicalKey.ofNat (high + 1 + b), 4, false⟩
  | 4, _ => ⟨LogicalKey.ofNat (high + 50), 5, false⟩
  | _, _ => ⟨LogicalKey.ofNat (high + 50), 6, false⟩

def adv : AdaptiveRun m0 :=
  ⟨[.probe, .chunk 3, .blind, .probe], [⟨LogicalKey.ofNat (high), 9000, false⟩], fun _ => false, client⟩

def words1 : Words := fun l v k => LogicalKey.toNat k * 3 + l + v
def words2 : Words := fun l v k => LogicalKey.toNat k * 3 + l + v + 1
def dummy0 : Nat → Nat → Nat := fun t i => 1000 + t + i

def T (w : Words) : Fin n0 → Fin m0 → Nat :=
  transcript c1 (geometry31.chunk 1).shapes g (syncSchedule c1) adv n0 w dummy0
def R (w : Words) : BatchRun :=
  realized c1 (geometry31.chunk 1).shapes g (syncSchedule c1) adv w dummy0
def rowsL (t : Fin n0 → Fin m0 → Nat) : List (List Nat) :=
  (List.finRange n0).map fun s => (List.finRange m0).map (t s)
def keysOf (run : BatchRun) : List Nat := (OnlineBatch.slots run).map fun s => LogicalKey.toNat s.record.key - high

set_option maxRecDepth 100000

/-- The client adapts: the two tapes give different runs. -/
example : keysOf (R words1) = [50, 1, 0, 1, 50, 50] := by decide +kernel
example : keysOf (R words2) = [50, 2, 0, 2, 50, 50] := by decide +kernel

/-- Row causality on this instance: the transcript is the realized run's view. -/
example : rowsL (T words1) = rowsL (OnlineBatch.view c1 (geometry31.chunk 1).shapes g (R words1)
    (syncSchedule c1) n0 m0 words1 dummy0) := by decide +kernel

/-- The replay identity on this instance. -/
example : keysOf (replay adv (T words1)) = keysOf (R words1) := by decide +kernel

/-- Real, real, real, a duplicate lane's dummy, a blind write, a dense hit's dummy. -/
example : (List.range n0).map (fun s => OnlineBatch.isReal c1 (geometry31.chunk 1).shapes g
    (R words1) (syncSchedule c1) words1 s 0) = [true, true, true, false, false, false] := by
  decide +kernel

theorem U_card : U.card = 100 := by decide +kernel

theorem client_U : ∀ rows i, (client rows i).key ∈ U := by
  intro rows i
  have hb := Nat.mod_lt ((rows.headD fun _ => 0) ⟨0, by decide +kernel⟩) (by decide +kernel : 0 < 2)
  rw [U, mem_fixtureKeys, Finset.mem_Ico]; unfold client
  split <;> simp only [LogicalKey.toNat_ofNat] <;> constructor <;> omega

theorem slots_replay (t : Fin n0 → Fin m0 → Nat) : OnlineBatch.slots (replay adv t) =
    [⟨0, 0, client (rowsOf t 0) 0, true⟩, ⟨1, 0, client (rowsOf t 1) 0, true⟩,
     ⟨1, 1, client (rowsOf t 1) 1, true⟩, ⟨1, 2, client (rowsOf t 1) 2, true⟩,
     ⟨2, 0, client (rowsOf t 4) 0, false⟩, ⟨3, 0, client (rowsOf t 5) 0, true⟩] := by
  simp [OnlineBatch.slots, replay, replayOps, adv, Kind.op, Kind.width, OnlineBatch.Op.lanes,
    List.range_succ]

theorem frozen_nil (t : Fin n0 → Fin m0 → Nat) :
    (OnlineBatch.stateAt g (replay adv t) (replay adv t).ops.length).frozen = [] := by
  simp [OnlineBatch.stateAt, replay, replayOps, adv, Kind.op, Kind.width, Requester.run,
    Requester.step, Requester.insert, Requester.clearKey, OnlineBatch.Op.requester, g,
    List.range_succ]

/-- The adaptive setting, for every candidate transcript. -/
theorem setting : AdaptiveSetting (geometry31.chunk 1) U g adv (syncSchedule c1) n0 := by
  refine ⟨by decide +kernel, fun t => ?_⟩
  refine ⟨?_, ?_, ?_, ⟨⟨by decide +kernel, by decide +kernel⟩, ?_, ?_, ?_, ?_⟩, SyncSchedule31 1 n0 le_rfl⟩
  · intro k hk; simp only [U, mem_fixtureKeys, Finset.mem_Ico] at hk; norm_num [high] at hk ⊢; omega
  · rw [U_card]; decide +kernel
  · rw [slots_replay]; simp
  · rw [slots_replay]; simp [HierarchyGeometry.chunk, chunkConfig]
  · intro s hs; rw [slots_replay] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> exact client_U _ _
  · exact { nodup := by intro i u hu; simp [OnlineBatch.traceOf, frozen_nil] at hu
            load := by intro i; simp [OnlineBatch.traceOf, frozen_nil, DirectMasks.records]
            keys := by intro i x hx; simp [OnlineBatch.traceOf, frozen_nil, DirectMasks.records] at hx
            initNodup := by simp [OnlineBatch.traceOf, replay, adv]
            initKeys := by
              intro x hx; simp only [OnlineBatch.traceOf, replay, adv, List.mem_singleton] at hx
              subst x; simp [U] }
  · intro words o _ r _ h; simp [earlyDrop, OnlineBatch.traceOf, replay, adv] at h

/-- Actual high keys index the ideal tape. -/
def words0 (ω : UniverseTape c1 U) : Words := fun l v k =>
  if h : (l, v) ∈ c1.coordinates.toFinset then
    if hk : k ∈ U then ((ω ⟨(l, v), h⟩ ⟨k, hk⟩ : Fin (2 ^ 64)) : Nat) else 0
  else 0

abbrev Ω0 := UniverseTape c1 U × DummyTape n0 m0
noncomputable abbrev μ0 : MeasureTheory.Measure Ω0 := ProbabilityTheory.uniformOn Set.univ

theorem tape : UniverseOnlineTapePremises c1 U n0 m0 μ0 Prod.fst Prod.snd (fun ω => words0 ω.1) where
  measurable := by
    have h : (fun ω : Ω0 => (ω.1, ω.2)) = id := rfl
    rw [h]; exact measurable_id
  uniform := by
    have h : (fun ω : Ω0 => (ω.1, ω.2)) = id := rfl
    rw [h, MeasureTheory.Measure.map_id]
  agree := by
    intro ω p k
    obtain ⟨⟨a, b⟩, hp⟩ := p
    simp [words0, hp]

/-- The adaptive transcript is measurable and has the public simulator's law. -/
theorem exactLaw :
    Measurable (fun ω : Ω0 => transcript c1 (geometry31.chunk 1).shapes g (syncSchedule c1) adv n0
        (words0 ω.1) (dummyOf ω.2)) ∧
      μ0.map (fun ω : Ω0 => transcript c1 (geometry31.chunk 1).shapes g (syncSchedule c1) adv n0
        (words0 ω.1) (dummyOf ω.2)) =
        simLaw c1 (slotSchedule (shapeWidths adv.shape) (syncSchedule c1)) (shapePattern adv.shape)
          n0 m0 :=
  AdaptiveExact31 1 le_rfl U g m0 adv (syncSchedule c1) n0 setting μ0 Prod.fst Prod.snd
    (fun ω => words0 ω.1) tape

/-- The realized run's capacity failure has probability at most `2^-64`. -/
theorem windows :
    μ0 {ω : Ω0 | AdaptiveFails c1 (geometry31.chunk 1).shapes g (syncSchedule c1) adv (words0 ω.1)
      (dummyOf ω.2)} ≤ ENNReal.ofReal ((1 : ℝ) / 2 ^ 64) := by
  simpa only [Nat.cast_one, one_mul] using AdaptiveWindows31 1 le_rfl U g m0 adv (syncSchedule c1)
    n0 setting μ0 Prod.fst Prod.snd (fun ω => words0 ω.1) tape

/-- Agreement is required only off failure: this observation returns 7 on failure. -/
theorem oblivious_junk (A : Set (Fin n0 → Fin m0 → Nat)) :
    let obs : Ω0 → (Fin n0 → Fin m0 → Nat) := fun ω => by
      classical
      exact if AdaptiveFails c1 (geometry31.chunk 1).shapes g (syncSchedule c1) adv (words0 ω.1)
          (dummyOf ω.2)
        then fun _ _ => 7
        else transcript c1 (geometry31.chunk 1).shapes g (syncSchedule c1) adv n0 (words0 ω.1)
          (dummyOf ω.2)
    μ0 (obs ⁻¹' A) ≤
        (simLaw c1 (slotSchedule (shapeWidths adv.shape) (syncSchedule c1)) (shapePattern adv.shape)
          n0 m0).map id A + ENNReal.ofReal ((1 : ℝ) / 2 ^ 64) ∧
      (simLaw c1 (slotSchedule (shapeWidths adv.shape) (syncSchedule c1)) (shapePattern adv.shape)
          n0 m0).map id A ≤ μ0 (obs ⁻¹' A) + ENNReal.ofReal ((1 : ℝ) / 2 ^ 64) := by
  intro obs
  simpa only [Nat.cast_one, one_mul] using AdaptiveOblivious31 1 le_rfl U g m0 adv (syncSchedule c1)
    n0 setting μ0 Prod.fst Prod.snd (fun ω => words0 ω.1) tape obs id
    (measurable_of_countable _) measurable_id (fun ω h => by simp [obs, h]) A
    MeasurableSet.of_discrete

/-- `selSepBound` is its A terms plus its insertion and output term. -/
example (g : SepGeom) : selSepBound g = selSepABound g + selSepUBound g := rfl

end AdaptiveWitness

/-- info: 'AdaptiveWitness.setting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AdaptiveWitness.setting

/-- info: 'AdaptiveWitness.exactLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AdaptiveWitness.exactLaw

/-- info: 'AdaptiveWitness.windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AdaptiveWitness.windows

/-- info: 'AdaptiveWitness.oblivious_junk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AdaptiveWitness.oblivious_junk
