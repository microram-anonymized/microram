import spec_tests.FixtureKeys
import RebuildBound.Proofs.HierarchySemantics
import RebuildBound.Proofs.SyncSchedule

/-! The generic replay argument applies outside the numerical family: this
one-page, two-level hierarchy has top digit four and capacity 1024. The same
finite structural checks and exact law work from both starts. The two-probe
client chooses its second key from its first observed bucket. No family
manifest or numerical capacity certificate is imported or assumed. -/

open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.Adaptive
open RebuildBound.HierarchyInvariantProof

namespace AdaptiveSemanticsTest

/-- The only direct digits are one and two, with four and eight output homes. -/
def direct (d : Nat) : DirectJob.Geometry :=
  ⟨2, d, d * 4, 64, if d = 1 then 0 else 64, 64, 64, 64, 64, .direct⟩

def geometry (initialized : Bool) : HierarchyGeometry :=
  let cfg : Config := ⟨[2], 4, 4, 32, 2 ^ 32, initialized⟩
  let top : TopGeom := ⟨64, 3, 2, 2, 3, true, 1, 1, 1, 1⟩
  let prep : TPGeom := ⟨64, 5, 1, 1, 1, 2, 3, true⟩
  ⟨cfg, [], top, prep, prep, 32 * top.T, direct⟩

example (initialized : Bool) : (geometry initialized).cfg.levels = 2 ∧
    (geometry initialized).cfg.topDigit = 4 ∧
    (geometry initialized).keyCapacity = 1024 := by
  cases initialized <;> decide +kernel

theorem low (initialized : Bool) :
    LowFacts (geometry initialized).cfg (geometry initialized).rows (geometry initialized).direct := by
  cases initialized <;> apply lowFacts_of <;> decide +kernel

theorem top (initialized : Bool) : (geometry initialized).TopCompatible := by
  cases initialized <;> decide +kernel

/-- The public contract is decidable from geometry alone, for either start. -/
theorem structural (initialized : Bool) : (geometry initialized).Structural := by
  cases initialized <;> decide +kernel

/-- The public generic endpoint supplies the adaptive law outside the family. -/
theorem exactFor (initialized : Bool) : AdaptiveExactFor (geometry initialized) :=
  (HierarchyAdaptiveSemantics _ (structural initialized)).1

example (initialized : Bool) : OnlineLookupFor (geometry initialized) ∧
    BatchLookupFor (geometry initialized) := HierarchyLookup _ (structural initialized)

example (initialized : Bool) : UniverseOnlineLookupFor (geometry initialized) ∧
    UniverseBatchLookupFor (geometry initialized) :=
  HierarchyUniverseLookup _ (structural initialized)

example (initialized : Bool) : AdaptiveFailureFor (geometry initialized) :=
  (HierarchyAdaptiveSemantics _ (structural initialized)).2

def U : Finset LogicalKey := fixtureKeys (Finset.range 3)
def online : OnlineGeom := ⟨64, 2⟩

def client : Client 2 := fun rows _ =>
  if rows.isEmpty then ⟨LogicalKey.ofNat (2), 7, false⟩
  else ⟨LogicalKey.ofNat ((rows.headD fun _ => 0) 0 % 2), 9, false⟩

def run : AdaptiveRun 2 := ⟨[.probe, .probe], [], fun _ => false, client⟩

example : slotCount run.shape = 2 := by decide +kernel
example : LogicalKey.toNat (client [fun _ => 0] 0).key = 0 ∧ LogicalKey.toNat (client [fun _ => 1] 0).key = 1 := by decide +kernel
example (initialized : Bool) : (geometry initialized).cfg.initialized = false → run.init = [] :=
  fun _ => rfl

theorem client_keys (rows : List (Fin 2 → Nat)) (i : Nat) : (client rows i).key ∈ U := by
  simp only [U, mem_fixtureKeys, Finset.mem_range, client]
  split_ifs <;> simp only [LogicalKey.toNat_ofNat]
  · decide +kernel
  · have := Nat.mod_lt ((rows.headD fun _ => 0) 0) (by decide +kernel : 0 < 2)
    omega

/-- Every possible transcript satisfies the same run setting and public schedule. -/
theorem setting (initialized : Bool) :
    AdaptiveSetting (geometry initialized) U online run (syncSchedule (geometry initialized).cfg) 2 := by
  apply AdaptiveAdmissible
  · intro k hk
    have : LogicalKey.toNat k < 3 := by simpa [U] using hk
    omega
  · change U.card ≤ 1024
    decide +kernel
  · rfl
  · decide +kernel
  · change 2 ≤ 2 ^ 32
    decide +kernel
  · decide +kernel
  · simp [run]
  · exact client_keys
  · intro r; rfl
  · exact SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ b ∈ ([2] : List Nat), 0 < b; decide +kernel)
      (by change 0 < 128; decide +kernel) 2

/-- Actual interactions, not only hypothetical branches, issue different keys. -/
example (initialized : Bool) :
    (OnlineBatch.slots (realized (geometry initialized).cfg (geometry initialized).shapes
      online (syncSchedule (geometry initialized).cfg) run (fun _ _ _ => 0) (fun _ _ => 0))).map
        (fun s => LogicalKey.toNat s.record.key) = [2, 0] ∧
    (OnlineBatch.slots (realized (geometry initialized).cfg (geometry initialized).shapes
      online (syncSchedule (geometry initialized).cfg) run (fun _ _ _ => 1) (fun _ _ => 0))).map
        (fun s => LogicalKey.toNat s.record.key) = [2, 1] := by
  cases initialized <;> decide +kernel

abbrev Ω (initialized : Bool) := UniverseTape (geometry initialized).cfg U × DummyTape 2 2
noncomputable abbrev μ (initialized : Bool) : MeasureTheory.Measure (Ω initialized) :=
  ProbabilityTheory.uniformOn Set.univ

def words (initialized : Bool) (ω : Ω initialized) : Words :=
  AdaptiveAssembly.uTapeWords (geometry initialized).cfg U 2 2 ω

/-- The canonical joint uniform tape discharges the probability-model premise. -/
theorem tape (initialized : Bool) : UniverseOnlineTapePremises (geometry initialized).cfg U 2 2
    (μ initialized) Prod.fst Prod.snd (words initialized) where
  measurable := measurable_id
  uniform := MeasureTheory.Measure.map_id
  agree := by
    intro ω p k
    simp [words, AdaptiveAssembly.uTapeWords, p.2, k.2]

/-- Both starts have an actual adaptive transcript with exactly the simulator law. -/
theorem exactLaw (initialized : Bool) :
    Measurable (fun ω : Ω initialized =>
      transcript (geometry initialized).cfg (geometry initialized).shapes online
        (syncSchedule (geometry initialized).cfg) run 2 (words initialized ω) (dummyOf ω.2)) ∧
    (μ initialized).map (fun ω : Ω initialized =>
      transcript (geometry initialized).cfg (geometry initialized).shapes online
        (syncSchedule (geometry initialized).cfg) run 2 (words initialized ω) (dummyOf ω.2)) =
      simLaw (geometry initialized).cfg
        (OnlineBatch.slotSchedule (shapeWidths run.shape) (syncSchedule (geometry initialized).cfg))
        (shapePattern run.shape) 2 2 :=
  exactFor initialized U online 2 run (syncSchedule (geometry initialized).cfg) 2
    (setting initialized) (μ initialized) Prod.fst Prod.snd (words initialized) (tape initialized)

end AdaptiveSemanticsTest
