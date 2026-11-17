import RebuildBound.Spec.HierarchyChunk
import RebuildBound.Spec.OnlineBase

/-!
# Obliviousness of the online layer (trusted statements)

For a fixed run (the
operations and the records they insert, the initialization's input, the
unshadowed flags) and a public plan schedule, the adversary's view — the bucket
each operation touches in each hashed table (`Model.Online.view`) — has, on the
ideal tape, exactly the law of the simulator, which reads only the schedule
and which operations probe (`OnlineExact`). Any observation that agrees with
the model's view on every outcome without a capacity failure is within the
failure probability of the simulator (`OnlineFailureFor`). The supported
`geometry31` numerical endpoint is `OnlineOblivious31`, with error at most
`h · 2^-64` over `h` chunks of `2^32` accesses. Two runs with the same schedule, probe pattern and
observation encoding `ι` therefore have observations within twice that
distance. That the engine's observation is such an observation is a
hypothesis of the theorems, not proved here: the view replay supports it.

**Premises.**
* `OnlineRunPremises`: the online geometry matches the configuration, the run
  fits the horizon, its keys lie below `N`, its trace meets `TracePremises`
  and the unshadowed promise holds.
* `SchedulePremises`: every plan reads only consumed prefixes, its tables are
  valid coordinates, at most one is a top, and their windows tile the consumed
  positions in cascade order. `syncSchedule` meets them (`SyncSchedule`).
* `OnlineTapePremises`: the family tape and the dummy tape are jointly
  uniform, and the model's words agree with the family tape. The dummy tape
  idealises the engine's AES dummy words (a never-repeating counter under the
  family's dummy nonce), as the family tape idealises its routing words.
* The observation agrees with the view off failure (a hypothesis of
  `OnlineFailureFor` and `OnlineObliviousFor`).
The schedule is a public input. That the engine's plan schedule does not
depend on the words is a fact about the engine, established by reading its
code (`Spec/Model/ENGINE_ONLINE.md`, section 1.3) and supported by the
two-secret replays of `oracle/`. The rebuild jobs' memory traces depend only
on public geometry (fixed work, masked kernels; the engine's instruction-census
and protected-page tests are the evidence); they are not part of the view. At an
initialized configuration the premises admit a trace with `init = []`; the
engine then starts empty and the model does not, so the agreement hypothesis
fails and the theorems say nothing about the engine there.

**Plan.** `OnlinePattern` (the real/dummy pattern does not depend on the
words), `OnlineFresh` (every real probe reads a distinct family-tape word),
`OnlineExact` (the exact law, from the two), `HierarchyChunkPartition` (the
chunk events partition the failures), and the generic failure and numerical
transfers. Selected configuration specializations are retained as internal
proof infrastructure; the public endpoints are in `Spec/Oblivious31.lean`.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online

/-! ### The real/dummy pattern and fresh real words -/

/-- Everything the online statements assume at one configuration. -/
def OnlineSettingFor (geo : HierarchyGeometry) (N : Nat) (g : OnlineGeom) (run : OnlineRun)
    (S : Schedule) (n m : Nat) : Prop :=
  N ≤ geo.keyCapacity ∧ n ≤ run.ops.length ∧
    OnlineRunPremises geo.cfg geo.shapes N g run ∧ SchedulePremises geo.cfg S n m

/-- Original selected-geometry specialization. -/
def OnlineSetting (cfg : Config) (rows : List (SepGeom × Nat)) (N : Nat) (g : OnlineGeom) (run : OnlineRun)
    (S : Schedule) (n m : Nat) : Prop :=
  OnlineSettingFor (HierarchyGeometry.selected cfg rows) N g run S n m

/-- A property at both selected configurations, at every horizon of a
positive number of chunks. -/
def SelectedOnline (P : Config → List (SepGeom × Nat) → Prop) : Prop :=
  SelectedChunks P

/-- The pattern does not depend on the words, at every entry of a plan. -/
def OnlinePatternFor (geo : HierarchyGeometry) : Prop :=
  ∀ N g run S n m, OnlineSettingFor geo N g run S n m →
    ∀ (words words' : Words) j i, j < n → i < (S j).tables.length →
      isReal geo.cfg geo.shapes g run S words j i =
        isReal geo.cfg geo.shapes g run S words' j i

/-- Original selected-geometry specialization. -/
def OnlinePatternAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  OnlinePatternFor (HierarchyGeometry.selected cfg rows)

/-- **OnlinePattern**: which plan entries get real buckets depends only on
the run and the schedule. -/
def OnlinePattern_statement : Prop := SelectedOnline OnlinePatternAt

/-- Every real probe at an entry of a plan reads a word of the family tape (a
coordinate of the horizon, a key below `N`), and no two real probes read the
same one. (`isReal` past a plan's end is not a probe.) -/
def OnlineFreshFor (geo : HierarchyGeometry) : Prop :=
  ∀ N g run S n m, OnlineSettingFor geo N g run S n m → ∀ (words : Words),
    (∀ j i, j < n → i < (S j).tables.length →
      isReal geo.cfg geo.shapes g run S words j i = true →
      ∃ c o, (S j).tables[i]? = some c ∧ run.ops[j]? = some o ∧
        familyOf geo.cfg c.1 c.2 ∈ geo.cfg.coordinates ∧ o.record.key.toNat < N) ∧
    ∀ j i j' i' c c' o o', j < n → i < m → j' < n → i' < m → (j, i) ≠ (j', i') →
      isReal geo.cfg geo.shapes g run S words j i = true →
      isReal geo.cfg geo.shapes g run S words j' i' = true →
      (S j).tables[i]? = some c → (S j').tables[i']? = some c' →
      run.ops[j]? = some o → run.ops[j']? = some o' →
      (familyOf geo.cfg c.1 c.2, o.record.key) ≠ (familyOf geo.cfg c'.1 c'.2, o'.record.key)

/-- Original selected-geometry specialization. -/
def OnlineFreshAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  OnlineFreshFor (HierarchyGeometry.selected cfg rows)

/-- **OnlineFresh**: at most one real probe per family and key. -/
def OnlineFresh_statement : Prop := SelectedOnline OnlineFreshAt

/-! ### The exact law -/

/-- The view's law is the simulator's. -/
def OnlineExactFor (geo : HierarchyGeometry) : Prop :=
  ∀ N g run S n m, OnlineSettingFor geo N g run S n m →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape geo.cfg N) (dtape : Ω → DummyTape n m) (words : Ω → Words),
      OnlineTapePremises geo.cfg N n m μ tape dtape words →
      μ.map (fun ω => view geo.cfg geo.shapes g run S n m (words ω) (dummyOf (dtape ω))) =
        simLaw geo.cfg S (probePattern run) n m

/-- Original selected-geometry specialization. -/
def OnlineExactAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  OnlineExactFor (HierarchyGeometry.selected cfg rows)

/-- **OnlineExact**: on the ideal tape the model's view is exactly the
simulator's, whatever the run. Conditional on the pattern and freshness
statements, which it takes as hypotheses (proved separately). -/
def OnlineExact_statement : Prop :=
  OnlinePattern_statement → OnlineFresh_statement → SelectedOnline OnlineExactAt

/-! ### The chunk partition -/

/-- The failures within `h ≥ 1` chunks are the first failures of the chunks
`k < h`. -/
def HierarchyChunkPartitionAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  ∀ (h : Nat) (tr : Trace) (words : Words), 1 ≤ h →
    (Fails (chunkConfig cfg h) (hierarchyShapes (chunkConfig cfg h) rows) tr words ↔
      ∃ k < h, ChunkFails cfg (hierarchyShapes (chunkConfig cfg h) rows) tr words k)

/-- **HierarchyChunkPartition**: the chunk events partition `Fails`. -/
def HierarchyChunkPartition_statement : Prop := SelectedAt HierarchyChunkPartitionAt

/-! ### Failures and the numerical bound -/

/-- Any observation that equals (an image of) the model's view on every
outcome without a capacity failure has, on every measurable set, the
simulator's probability up to the failure probability. -/
def OnlineFailureFor (geo : HierarchyGeometry) : Prop :=
  ∀ N g run S n m, OnlineSettingFor geo N g run S n m →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape geo.cfg N) (dtape : Ω → DummyTape n m) (words : Ω → Words),
      OnlineTapePremises geo.cfg N n m μ tape dtape words →
      ∀ {V : Type} [MeasurableSpace V] (obs : Ω → V) (ι : (Fin n → Fin m → Nat) → V),
        Measurable obs → Measurable ι →
        (∀ ω, ¬ Fails geo.cfg geo.shapes (traceOf g run) (words ω) →
          obs ω = ι (view geo.cfg geo.shapes g run S n m (words ω) (dummyOf (dtape ω)))) →
        ∀ A : Set V, MeasurableSet A →
          μ (obs ⁻¹' A) ≤ (simLaw geo.cfg S (probePattern run) n m).map ι A +
              μ {ω | Fails geo.cfg geo.shapes (traceOf g run) (words ω)} ∧
            (simLaw geo.cfg S (probePattern run) n m).map ι A ≤ μ (obs ⁻¹' A) +
              μ {ω | Fails geo.cfg geo.shapes (traceOf g run) (words ω)}

/-- Original selected-geometry specialization. -/
def OnlineFailureAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  OnlineFailureFor (HierarchyGeometry.selected cfg rows)

/-- **OnlineFailure**: every observation that agrees with the view off failure
is within the failure probability of the simulator. Conditional on
`OnlineExact` and the two statements it uses (proved separately). -/
def OnlineFailure_statement : Prop :=
  OnlinePattern_statement → OnlineFresh_statement → OnlineExact_statement →
    SelectedOnline OnlineFailureAt

/-- The numerical form over `h` chunks of `2^32` accesses. -/
def OnlineObliviousFor (geo : HierarchyGeometry) (error : ℝ≥0∞) : Prop :=
  ∀ (h : Nat), 1 ≤ h →
    let current := geo.chunk h
    let c := current.cfg
    ∀ N g run S n m, OnlineSettingFor current N g run S n m →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (tape : Ω → FamilyTape c N) (dtape : Ω → DummyTape n m) (words : Ω → Words),
        OnlineTapePremises c N n m μ tape dtape words →
        ∀ {V : Type} [MeasurableSpace V] (obs : Ω → V) (ι : (Fin n → Fin m → Nat) → V),
          Measurable obs → Measurable ι →
          (∀ ω, ¬ Fails c current.shapes (traceOf g run) (words ω) →
            obs ω = ι (view c current.shapes g run S n m (words ω) (dummyOf (dtape ω)))) →
          ∀ A : Set V, MeasurableSet A →
            μ (obs ⁻¹' A) ≤ (simLaw c S (probePattern run) n m).map ι A +
                (h : ℝ≥0∞) * error ∧
              (simLaw c S (probePattern run) n m).map ι A ≤ μ (obs ⁻¹' A) +
                (h : ℝ≥0∞) * error

/-! ### The synchronous schedule meets the premises -/

/-- **SyncSchedule**: the synchronous storage mode's schedule meets the
schedule premises with plans of `L` tables, for every run within the horizon. -/
def SyncSchedule_statement : Prop :=
  ∀ cfg rows, (cfg, rows) = (uniformConfig, uniformSeparated) ∨
    (cfg, rows) = (halfFanoutConfig, halfFanoutSeparated) →
    ∀ h n, 1 ≤ h → SchedulePremises (chunkConfig cfg h) (syncSchedule (chunkConfig cfg h)) n
      (chunkConfig cfg h).levels

end RebuildBound.Spec
