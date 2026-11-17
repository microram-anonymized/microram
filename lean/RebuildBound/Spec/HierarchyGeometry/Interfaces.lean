import RebuildBound.Spec.HierarchyChunk

/-! Geometry-parametric hierarchy contracts and probability interfaces.
Concrete 31 statements re-export these definitions without changing them.

The selected-configuration level-one and covering interfaces below use the
`cycleUnits` / `CycleStuck` model and its 512-record bound. The completed family
proof uses the general direct-geometry and first-failure interfaces instead;
these selected-configuration interfaces do not restrict its smaller direct jobs. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec
open Model Model.DirectJob Model.Hierarchy

/-- Structural contracts under the instance's key-universe bound. -/
def HierarchyInvariantFor (g : HierarchyGeometry) : Prop :=
  ∀ (N : Nat) (tr : Trace), N ≤ g.keyCapacity → TracePremises g.cfg N tr →
    UnshPromise g.cfg g.shapes tr →
    ∀ words : Words, JobContracts g.cfg g.shapes tr N words

/-- Word locality and exclusion of the current family from the previous cone. -/
def HierarchyLocalityFor (cfg : Config) (sh : Shapes) : Prop :=
  (∀ (tr : Trace) (words words' : Words) (ℓ v : Nat),
    AgreeOnCone cfg sh tr words words' ℓ v →
    table cfg sh tr words ℓ v =
      table cfg sh tr words' ℓ v) ∧
  (∀ ℓ v, 1 ≤ ℓ → ℓ ≤ cfg.levels → cfg.seed ℓ < v →
    ∀ q ∈ cone cfg ℓ (v - 1), familyOf cfg q.1 q.2 ≠ familyOf cfg ℓ v)

/-- Separated job laws with their exact finite-word old-home density bound. -/
def HierarchySepLawFor (geo : HierarchyGeometry) : Prop :=
  ∀ (N : Nat) (tr : Trace), N ≤ geo.keyCapacity → TracePremises geo.cfg N tr →
    UnshPromise geo.cfg geo.shapes tr →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape geo.cfg N) (words : Ω → Words),
      TapePremises geo.cfg N μ tape words →
      ∀ ℓ o g, JobId.ordinary ℓ o ∈ geo.cfg.potentialJobs → 2 ≤ ℓ →
        geo.cfg.sepRow geo.rows ℓ (Config.digitOf (geo.cfg.fanout ℓ) o) = some g →
        ∃ (L : SJobLaw g) (D : ℝ≥0) (sample : Ω → L.toFinite.Outcome),
          SInputLaw L 32 D ∧ L.W = 64 ∧ D ≤ g.oldDensity 64 (32 * ((g.d - 1) * g.U)) ∧
          FiniteCoupling μ L.toFinite sample ∧
          jobEvent geo.cfg geo.shapes tr words (.ordinary ℓ o) ⊆
            {ω | sepFailEvent L (sample ω).1 (L.wordFn (sample ω).2)}

/-- Finish, preparation and initialization laws at their actual geometries. -/
def HierarchyTopLawFor (geo : HierarchyGeometry) : Prop :=
  ∀ (N : Nat) (tr : Trace), N ≤ geo.keyCapacity → TracePremises geo.cfg N tr →
    UnshPromise geo.cfg geo.shapes tr →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape geo.cfg N) (words : Ω → Words),
      TapePremises geo.cfg N μ tape words →
      (∀ o, JobId.topFinish o ∈ geo.cfg.potentialJobs →
        ∃ (L : TopJobLaw geo.top) (unsh : Rec → Bool) (sample : Ω → L.toFinite.Outcome),
          TopLaw L unsh 32 ∧ FiniteCoupling μ L.toFinite sample ∧
          jobEvent geo.cfg geo.shapes tr words (.topFinish o) ⊆
            {ω | topFailEvent L unsh (sample ω).1 (L.wordFn (sample ω).2)}) ∧
      (∀ o, JobId.topPrepare o ∈ geo.cfg.potentialJobs →
        ∃ (L : TPJobLaw geo.prep) (unsh : Rec → Bool) (sample : Ω → L.toFinite.Outcome),
          TPLaw L 32 1 ∧ FiniteCoupling μ L.toFinite sample ∧
          jobEvent geo.cfg geo.shapes tr words (.topPrepare o) ⊆
            {ω | tpFailEvent L engineRule unsh (sample ω).1 (L.wordFn (sample ω).2)}) ∧
      (JobId.initialization ∈ geo.cfg.potentialJobs →
        ∃ (L : TPJobLaw geo.init) (input : List Rec) (sample : Ω → L.toFinite.Outcome),
          InitLaw L input ∧ FiniteCoupling μ L.toFinite sample ∧
          jobEvent geo.cfg geo.shapes tr words .initialization ⊆
            {ω | tpFailEvent L engineRule (fun _ => false) (sample ω).1 (L.wordFn (sample ω).2)})

/-- Level-one cycle projections under an explicit key-universe capacity. -/
def HierarchyLevelOneFor (cfg : Config) (keyCapacity : Nat) : Prop :=
  ∀ (N : Nat) (tr : Trace), N ≤ keyCapacity → TracePremises cfg N tr →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape cfg N) (words : Ω → Words),
      TapePremises cfg N μ tape words →
      ∃ cycTape : ∀ c, Ω → CycleTape (cycleUnits cfg tr c).units,
        (∀ c < cfg.levelOneCycles, (cycleUnits cfg tr c).n ≤ cfg.cycleLength c) ∧
        (∀ c < cfg.levelOneCycles, ∀ j, ∀ u ∈ (cycleUnits cfg tr c).units j,
          (u.recs.map Rec.key).Nodup) ∧
        (∀ c < cfg.levelOneCycles, ∀ j, (unitKeys ((cycleUnits cfg tr c).units j)).card ≤ 512) ∧
        (∀ c < cfg.levelOneCycles, Measurable (cycTape c) ∧
          μ.map (cycTape c) =
            ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape (cycleUnits cfg tr c).units))) ∧
        (∀ c < cfg.levelOneCycles, ∀ j ω k (hk : k ∈ cycleKeys (cycleUnits cfg tr c).units j),
          cycleNative cfg c j (words ω) k = cycTape c ω j ⟨k, hk⟩)

/-- A failing execution has a failing job above level one whose input tiers
fit, or a level-one cycle that does not publish. -/
def HierarchyCoveringFor (g : HierarchyGeometry) : Prop :=
  ∀ (tr : Trace) (words : Words), Fails g.cfg g.shapes tr words →
    (∃ j ∈ g.cfg.potentialJobs, (∀ o, j ≠ .ordinary 1 o) ∧ WithinHorizon g.cfg j ∧
      jobTiersFit g.cfg g.shapes tr words j ∧
      jobFails g.cfg g.shapes tr words j = true) ∨
    ∃ c < g.cfg.levelOneCycles, CycleStuck g.cfg tr words c

/-- Failure probability under a fixed trace and an ideal family tape. -/
def HierarchyUniformFor (geo : HierarchyGeometry) (error : ℝ≥0∞) : Prop :=
  ∀ (N : Nat) (tr : Trace), N ≤ geo.keyCapacity → TracePremises geo.cfg N tr →
    UnshPromise geo.cfg geo.shapes tr →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape geo.cfg N) (words : Ω → Words),
      TapePremises geo.cfg N μ tape words →
      μ {ω | Fails geo.cfg geo.shapes tr (words ω)} ≤ error

/-- First-failure covering after an arbitrary failure-free prefix. -/
def HierarchyCoveringFromFor (geo : HierarchyGeometry) : Prop :=
  ∀ (tr : Trace) (words : Words) (T : Nat),
    Fails geo.cfg geo.shapes tr words →
    (∀ j ∈ geo.cfg.potentialJobs, jobTime geo.cfg j ≤ T →
      jobFails geo.cfg geo.shapes tr words j = false) →
    (∃ j ∈ geo.cfg.potentialJobs, (∀ o, j ≠ .ordinary 1 o) ∧ WithinHorizon geo.cfg j ∧
      T < jobTime geo.cfg j ∧ jobTiersFit geo.cfg geo.shapes tr words j ∧
      jobFails geo.cfg geo.shapes tr words j = true) ∨
    ∃ c < geo.cfg.levelOneCycles,
      (∃ i < geo.cfg.cycleLength c, T < geo.cfg.cycleOrdinal c i) ∧
      CycleStuck geo.cfg tr words c

/-- The unconditional probability of a first failure in any fixed chunk. -/
def HierarchyChunkFor (geo : HierarchyGeometry) (error : ℝ≥0∞) : Prop :=
  ∀ (k N : Nat) (tr : Trace), N ≤ geo.keyCapacity →
    TracePremises (chunkConfig geo.cfg (k + 1)) N tr →
    UnshPromise (chunkConfig geo.cfg (k + 1)) (geo.chunk (k + 1)).shapes tr →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape (chunkConfig geo.cfg (k + 1)) N) (words : Ω → Words),
      TapePremises (chunkConfig geo.cfg (k + 1)) N μ tape words →
      μ {ω | ChunkFails geo.cfg (geo.chunk (k + 1)).shapes tr (words ω) k} ≤ error

/-- Failure within a positive number of chunks, from premises at that horizon. -/
def HierarchyWindowsFor (geo : HierarchyGeometry) (error : ℝ≥0∞) : Prop :=
  ∀ (h N : Nat) (tr : Trace), 1 ≤ h → N ≤ geo.keyCapacity →
    TracePremises (chunkConfig geo.cfg h) N tr →
    UnshPromise (chunkConfig geo.cfg h) (geo.chunk h).shapes tr →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape (chunkConfig geo.cfg h) N) (words : Ω → Words),
      TapePremises (chunkConfig geo.cfg h) N μ tape words →
      μ {ω | Fails (chunkConfig geo.cfg h) (geo.chunk h).shapes tr (words ω)} ≤
        (h : ℝ≥0∞) * error

end RebuildBound.Spec
