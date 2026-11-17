import RebuildBound.Spec.DirectJobCycleGeometry

/-! Geometry-local cycle composition. Structural validity, independent source
laws and numerical budgets remain separate premises; no probability statement
is hidden in the geometry contract. -/

open MeasureTheory
open scoped ENNReal
namespace RebuildBound.Spec
open Model Model.DirectJob

/-- The finite checks needed to adopt every successful ordinal into the next.
Only the first `n` digits are constrained. -/
structure DirectCycleGeometry (geometry : Nat → Geometry) (n : Nat) : Prop where
  first : 0 < n → (geometry 1).digit = 1
  valid : ∀ d, 1 ≤ d → d ≤ n → (geometry d).Valid
  next : ∀ d, 1 ≤ d → d < n →
    (geometry (d + 1)).K = (geometry d).K ∧
    (geometry (d + 1)).digit = (geometry d).digit + 1 ∧
    (geometry d).outputCapacity ≤ (geometry (d + 1)).aTierCapacity

/-- Capacity failure of ordinal `j`, with its actual published prefix. -/
def DirectCycleFailureAt {Ω : Type} (geometry : Nat → Geometry)
    (oldWord : Ω → LogicalKey → Nat) (steps : Ω → List ((LogicalKey → Nat) × List Bucket))
    (j : Nat) : Set Ω :=
  {ω | ∃ e step out, (steps ω)[j]? = some step ∧
    runChain (oldWord ω) emptyOutput
      (directChainJobs geometry 1 ((steps ω).take j)) = .published out ∧
    runJob (geometry (j + 1)) (selectedCycleOldWord (oldWord ω) (steps ω) j)
      step.1 (adopt out step.2) = .failed e}

/-- The first ordinal needs only a complete B population and its independent
64-bit word block. Its shape and numerical budget are supplied separately. -/
def DirectCycleDigitOneCoupled {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (capacity : Nat) (steps : Ω → List ((LogicalKey → Nat) × List Bucket)) : Prop :=
  ∃ (s : SepGeom) (L : SJobLaw s) (direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs)
    (sample : Ω → L.toFinite.Outcome),
    (∑ hist, L.weight hist = 1) ∧ L.W = 64 ∧
    (∀ hist hw, ((direct hist (L.wordFn hw)).bRecords.map Rec.key).toFinset = L.KB) ∧
    L.KB.card ≤ capacity ∧ FiniteCoupling μ L.toFinite sample ∧
    ∀ ω step, (steps ω)[0]? = some step →
      direct (sample ω).1 (L.wordFn (sample ω).2) = adopt emptyOutput step.2 ∧
      ∀ k ∈ L.KA ∪ L.KB, L.wordFn (sample ω).2 k = step.1 k

/-- Uniform cycle tapes supply the first block at the actual source capacity. -/
def DirectJobUniformCycleFirst_statement : Prop :=
  ∀ (n : Nat) (units : Fin n → List Bucket) (capacity : Nat),
    (∀ j, (unitKeys (units j)).card ≤ capacity) →
    ∀ [MeasurableSpace (CycleTape units)] [MeasurableSingletonClass (CycleTape units)]
      {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (π : Ω → CycleTape units),
    Measurable π → μ.map π = ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape units)) →
    ∀ native : Fin n → Ω → LogicalKey → Nat,
    (∀ j ω k (hk : k ∈ cycleKeys units j), native j ω k = π ω j ⟨k, hk⟩) →
    0 < n → DirectCycleDigitOneCoupled μ capacity (cycleStepsOn units native)

/-- Transport the first reached failure to its independent finite-word law. -/
def DirectJobCycleFirstBound_statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (geometry : Nat → Geometry) (capacity : Nat)
    (oldWord : Ω → LogicalKey → Nat) (steps : Ω → List ((LogicalKey → Nat) × List Bucket)),
    DirectCycleDigitOneCoupled μ capacity steps → ∀ bound : ℝ≥0∞,
    (∀ (s : SepGeom) (L : SJobLaw s) (direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs),
      (∑ hist, L.weight hist = 1) → L.W = 64 →
      (∀ hist hw, ((direct hist (L.wordFn hw)).bRecords.map Rec.key).toFinset = L.KB) →
      L.KB.card ≤ capacity →
      L.prob (fun hist word => ∃ e, runJob (geometry 1) (L.wOld hist) word
        (direct hist word) = .failed e) ≤ bound) →
    μ (DirectCycleFailureAt geometry oldWord steps 0) ≤ bound

/-- The common cycle union bound. Shape checks derive rejection-freedom;
local unconditional probability bounds may be shared across configurations. -/
def DirectJobCycleBound_statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (geometry : Nat → Geometry) (n : Nat), DirectCycleGeometry geometry n →
    ∀ (oldWord : Ω → LogicalKey → Nat) (steps : Ω → List ((LogicalKey → Nat) × List Bucket)),
    (∀ ω, (steps ω).length ≤ n) →
    (∀ ω, ∀ step ∈ steps ω, ∀ u ∈ step.2, (u.recs.map Rec.key).Nodup) →
    ∀ budget : Nat → ℝ≥0∞,
    (∀ j < n, μ (DirectCycleFailureAt geometry oldWord steps j) ≤ budget (j + 1)) →
    μ {ω | ¬ ∃ out, runChain (oldWord ω) emptyOutput
      (directChainJobs geometry 1 (steps ω)) = .published out} ≤
        ∑ j ∈ Finset.range n, budget (j + 1)

/-- A coupled later history consumes the same local bound used by a fixed or
adaptive source-law adapter. It is never conditioned on earlier success. -/
def DirectJobCycleLaterBound_statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (geometry : Nat → Geometry) (s : SepGeom) (load : Nat)
    (oldWord : Ω → LogicalKey → Nat) (steps : Ω → List ((LogicalKey → Nat) × List Bucket))
    (i : Nat), DirectCycleLaterCoupled μ geometry s load oldWord steps i →
    ∀ bound : ℝ≥0∞,
    (∀ data : DirectHistoryData, data.ValidFor s load →
      (data.lawFor (geometry (i + 1)) s).prob (fun hist word => ∃ e,
        runJob (geometry (i + 2)) ((data.lawFor (geometry (i + 1)) s).wOld hist) word
          (data.directFor (geometry (i + 1)) hist word) = .failed e) ≤ bound) →
    μ (DirectCycleFailureAt geometry oldWord steps (i + 1)) ≤ bound

end RebuildBound.Spec
