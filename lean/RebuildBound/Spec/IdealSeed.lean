import RebuildBound.Spec.IdealKeyLaw

/-! Independent client coins for the common ideal tape. These are mixture
adapters: seedwise laws and error bounds remain explicit premises until the
hierarchy's freshness and exposure proofs supply them. Public metadata and the
simulator law are fixed across seeds; initialization and requests may vary.
The tape always retains its product sigma algebra. -/
namespace RebuildBound.Spec
open Model MeasureTheory IdealKey
open scoped ENNReal

/-- The seed and the entire canonical tape have their independent product law. -/
def IdealSeedProbability_statement : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ],
    IsProbabilityMeasure (μ.prod tapeLaw) ∧
      (μ.prod tapeLaw).map Prod.fst = μ ∧ (μ.prod tapeLaw).map Prod.snd = tapeLaw

/-- Countable seeds of unbounded support need only measurable tape sections.
This is not a discrete-space assertion about the infinite tape. -/
def IdealSeedMeasurable_statement : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] [Countable Seed] [MeasurableSingletonClass Seed]
    (Value : Type) [MeasurableSpace Value] (observe : Seed → Tape → Value),
    (∀ seed, Measurable (observe seed)) → Measurable (Function.uncurry observe)

/-- Different seed slices can carry different error budgets and different
initial maps. No finite dictionary is shared across their executions. -/
def IdealSeedBound_statement : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (event : Set (Seed × Tape)), MeasurableSet event →
    ∀ bound : Seed → ℝ≥0∞,
    (∀ seed, tapeLaw (Prod.mk seed ⁻¹' event) ≤ bound seed) →
    (μ.prod tapeLaw) event ≤ ∫⁻ seed, bound seed ∂μ

/-- A fixed public simulator valid in every seed slice remains exact after
mixing. The stronger joint conclusion also makes the transcript independent
of the private seed. Joint measurability is an explicit obligation. -/
def IdealSeedExact_statement : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (Value : Type) [MeasurableSpace Value] (simulator : Measure Value)
    [IsProbabilityMeasure simulator] (observe : Seed → Tape → Value),
    Measurable (Function.uncurry observe) →
    (∀ seed, tapeLaw.map (observe seed) = simulator) →
    (μ.prod tapeLaw).map (fun p => (p.1, observe p.1 p.2)) = μ.prod simulator ∧
      (μ.prod tapeLaw).map (Function.uncurry observe) = simulator

/-- Unconditional coupling transfer after mixing independent client seeds.
The reference law and the seedwise bad-event bound are named hypotheses;
neither is inferred from capacity admissibility alone. -/
def IdealSeedFailure_statement : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (Value : Type) [MeasurableSpace Value] (simulator : Measure Value)
    [IsProbabilityMeasure simulator] (reference observed : Seed → Tape → Value)
    (bad : Set (Seed × Tape)),
    Measurable (Function.uncurry reference) →
    Measurable (Function.uncurry observed) → MeasurableSet bad →
    (∀ seed, tapeLaw.map (reference seed) = simulator) →
    (∀ seed tape, (seed, tape) ∉ bad → observed seed tape = reference seed tape) →
    ∀ bound : ℝ≥0∞, (∀ seed, tapeLaw (Prod.mk seed ⁻¹' bad) ≤ bound) →
    ∀ event : Set Value, MeasurableSet event →
    (μ.prod tapeLaw) (Function.uncurry observed ⁻¹' event) ≤ simulator event + bound ∧
      simulator event ≤ (μ.prod tapeLaw) (Function.uncurry observed ⁻¹' event) + bound

end RebuildBound.Spec
