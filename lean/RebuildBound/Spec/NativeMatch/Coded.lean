import RebuildBound.Spec.NativeMatch.Endpoint
import RebuildBound.Spec.NativeMatch.RoutingBudget
namespace RebuildBound.Spec.NativeMatchCoded
open Model NativeMatchProduction NativeMatchApi NativeMatchEndpoint NativeNormalize NativeRoutingActual NativeRoutingCoupling
open MeasureTheory
open scoped ENNReal

/-- The complete native message is evaluated by one independent RF64 oracle.
The leading unit keeps the finite causal replay's existing product interface. -/
abbrev Sample (model : KeyModel) := (Unit × Noise model) × Tape 64
noncomputable def law (model : KeyModel) : Measure (Sample model) :=
  ((Measure.dirac ()).prod (noiseLaw model)).prod (tapeLaw 64)
instance (model : KeyModel) : IsProbabilityMeasure (law model) := by unfold law; infer_instance

def stored : (model : KeyModel) → Noise model → Tape 128
  | .sixteen, σ => stored16 (encrypt16 σ)
  | .longer, f => f

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

def routing (ctx : Context member initialized h) (model : KeyModel) (p : Sample model) : IdealKey.Tape :=
  p.2 ∘ Coordinates.nativeCode (stored model p.1.2) ∘ NativeMatchRoutingBudget.wire ctx

def failure (ctx : Context member initialized h) (policy : Policy) (model : KeyModel) (p : Sample model) : Prop :=
  match production ctx policy (stored model p.1.2) (routing ctx model p) with
  | .error _ => True
  | .ok state => ¬ResultsCorrect ctx (routing ctx model p) state

def observed (ctx : Context member initialized h) (policy : Policy) (model : KeyModel)
    (p : Sample model) : View ctx :=
  (production ctx policy (stored model p.1.2) (routing ctx model p)).toOption.map (rows ctx)

/-- Reference ring stops are charged on the unconditional canonical experiment.
Other completion, resource, physical schedule and compiled-execution obligations
are additional terms in an event-specific deployment hybrid. -/
noncomputable def ringCost (ctx : Context member initialized h) : ℝ≥0∞ :=
  IdealKey.tapeLaw {tape | NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit
    ctx.snapshots ctx.client ctx.accesses tape}

noncomputable def error (ctx : Context member initialized h) (model : KeyModel) : ℝ≥0∞ :=
  (h:ℝ≥0∞)*ENNReal.ofReal (1/(2:ℝ)^64) + normalizeCost ctx model + ringCost ctx
end RebuildBound.Spec.NativeMatchCoded

namespace RebuildBound.Spec
open Model NativeMatchProduction NativeMatchApi NativeMatchEndpoint NativeRoutingActual NativeMatchRoutingBudget
open MeasureTheory
open scoped ENNReal

/-- All-width correctness for the actual complete-message ideal routing model.
The transfer charges one shared used-key normalization event, without assuming
native outcomes after a bad match can be decoded from an exact-reference memo. -/
def NativeMatchCodedFailure_statement : Prop :=
  ∀ member initialized, member∈ConfigurationFamily.members → ∀ h, 1 ≤ h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ model width, Width model width → InputWidth ctx.client width →
  FieldsFit ctx → CounterFit ctx → ∀ policy,
  NativeMatchCoded.law model {p | NativeMatchCoded.failure ctx policy model p} ≤
    min 1 (NativeMatchCoded.error ctx model)

/-- The complete native-message experiment has the same public exact simulator
up to the same capacity/matching/normalization/ring error in each direction.
The two inequalities do not add their birthday charges together. -/
def NativeMatchCodedObservation_statement : Prop :=
  ∀ member initialized, member∈ConfigurationFamily.members → ∀ h, 1 ≤ h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ model width, Width model width → InputWidth ctx.client width →
  FieldsFit ctx → CounterFit ctx → ∀ policy (event : Set (View ctx)), MeasurableSet event →
  NativeMatchCoded.law model ((NativeMatchCoded.observed ctx policy model) ⁻¹' event) ≤
      min 1 (simulator ctx event + NativeMatchCoded.error ctx model) ∧
    simulator ctx event ≤
      min 1 (NativeMatchCoded.law model ((NativeMatchCoded.observed ctx policy model) ⁻¹' event) +
        NativeMatchCoded.error ctx model)
end RebuildBound.Spec
