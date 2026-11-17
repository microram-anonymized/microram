import RebuildBound.Spec.NativeMatch.Api
import RebuildBound.Spec.ApiBounded
import RebuildBound.Spec.NativeError
namespace RebuildBound.Spec.NativeMatchEndpoint
open Model Model.Hierarchy Model.Online NativeMatchProduction NativeMatchApi NativeNormalize NativeMatch
open MeasureTheory
open scoped ENNReal

/-- Ideal stored-key experiments for the secret user-key interface. Sixteen-byte
keys use one permutation; longer keys use the normalization random function.
AES replacement, public stored-key injection, and compiled execution are not
silently included in either law. -/
inductive KeyModel where
  | sixteen
  | longer
  deriving DecidableEq

abbrev Noise : KeyModel → Type
  | .sixteen => Equiv.Perm (Fingerprint 128)
  | .longer => Tape 128

instance (model : KeyModel) : MeasurableSpace (Noise model) := by
  cases model <;> unfold Noise <;> infer_instance

noncomputable def noiseLaw : (model : KeyModel) → Measure (Noise model)
  | .sixteen => permLaw 128
  | .longer => tapeLaw 128

instance (model : KeyModel) : IsProbabilityMeasure (noiseLaw model) := by
  cases model <;> unfold noiseLaw <;> infer_instance

def stored : (model : KeyModel) → Noise model → Tape 128
  | .sixteen, σ => fun key => σ (NativeMatchTrace.block16 key)
  | .longer, f => f

def Width : KeyModel → Nat → Prop
  | .sixteen, width => width = 16
  | .longer, width => 16 < width ∧ width ≤ 64

abbrev Sample (model : KeyModel) := IdealKey.Tape × Noise model
/-- Canonical logical-routing product experiment. Complete native-message
routing is coupled separately by NativeMatchRoutingBudget. -/
noncomputable def law (model : KeyModel) : Measure (Sample model) := IdealKey.tapeLaw.prod (noiseLaw model)
instance (model : KeyModel) : IsProbabilityMeasure (law model) := by unfold law; infer_instance

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

noncomputable def normalizeCost (ctx : Context member initialized h) : KeyModel → ℝ≥0∞
  | .sixteen => 0
  | .longer => birthday 128 (ctx.init.length+ctx.accesses)

/-- Logical replies, history, selected addresses and advertised lengths of the
actual successful native state. Producer stops count as unsuccessful completion. -/
def ResultsCorrect (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (state : State ctx.transcriptWidth) : Prop :=
  ApiResultsCorrect ctx.geo ctx.codec ctx.unit
    ⟨state.ops,ctx.init,fun r=>ctx.codec.flag r.val⟩ ctx.schedule ctx.accesses
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) state.requests
    (fun t=>state.selected.getD t ⟨none,[]⟩) ∧
      state.selected.length = ctx.accesses ∧ state.rows.length = ctx.accesses

def failure (ctx : Context member initialized h) (policy : Policy) (model : KeyModel)
    (p : Sample model) : Prop :=
  match production ctx policy (stored model p.2) p.1 with
  | .error _ => True
  | .ok state => ¬ResultsCorrect ctx p.1 state

abbrev Transcript (ctx : Context member initialized h) := Fin ctx.accesses → Fin ctx.transcriptWidth → Nat
abbrev View (ctx : Context member initialized h) := Option (Transcript ctx)

instance (n m : Nat) : MeasurableSpace (Option (Fin n → Fin m → Nat)) := ⊤
instance (n m : Nat) : DiscreteMeasurableSpace (Option (Fin n → Fin m → Nat)) := ⟨fun _=>trivial⟩

def rows (ctx : Context member initialized h) (state : State ctx.transcriptWidth) : Transcript ctx :=
  fun t i => state.rows.getD t.val (fun _=>0) i

def observed (ctx : Context member initialized h) (policy : Policy) (model : KeyModel)
    (p : Sample model) : View ctx :=
  (production ctx policy (stored model p.2) p.1).toOption.map (rows ctx)

def referenceView (ctx : Context member initialized h) (tape : IdealKey.Tape) : View ctx :=
  some (rows ctx (reference ctx tape))

noncomputable def simulator (ctx : Context member initialized h) : Measure (View ctx) :=
  (simLaw ctx.geo.cfg (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape ctx.frames)) ctx.schedule)
    (Adaptive.shapePattern (ApiAdaptive.shape ctx.frames)) ctx.accesses ctx.transcriptWidth).map some

/-- The stop set includes the actual reference ring guard and any further
completion refusals the compiled contract declares. Its probability is an
explicit obligation; enforcing a resource allowance does not bound it. -/
def Events (ctx : Context member initialized h) (model : KeyModel)
    (encoding stopped : Set (Sample model)) : NativeError.Events (Sample model) where
  normalize := {p | normalizationBad ctx (stored model p.2) p.1}
  matchKey := {p | ∃ e∈ctx.inventory p.1, e.bad (stored model p.2)}
  encoding := encoding
  stopped := stopped
  capacity := {p | ctx.capacityBad p.1}

noncomputable def budget (ctx : Context member initialized h) (model : KeyModel)
    (crypto encoding stopped : ℝ≥0∞) : NativeError.Budget where
  crypto := crypto
  normalize := normalizeCost ctx model
  matchKey := (h:ℝ≥0∞)*((NativeMatchInventory.weight member initialized:ℝ≥0∞)/(2:ℝ≥0∞)^128)
  encoding := encoding
  stopped := stopped
  capacity := IdealKey.tapeLaw {tape | ctx.capacityBad tape}

noncomputable def total (ctx : Context member initialized h) (model : KeyModel)
    (crypto encoding stopped : ℝ≥0∞) : ℝ≥0∞ :=
  (h:ℝ≥0∞)*ENNReal.ofReal (1/(2:ℝ)^64) + normalizeCost ctx model + encoding + stopped + crypto

end RebuildBound.Spec.NativeMatchEndpoint

namespace RebuildBound.Spec
open Model NativeMatchProduction NativeMatchApi NativeMatchEndpoint NativeRoutingActual MeasureTheory
open scoped ENNReal

/-- All bad events and deterministic correspondence are instantiated with the
actual production interpreter. In this canonical logical-routing experiment, encoding and completion
probabilities are the remaining noncryptographic inputs. The complete-message
routing transfer is a separate proved coupling. -/
def NativeMatchIdealFailure_statement : Prop :=
  ∀ member initialized, member∈ConfigurationFamily.members → ∀ h, 1≤h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ model width, Width model width → InputWidth ctx.client width → ∀ policy,
  ∀ (encoding stopped : Set (Sample model)) (encodingCost stopCost : ℝ≥0∞),
  (∀ p : Sample model, NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit
    ctx.snapshots ctx.client ctx.accesses p.1 → p∈stopped) →
  law model encoding ≤ encodingCost → law model stopped ≤ stopCost →
  law model {p | failure ctx policy model p} ≤ min 1 (total ctx model 0 encodingCost stopCost)

/-- The event-specific hybrid must account for the declared cryptographic and
compiled execution replacement. It is separate from the proved matching,
normalization, capacity and reference correctness conclusions. -/
def NativeMatchFailureEndpoint_statement : Prop :=
  ∀ member initialized, member∈ConfigurationFamily.members → ∀ h, 1≤h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ model width, Width model width → InputWidth ctx.client width → ∀ policy,
  ∀ (encoding stopped : Set (Sample model)) (crypto encodingCost stopCost : ℝ≥0∞),
  (∀ p : Sample model, NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit
    ctx.snapshots ctx.client ctx.accesses p.1 → p∈stopped) →
  law model encoding ≤ encodingCost → law model stopped ≤ stopCost →
  ∀ {Native : Type} [MeasurableSpace Native] (native : Measure Native) [IsProbabilityMeasure native]
    (nativeFailure : Set Native),
  native nativeFailure ≤ law model {p | failure ctx policy model p} + crypto →
  native nativeFailure ≤ min 1 (total ctx model crypto encodingCost stopCost)

/-- The actual native rows are compared to the public exact simulator obtained
from IdealApiExact. Confidential replies are excluded from this public view.
Stops are visible through none; declared extra leakage requires a separate
compiled observation contract. -/
def NativeMatchObservationEndpoint_statement : Prop :=
  ∀ member initialized, member∈ConfigurationFamily.members → ∀ h, 1≤h →
  ∀ (ctx : Context member initialized h), ctx.Valid →
  ∀ model width, Width model width → InputWidth ctx.client width → ∀ policy,
  ∀ (encoding stopped : Set (Sample model)) (crypto encodingCost stopCost : ℝ≥0∞),
  (∀ p : Sample model, NativeMatchHierarchy.ringStopped ctx.geo.cfg ctx.geo.shapes ctx.unit
    ctx.snapshots ctx.client ctx.accesses p.1 → p∈stopped) →
  law model encoding ≤ encodingCost → law model stopped ≤ stopCost →
  ∀ (native : Measure (View ctx)) [IsProbabilityMeasure native]
    (event : Set (View ctx)), MeasurableSet event →
  (native event ≤ law model ((observed ctx policy model) ⁻¹' event) + crypto ∧
    law model ((observed ctx policy model) ⁻¹' event) ≤ native event + crypto) →
  native event ≤ min 1 (simulator ctx event + total ctx model crypto encodingCost stopCost) ∧
    simulator ctx event ≤ min 1 (native event + total ctx model crypto encodingCost stopCost)
end RebuildBound.Spec
