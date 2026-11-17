import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Conditional native error composition on an unconditional coupling. These
interfaces prove no AES security or native correspondence. The hybrid premise
concerns only the event being tested; it need not assert statistical closeness
for all measurable events. Correctness uses its own outcome-event hybrid.
Resource refusal is separate from capacity failure and cannot be omitted merely
because a query allowance is enforced. -/
namespace RebuildBound.Spec.NativeError
open MeasureTheory
open scoped ENNReal

/-- All events live in the same ideal replacement experiment. `stopped`
includes refusals that prevent completion of the advertised execution. -/
structure Events (Ω : Type) where
  normalize : Set Ω
  matchKey : Set Ω
  encoding : Set Ω
  stopped : Set Ω
  capacity : Set Ω

def Events.bad {Ω : Type} (e : Events Ω) : Set Ω :=
  e.normalize ∪ e.matchKey ∪ e.encoding ∪ e.stopped ∪ e.capacity

/-- Construction switches belong in `crypto` once. Exact stored equality and
injective message encoding permit zero terms only under their correspondence
premises. Segment matching of sixteen-byte stored keys has a nonzero matching
term (`NativeMatch`) that treats those keys as ideal: at width sixteen the
normalization permutation is then replaced, and that advantage also belongs in
`crypto`. In a probability experiment, an unknown stop probability can be
charged one. -/
structure Budget where
  crypto : ℝ≥0∞
  normalize : ℝ≥0∞
  matchKey : ℝ≥0∞
  encoding : ℝ≥0∞
  stopped : ℝ≥0∞
  capacity : ℝ≥0∞

def Budget.ideal (b : Budget) : ℝ≥0∞ :=
  b.normalize + b.matchKey + b.encoding + b.stopped + b.capacity

def Budget.total (b : Budget) : ℝ≥0∞ := b.ideal + b.crypto

/-- Outer-measure bounds suffice; no measurability or independence of the bad
events is required, and no experiment is conditioned on their absence. -/
def Events.BoundedBy {Ω : Type} [MeasurableSpace Ω]
    (e : Events Ω) (μ : Measure Ω) (b : Budget) : Prop :=
  μ e.normalize ≤ b.normalize ∧ μ e.matchKey ≤ b.matchKey ∧
    μ e.encoding ≤ b.encoding ∧ μ e.stopped ≤ b.stopped ∧ μ e.capacity ≤ b.capacity

end RebuildBound.Spec.NativeError

namespace RebuildBound.Spec
open MeasureTheory NativeError
open scoped ENNReal

/-- A correctness/failure monitor needs an outcome-event hybrid, separately
from any public-view hybrid. Off the five bad events, correctness must already
be established by the native/reference adapter. -/
def NativeFailureBound_statement : Prop :=
  ∀ {Ω Native : Type} [MeasurableSpace Ω] [MeasurableSpace Native]
    (μ : Measure Ω) (native : Measure Native) [IsProbabilityMeasure native]
    (e : Events Ω) (b : Budget) (idealFailure : Set Ω) (nativeFailure : Set Native),
    e.BoundedBy μ b → idealFailure ⊆ e.bad →
    native nativeFailure ≤ μ idealFailure + b.crypto →
    native nativeFailure ≤ min 1 b.total

/-- For the particular observable event, combine a two-sided hybrid with
off-failure agreement and an exact reference law. `observed` must describe the
claimed public view, including stops and any declared address/timing leakage;
confidential API responses are not implicitly public. The encoded reference
and its simulator can be supplied by the canonical API exact-law theorem. -/
def NativeObservationBound_statement : Prop :=
  ∀ {Ω View : Type} [MeasurableSpace Ω] [MeasurableSpace View]
    (μ : Measure Ω) (native simulator : Measure View)
    [IsProbabilityMeasure native] [IsProbabilityMeasure simulator]
    (reference observed : Ω → View) (e : Events Ω) (b : Budget),
    Measurable reference → μ.map reference = simulator → e.BoundedBy μ b →
    (∀ ω, ω ∉ e.bad → observed ω = reference ω) →
    ∀ event : Set View, MeasurableSet event →
    (native event ≤ μ (observed ⁻¹' event) + b.crypto ∧
      μ (observed ⁻¹' event) ≤ native event + b.crypto) →
    native event ≤ min 1 (simulator event + b.total) ∧
      simulator event ≤ min 1 (native event + b.total)

end RebuildBound.Spec
