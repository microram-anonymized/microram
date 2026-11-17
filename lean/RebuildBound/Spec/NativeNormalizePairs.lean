import RebuildBound.Spec.NativeMatch

/-! Local normalization collisions. An inventory lists the key pairs whose
equality matters to an independently chosen reference execution. Repetitions
are allowed; a self-pair is never bad. This interface supplies the probability
calculation only, not execution coverage or a geometry-dependent pair count. -/
namespace RebuildBound.Spec.NativeNormalizePairs
open Model NativeNormalize
open scoped ENNReal

abbrev Pairs (Key : Type) := List (Key × Key)

/-- A collision between distinct logical keys in a listed pair. -/
def PairBad {Key Stored : Type} (stored : Key → Stored) (pairs : Pairs Key) : Prop :=
  ∃ p ∈ pairs, p.1 ≠ p.2 ∧ stored p.1 = stored p.2

/-- The union bound counts listed pairs, including repetitions. -/
noncomputable def pairBound (bits budget : Nat) : ℝ≥0∞ :=
  min 1 ((budget : ℝ≥0∞) / (2 : ℝ≥0∞) ^ bits)

end RebuildBound.Spec.NativeNormalizePairs

namespace RebuildBound.Spec
open Model NativeNormalize NativeNormalizePairs MeasureTheory

/-- Concatenating inventories combines their events; no collision independence
is assumed. An injective stored-key map makes every inventory safe. -/
def NativeNormalizePairsEvent_statement : Prop :=
  (∀ {Key Stored : Type} (stored : Key → Stored) (left right : Pairs Key),
    PairBad stored (left ++ right) ↔ PairBad stored left ∨ PairBad stored right) ∧
  (∀ {Key Stored : Type} (stored : Key → Stored), Function.Injective stored →
    ∀ pairs : Pairs Key, ¬ PairBad stored pairs)

/-- Measurable fibres suffice, even for arbitrary independent environments.
The inventory has no normalization-tape argument. -/
def NativeNormalizePairsMeasurable_statement : Prop :=
  ∀ {Env : Type} [MeasurableSpace Env] (bits : Nat)
    (pairs : Env → Pairs LogicalKey),
    (∀ l, MeasurableSet {env | pairs env = l}) →
    MeasurableSet {p : Env × Tape bits | PairBad p.2 (pairs p.1)}

/-- A local pair budget under an unconditional independent random function.
At 128 bits this is the proposed normalization charge. A chooser that inspects
the normalization tape does not meet this interface merely by returning a
short list. Canonical failure guards may be encoded in the independent
inventory, without conditioning the random-function law on success. -/
def NativeNormalizePairsBound_statement : Prop :=
  ∀ {Env : Type} [MeasurableSpace Env] (μ : Measure Env) [IsProbabilityMeasure μ]
    (bits budget : Nat) (pairs : Env → Pairs LogicalKey),
    (∀ l, MeasurableSet {env | pairs env = l}) →
    (∀ env, (pairs env).length ≤ budget) →
    (μ.prod (tapeLaw bits)) {p | PairBad p.2 (pairs p.1)} ≤ pairBound bits budget

end RebuildBound.Spec
