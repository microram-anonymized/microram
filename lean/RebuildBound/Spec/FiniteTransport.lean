import RebuildBound.Spec.Model.FiniteJobLaw
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# One coupling and one transport for every job law (trusted)

A job's finite law (`FiniteJobLaw`, the `toFinite` of each job class) is
coupled to an ambient probability space through a `sample` of its finite
outcomes: the coupling is the joint fiber bound, `μ {sample = o}` at most the
law's mass of `o` (history weight times the uniform word mass). Bounds on the
individual fibers suffice; separate marginal laws for history and words would
not. No earlier-success event restricts the fibers or the ambient measure.

**FiniteTransport.** Under the coupling, any ambient set contained in the
event of the law at the sample has probability at most the law's probability
of that event. Neither measurability nor normalization is needed for this
upper bound.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec

open RebuildBound.Model

/-- The joint fiber bound of a sample of a finite job law's outcomes. -/
def FiniteCoupling {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (L : FiniteJobLaw) (sample : Ω → L.Outcome) : Prop :=
  ∀ outcome, μ {ω | sample ω = outcome} ≤
    L.weight outcome.1 * (Fintype.card L.Words : ℝ≥0∞)⁻¹

/-- **FiniteTransport**: a set contained in the event at a coupled sample has
probability at most the law's probability of the event. -/
def FiniteTransport_statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (L : FiniteJobLaw) (sample : Ω → L.Outcome),
    FiniteCoupling μ L sample →
    ∀ (E : L.Hist → (LogicalKey → Nat) → Prop) (A : Set Ω),
      A ⊆ {ω | E (sample ω).1 (L.wordFn (sample ω).2)} → μ A ≤ L.prob E

end RebuildBound.Spec
