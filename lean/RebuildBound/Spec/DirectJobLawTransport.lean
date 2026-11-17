import RebuildBound.Spec.DirectJobHistoryLaw
import RebuildBound.Spec.FiniteTransport

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- The finite outcomes of an existing job law, retaining one shared current
word per key. This does not introduce a second independent word for A/B overlap.
It is the generic `L.toFinite.Outcome`, `L.Hist × (L.Key → Fin (2 ^ L.W))`. -/
abbrev DirectJobOutcome {g : SepGeom} (L : SJobLaw g) := L.toFinite.Outcome

/-- An unconditional joint marginal on an ambient space: the generic
`FiniteCoupling` of `L.toFinite`. Bounds on individual fibers suffice;
separate marginal laws for history and words would not suffice. No
earlier-success event restricts either the fibers or the ambient measure. -/
abbrev DirectJobLawCoupling {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    {g : SepGeom} (L : SJobLaw g) (sample : Ω → DirectJobOutcome L) : Prop :=
  FiniteCoupling μ L.toFinite sample

/-- Transport any finite-word event using the joint fiber bound. Neither
measurability of the event nor normalization is needed for this upper bound. -/
def DirectJobLawTransport_statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    {g : SepGeom} (L : SJobLaw g) (sample : Ω → DirectJobOutcome L),
    DirectJobLawCoupling μ L sample →
    ∀ E : L.Hist → (LogicalKey → Nat) → Prop,
      μ {ω | E (sample ω).1 (L.wordFn (sample ω).2)} ≤ L.prob E

/-- Apply the checked history-law theorem on a shared space. Coupling remains
an explicit global probability premise; this is not a native seeding theorem. -/
def DirectJobHistoryTransport_statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : Nat), 2 ≤ d → d ≤ 8 →
    ∀ (data : DirectHistoryData), data.Valid d →
    ∀ sample : Ω → DirectJobOutcome (data.law d),
    DirectJobLawCoupling μ (data.law d) sample →
    μ {ω | ∃ e, runJob (selectedDirectGeometry d)
      ((data.law d).wOld (sample ω).1) ((data.law d).wordFn (sample ω).2)
      (data.direct d (sample ω).1 ((data.law d).wordFn (sample ω).2)) = .failed e} ≤
      selectedDirectBound selectedDirectABudget d

end RebuildBound.Spec
