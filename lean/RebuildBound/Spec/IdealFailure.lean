import RebuildBound.Spec.IdealMeasurable

/-! Capacity events on the unconditional reference execution are measurable.
This supplies the event-space obligation for probability arguments; it does
not bound any job or assert freshness of a routing family. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy IdealKey MeasureTheory

/-- A particular bounded job's failure test, evaluated on reference inputs,
has finite local word dependence, whether or not an earlier job overflowed. -/
def IdealJobFailureFiniteRead_statement : Prop :=
  ∀ cfg sh tr job,
    FiniteRead (fun tape => jobFails cfg sh tr (IdealHierarchy.words tape) job)

/-- The finite public inventory defines a measurable failure event. -/
def IdealFailureMeasurable_statement : Prop :=
  ∀ cfg sh tr,
    MeasurableSet {tape | Fails cfg sh tr (IdealHierarchy.words tape)}

/-- Adaptive requests and their actual trace can be substituted into the same
unconditional event. There is no capacity-success or key-universe premise. -/
def IdealAdaptiveFailureMeasurable_statement : Prop :=
  ∀ cfg sh g S m (a : Adaptive.AdaptiveRun m),
    MeasurableSet {tape | Fails cfg sh
      (OnlineBatch.traceOf g (Adaptive.realized cfg sh g S a
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)))
      (IdealHierarchy.words tape)}

end RebuildBound.Spec
