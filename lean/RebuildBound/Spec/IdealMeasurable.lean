import RebuildBound.Spec.IdealHierarchy
import RebuildBound.Spec.Model.Adaptive

/-! Actual reference execution on the canonical product tape is measurable.
Finite dependence is local to each execution: it assumes neither a common key
dictionary across branches nor a uniform bound on the number of queried keys.
No capacity-success, geometry, schedule or flag premise is needed. -/
namespace RebuildBound.Spec.IdealKey
open Model

/-- Each outcome has a finite set of coordinates that determines its result.
The witness may depend on that outcome; no common finite restriction across
branches is supplied as a premise. -/
def FiniteRead {Value : Type} (f : Tape → Value) : Prop :=
  ∀ tape, ∃ coordinates : Finset Coord,
    ∀ other, (∀ c ∈ coordinates, other c = tape c) → f other = f tape

end RebuildBound.Spec.IdealKey

namespace RebuildBound.Spec
open Model Model.Hierarchy MeasureTheory IdealKey

/-- Countably many finite cylinders suffice even when the selected coordinates
depend on the tape. The infinite tape is not given the discrete sigma algebra. -/
def IdealFiniteReadMeasurable_statement : Prop :=
  ∀ (Value : Type) [MeasurableSpace Value] (f : Tape → Value),
    FiniteRead f → Measurable f

/-- Every actual hierarchy table uses only finitely many words at each outcome,
including reference continuations after overflow. -/
def IdealTableFiniteRead_statement : Prop :=
  ∀ cfg sh tr level ordinal,
    FiniteRead (fun tape => table cfg sh tr (IdealHierarchy.words tape) level ordinal)

/-- Fixed-run public observations are measurable without a success condition. -/
def IdealViewMeasurable_statement : Prop :=
  ∀ cfg sh g run S n m,
    Measurable (fun tape => OnlineBatch.view cfg sh g run S n m
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape))

/-- Finite-read locality survives the complete adaptive interaction. Arbitrary
clients can choose new keys from earlier rows; the proof follows those actual
decisions rather than enumerating all possible dictionaries. -/
def IdealAdaptiveFiniteRead_statement : Prop :=
  ∀ cfg sh g S m (a : Adaptive.AdaptiveRun m),
    FiniteRead (fun tape => Adaptive.interact cfg sh g S a
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape))

/-- The actual adaptive transcript has the product-space measurability needed
by subsequent event-section and independent-seed arguments. -/
def IdealAdaptiveMeasurable_statement : Prop :=
  ∀ cfg sh g S m (a : Adaptive.AdaptiveRun m) n,
    Measurable (fun tape => Adaptive.transcript cfg sh g S a n
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape))

end RebuildBound.Spec
