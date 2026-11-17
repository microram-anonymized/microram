import RebuildBound.Spec.IdealExposure
import RebuildBound.Spec.IdealMeasurable

/-! The actual direct job's complete inputs and previous-family words are
unchanged by resampling its current family. This statement concerns reference
execution, including overflow continuations, and requires no key universe,
capacity bound, flag soundness or successful execution. -/
namespace RebuildBound.Spec.IdealDirect
open Model Model.Hierarchy

/-- The actual adaptive trace fed to every hierarchy job. -/
def trace (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (tape : IdealKey.Tape) : Trace :=
  OnlineBatch.traceOf g
    (Adaptive.realized cfg sh g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape))

/-- The actual direct job's adopted previous table and fresh input units. -/
def inputs (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (ordinal : Nat) (tape : IdealKey.Tape) : DirectJob.Inputs :=
  levelOneInputs cfg sh (trace cfg sh g S a tape) (IdealHierarchy.words tape) ordinal

end RebuildBound.Spec.IdealDirect

namespace RebuildBound.Spec
open Model Model.Hierarchy IdealHierarchy IdealDirect

/-- Finite local dependence follows the actual interaction's requests and
reference tables. No finite dictionary shared between branches is needed. -/
def IdealDirectInputFiniteRead_statement : Prop :=
  ∀ cfg sh g S m (a : Adaptive.AdaptiveRun m) ordinal,
    IdealKey.FiniteRead (inputs cfg sh g S a ordinal)

/-- The late direct-job cut fixes all inputs and all previous-family words
when only its current, possibly forwarded, family is resampled. The ordinal
need not lie within the configured horizon. -/
def IdealDirectInputFresh_statement : Prop :=
  ∀ cfg sh g S m (a : Adaptive.AdaptiveRun m), ExposureGeometry cfg →
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg S (Adaptive.slotCount a.shape) m →
    ∀ ordinal, cfg.seed 1 < ordinal → ∀ x y : IdealKey.Tape,
    (∀ coordinate, coordinate ∉ familyBlock (familyOf cfg 1 ordinal) →
      x coordinate = y coordinate) →
    inputs cfg sh g S a ordinal x = inputs cfg sh g S a ordinal y ∧
      jobWord cfg (words x) 1 (ordinal - 1) = jobWord cfg (words y) 1 (ordinal - 1)

end RebuildBound.Spec
