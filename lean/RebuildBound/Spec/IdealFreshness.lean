import RebuildBound.Spec.IdealExposure
import RebuildBound.Spec.IdealMeasurable

/-! The actual adaptive trace prefix is independent of the entire fresh family,
not just of a predetermined finite dictionary of its words. The prefix is a
finite list of completed input units; this does not assert independence of
subsequent routed layouts or prepared records. -/
namespace RebuildBound.Spec.IdealHierarchy
open Model Model.Hierarchy

/-- Completed trace units through a public level-one time. Initialization is
fixed by the client and hence need not be included in this random variable. -/
def inputPrefix (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom)
    (S : Online.Schedule) {m : Nat} (a : Adaptive.AdaptiveRun m)
    (cutoff : Nat) (tape : IdealKey.Tape) : List (List Bucket) :=
  (List.range (cutoff - cfg.seed 1)).map fun i =>
    (OnlineBatch.traceOf g (Adaptive.realized cfg sh g S a (words tape) (dummy tape))).units i

end RebuildBound.Spec.IdealHierarchy

namespace RebuildBound.Spec
open Model Model.Hierarchy IdealHierarchy MeasureTheory ProbabilityTheory

/-- Only the finite history value has the discrete measurable space. -/
def IdealInputPrefixMeasurable_statement : Prop :=
  letI : MeasurableSpace (List (List Bucket)) := ⊤
  ∀ cfg sh g S m (a : Adaptive.AdaptiveRun m) cutoff,
    Measurable (inputPrefix cfg sh g S a cutoff)

/-- Fresh-family independence is derived for the actual adaptive prefix;
there is no supplied independence, fixed dictionary, load or success premise. -/
def IdealInputPrefixIndependent_statement : Prop :=
  letI : MeasurableSpace (List (List Bucket)) := ⊤
  ∀ cfg sh g S m (a : Adaptive.AdaptiveRun m), ExposureGeometry cfg →
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg S (Adaptive.slotCount a.shape) m →
    ∀ family : IdealKey.Family,
      IndepFun (inputPrefix cfg sh g S a (time cfg family.1 family.2))
        (familyBlock family).domRestrict IdealKey.tapeLaw

end RebuildBound.Spec
