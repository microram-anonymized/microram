import RebuildBound.Proofs.IdealFailure
import spec_tests.HierarchyInitialization

/-! A measurable event contains a real overflowing reference execution. None
of the measurability theorems requires that this event be empty or unlikely. -/
namespace IdealFailureTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open MeasureTheory IdealKey HierarchyInitializationTest

def zeroTape : Tape := fun _ => 0

example : initResult cfg sh tr (IdealHierarchy.words zeroTape) = .error .drain := by
  decide +kernel

theorem overflow : Fails cfg sh tr (IdealHierarchy.words zeroTape) := by
  refine ⟨.initialization, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Initialization has failed, but the reference table retains all five
records and remains finitely determined by the canonical words. -/
example : (initOutput cfg sh tr (IdealHierarchy.words zeroTape)).records.length = 5 := by
  decide +kernel

example : FiniteRead (fun tape => table cfg sh tr (IdealHierarchy.words tape)
    cfg.levels (cfg.seed cfg.levels)) := IdealTableFiniteRead cfg sh tr _ _

example : MeasurableSet {tape | Fails cfg sh tr (IdealHierarchy.words tape)} ∧
    Set.Nonempty {tape | Fails cfg sh tr (IdealHierarchy.words tape)} :=
  ⟨IdealFailureMeasurable cfg sh tr, zeroTape, overflow⟩

/-- The actual adaptive failure event remains measurable even with an
unrestricted record client, before any logical-capacity contract is imposed. -/
example (g : Online.OnlineGeom) (S : Online.Schedule) (a : Adaptive.AdaptiveRun 2) :
    MeasurableSet {tape | Fails cfg sh (OnlineBatch.traceOf g
      (Adaptive.realized cfg sh g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)))
      (IdealHierarchy.words tape)} := IdealAdaptiveFailureMeasurable cfg sh g S 2 a

end IdealFailureTests
