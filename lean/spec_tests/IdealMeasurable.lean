import RebuildBound.Proofs.IdealMeasurable
import RebuildBound.Proofs.IdealKeyLaw

/-! Measurability follows actual dynamic reads and adaptive operations, with no
geometry, schedule, capacity, flag, or successful-execution assumptions. -/
namespace IdealMeasurableTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open MeasureTheory IdealKey

/-- Reading a word can choose a new, longer key for a later read. FiniteRead
does not infer that the later read is fresh or independent. -/
def dynamic (tape : Tape) : Word64 :=
  tape (.inl ((2, 7), List.replicate ((tape (.inr (0, 0))).val + 65) 0))

theorem dynamic_finite : FiniteRead dynamic :=
  (FiniteRead.read (.inr (0, 0))).bind
    (fun word tape => tape (.inl ((2, 7), List.replicate (word.val + 65) 0)))
    (fun _ => FiniteRead.read _)

example : Measurable dynamic := IdealFiniteReadMeasurable _ _ dynamic_finite

/-- The actual interaction, including chosen records, has a finite local
witness for every tape; invalid public inputs are also total computations. -/
example (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom) (S : Online.Schedule)
    (a : Adaptive.AdaptiveRun 3) (tape : Tape) :
    ∃ coordinates : Finset Coord, ∀ other,
      (∀ c ∈ coordinates, other c = tape c) →
      Adaptive.interact cfg sh g S a (IdealHierarchy.words other) (IdealHierarchy.dummy other) =
        Adaptive.interact cfg sh g S a (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) :=
  IdealAdaptiveFiniteRead cfg sh g S 3 a tape

example (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom) (S : Online.Schedule)
    (a : Adaptive.AdaptiveRun 0) :
    Measurable (fun tape => Adaptive.transcript cfg sh g S a 0
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)) :=
  IdealAdaptiveMeasurable cfg sh g S 0 a 0

/-- Arbitrary postprocessing of the finite transcript is measurable too; in
particular legal typed normalization cannot introduce a measurability gap. -/
example (cfg : Config) (sh : Shapes) (g : Online.OnlineGeom) (S : Online.Schedule)
    {m : Nat} (a : Adaptive.AdaptiveRun m) (n : Nat) (event : Set (Fin n → Fin m → Nat)) :
    MeasurableSet {tape | Adaptive.transcript cfg sh g S a n
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ∈ event} :=
  IdealAdaptiveMeasurable cfg sh g S m a n (Set.to_countable event).measurableSet

end IdealMeasurableTests
