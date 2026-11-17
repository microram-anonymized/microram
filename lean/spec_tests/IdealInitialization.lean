import RebuildBound.Proofs.IdealInitialization
import RebuildBound.Proofs.IdealKeyLaw
import RebuildBound.Proofs.IdealFailure
import spec_tests.HierarchyInitialization

namespace IdealInitializationPositiveTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open MeasureTheory ProbabilityTheory IdealKey HierarchyInitializationTest

/-- Fix only the five initialization words, leaving the rest of the infinite
routing and dummy tape completely unrestricted. -/
def initCoords : Finset IdealKey.Coord :=
  (tr.init.map fun r => Sum.inl
    (familyOf cfg cfg.levels (cfg.seed cfg.levels), r.key)).toFinset

def cylinder : Set Tape := initCoords.restrict ⁻¹' {fun _ => (0 : Word64)}

lemma cylinder_positive : 0 < tapeLaw cylinder := by
  rw [cylinder, ← Measure.map_apply (Finset.measurable_restrict initCoords)
    (measurableSet_singleton _), (IdealKeyRestriction initCoords).2]
  exact pos_iff_ne_zero.mpr (by
    simp [uniformOn_eq_zero_iff Set.finite_univ])

lemma cylinder_overflows {tape : Tape} (htape : tape ∈ cylinder) :
    initResult cfg sh tr (IdealHierarchy.words tape) = .error .drain := by
  have hzero : initCoords.restrict tape = fun _ => (0 : Word64) := htape
  have hlocal : ∀ r ∈ (⟨initMain sh.init tr.init, []⟩ : TPInputs).aAll,
      jobWord cfg (IdealHierarchy.words tape) cfg.levels (cfg.seed cfg.levels) r.key = 0 := by
    intro r hr
    have hmem := HierarchyTopLawProof.initMain_mem sh.init tr.init r hr
    have hc : Sum.inl (familyOf cfg cfg.levels (cfg.seed cfg.levels),
        r.key) ∈ initCoords :=
      List.mem_toFinset.mpr (List.mem_map_of_mem hmem)
    have hread := congrFun hzero ⟨_, hc⟩
    change (tape (Sum.inl (familyOf cfg cfg.levels (cfg.seed cfg.levels),
      r.key))).val = 0
    exact congrArg Fin.val hread
  change tpJob engineRule sh.init (fun _ => false)
    (jobWord cfg (IdealHierarchy.words tape) cfg.levels (cfg.seed cfg.levels))
    ⟨initMain sh.init tr.init, []⟩ = .error .drain
  rw [TPJobWordLocal sh.init (fun _ => false) _ (fun _ => 0) _ hlocal]
  decide +kernel

/-- The actual reference initialization overflow has positive mass, rather
than merely containing one (zero-mass) infinite tape. -/
theorem initialization_failure_positive :
    0 < tapeLaw {tape | (initResult cfg sh tr (IdealHierarchy.words tape)).toBool = false} := by
  apply lt_of_lt_of_le cylinder_positive
  apply measure_mono
  intro tape htape
  simp only [Set.mem_ofPred_eq, cylinder_overflows htape]
  rfl

end IdealInitializationPositiveTests

namespace IdealInitializationBoundTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open MeasureTheory IdealKey HierarchyInitializationTest
open scoped NNReal

/-- The same initialization with positive overflow probability satisfies the
analytic theorem; the theorem does not assume that the event is empty. -/
example : tapeLaw {tape | (initResult cfg sh tr (IdealHierarchy.words tape)).toBool = false} ≤
    tpBound sh.init ((sh.init.C / 2 : Nat) : NNReal) 1 9 3 := by
  apply IdealInitializationBound cfg sh tr.init 9 3
  all_goals first | exact fun _ => rfl | decide +kernel

/-- Empty, leading-zero and 65-byte keys enter initialization records directly. -/
def wideInput : List Rec :=
  [⟨[], 0, false⟩,
   ⟨[0], 1, false⟩,
   ⟨List.replicate 65 0, 2, false⟩]

example : (wideInput.map Rec.key).Nodup := by decide +kernel
example : 64 < (wideInput[2]!).key.length := by decide +kernel

example (trace : Tape → Trace) (htrace : ∀ tape, (trace tape).init = wideInput) :
    tapeLaw {tape | jobFails cfg sh (trace tape) (IdealHierarchy.words tape) .initialization = true} ≤
      tpBound sh.init ((sh.init.C / 2 : Nat) : NNReal) 1 9 3 := by
  apply IdealInitializationApi cfg sh 3 wideInput 9 3
  all_goals first | exact htrace | decide +kernel | skip
  unfold ApiCapacity.InitialStateValid
  exact ⟨by decide +kernel, by decide +kernel, by simp [wideInput], by simp [cfg]⟩

/-- Duplicate inputs and an overfull initial map fail the public contract. -/
example : ¬ ApiCapacity.InitialStateValid 2 true [⟨LogicalKey.ofNat (0), 0, false⟩, ⟨LogicalKey.ofNat (0), 1, false⟩] := by
  simp [ApiCapacity.InitialStateValid]
example : ¬ ApiCapacity.InitialStateValid 2 true wideInput := by
  simp [ApiCapacity.InitialStateValid, wideInput]

/-- An empty start has no initialization exposure in the public inventory. -/
example : JobId.initialization ∉ ({cfg with initialized := false} : Config).potentialJobs := by
  decide +kernel

end IdealInitializationBoundTests
