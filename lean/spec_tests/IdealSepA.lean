import RebuildBound.Proofs.IdealSepA
import spec_tests.IdealSepUnion

/-! Canonical separated A regressions: real failure continuation, independent
old/current sensitivity, empty finite restrictions, and both public endpoints. -/

namespace IdealSepATests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.DirectJob MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A failed digit-one producer has four old homes and zero output tier.
The following separated row deliberately has zero stash capacity; this is a
failure-continuation witness, not a certified small-error geometry. -/
def producer : DirectJob.Geometry := ⟨2, 1, 4, 0, 0, 0, 0, 0, 0, .direct⟩
def receiver : SepGeom := ⟨64, 2, 1, 1, 3, 0, 0, 2, 1, 0⟩
def records : List Rec := (List.range 66).map fun i => ⟨List.replicate i 0, i, false⟩

def oldOutput (oldWord : LogicalKey → Nat) : Output :=
  levelOneStep producer (fun _ => 0) oldWord emptyOutput [records.map some]
def input (oldWord : LogicalKey → Nat) : SInputs :=
  sepInputs receiver (oldOutput oldWord)
    ⟨List.replicate receiver.U (Bucket.empty receiver.C), []⟩

def zero : LogicalKey → Nat := fun _ => 0
def oldSpread : LogicalKey → Nat := fun key => key.length % 4
def currentSpread : LogicalKey → Nat := fun key => key.length % 2

example : runJob producer zero zero (adopt emptyOutput [records.map some]) =
    .failed ⟨⟨.produceB, .outputTier, 0⟩, 2, 0⟩ := rfl

/-- The A side consumes every record of the failed predecessor, including
both the empty key and the 65-byte zero key. -/
example : (input zero).aAll.length = 66 ∧
    [] ∈ ((input zero).aAll.map Rec.key) ∧
    List.replicate 65 0 ∈ ((input zero).aAll.map Rec.key) := by
  decide +kernel

/-- The old family changes the physical A layout and the early raw-stage
witness. The current family independently changes the same witness. -/
example : (input zero).aMain ≠ (input oldSpread).aMain ∧
    sRawStageExcess receiver zero zero (input zero) 0 = 2 ∧
    sRawStageExcess receiver oldSpread zero (input oldSpread) 0 = 0 ∧
    sRawStageExcess receiver zero currentSpread (input zero) 0 = 0 := by
  decide +kernel

/-- Fallback preserves the exact structural input contract, even though the
producer's advertised tier was zero. The next row can accept that old tier. -/
example : SInputShape receiver zero zero (input zero) := by
  constructor <;> decide +kernel

example : receiver.Valid ∧ STiersFit receiver (input zero) := by
  constructor
  · decide +kernel
  · unfold STiersFit
    decide +kernel

/-- The unconditional A event really occurs after producer fallback. -/
example : sharedARouteWitness receiver zero zero (input zero) := by
  left
  exact ⟨0, by decide +kernel, by decide +kernel⟩

end IdealSepATests

namespace IdealSepATests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open MeasureTheory
open IdealDirectAProof (freshBlock oldWords currentWords)
open scoped ENNReal

/-- Empty A/source restrictions retain a valid probability coupling. -/
example (row : SepGeom) :
    FiniteCoupling
      (Measure.infinitePi (fun _ : freshBlock (2, 1) (3, 1) => IdealKey.wordLaw))
      (IdealSepAProof.law row ∅ ∅ (fun _ => ⟨[], [], [], []⟩)).toFinite
      (IdealSepAProof.read (2, 1) (3, 1) ∅ ∅) :=
  IdealSepAProof.coupling (2, 1) (3, 1) (by decide +kernel)
    row ∅ ∅ (fun _ => ⟨[], [], [], []⟩)

/-- Source keys outside the final A population remain in the old history.
The empty key and a long key occupy separate coordinates. -/
def sourceKeys : Finset LogicalKey := {[], List.replicate 65 0}
def aKeys : Finset LogicalKey := {List.replicate 65 0}

example (fresh : freshBlock (2, 1) (3, 1) → Word64) :
    IdealSepAProof.oldWord sourceKeys aKeys
        (IdealSepAProof.read (2, 1) (3, 1) sourceKeys aKeys fresh).1 [] =
      oldWords (2, 1) (3, 1) fresh [] := by
  simp [IdealSepAProof.oldWord, sourceKeys, aKeys, IdealSepAProof.read, oldWords]

example (fresh : freshBlock (2, 1) (3, 1) → Word64) :
    IdealSepAProof.oldWord sourceKeys aKeys
        (IdealSepAProof.read (2, 1) (3, 1) sourceKeys aKeys fresh).1 (List.replicate 65 0) =
      oldWords (2, 1) (3, 1) fresh (List.replicate 65 0) := by
  simp [IdealSepAProof.oldWord, sourceKeys, aKeys, IdealSepAProof.read, oldWords]

end IdealSepATests

namespace IdealSepATests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.DirectJob MeasureTheory
open IdealSepUnionTests
open scoped ENNReal

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The exact A endpoint applies to a nonempty adaptive run for both starts,
including the terminal separated digit whose family is forwarded to the top. -/
example (initialized forwarded : Bool) :
    IdealKey.tapeLaw {tape |
      sharedARouteWitness (row forwarded)
          (jobWord (geo initialized).cfg (IdealHierarchy.words tape) 2
            (ordinal initialized forwarded - 1))
          (jobWord (geo initialized).cfg (IdealHierarchy.words tape) 2
            (ordinal initialized forwarded))
          (sepInputsAt (geo initialized).cfg (geo initialized).shapes
            (IdealDirect.trace (geo initialized).cfg (geo initialized).shapes online
              (schedule initialized) client tape)
            (IdealHierarchy.words tape) 2 (ordinal initialized forwarded)) ∨
        sharedARangeWitness (row forwarded)
          (jobWord (geo initialized).cfg (IdealHierarchy.words tape) 2
            (ordinal initialized forwarded))
          (sepInputsAt (geo initialized).cfg (geo initialized).shapes
            (IdealDirect.trace (geo initialized).cfg (geo initialized).shapes online
              (schedule initialized) client tape)
            (IdealHierarchy.words tape) 2 (ordinal initialized forwarded))} ≤
      selSepABound (row forwarded) := by
  apply IdealSepA initialized member member_valid 1 online (schedule initialized) 1 client
    (online_matches initialized) (by decide +kernel) (schedule_valid initialized)
    2 (ordinal initialized forwarded) (row forwarded)
  · apply HierarchyCoveringProof.mem_ordinary.mpr
    cases initialized <;> cases forwarded <;> decide +kernel
  · decide +kernel
  · cases initialized <;> cases forwarded <;> decide +kernel
  · cases initialized <;> cases forwarded <;> decide +kernel

/-- First failure combines the actual A and union sections for the same
adaptive run; these hypotheses have concrete arithmetic witnesses. -/
example (initialized forwarded : Bool) :
    IdealKey.tapeLaw {tape |
      JobFailsFirst (geo initialized).cfg (geo initialized).shapes
        (IdealDirect.trace (geo initialized).cfg (geo initialized).shapes online
          (schedule initialized) client tape)
        (IdealHierarchy.words tape) (.ordinary 2 (ordinal initialized forwarded))} ≤
      selSepBound (row forwarded) := by
  apply IdealSepFirstFailure initialized member member_valid 1 online (schedule initialized)
    1 client (online_matches initialized) (by decide +kernel) (schedule_valid initialized)
    2 (ordinal initialized forwarded) (row forwarded)
  · apply HierarchyCoveringProof.mem_ordinary.mpr
    cases initialized <;> cases forwarded <;> decide +kernel
  · decide +kernel
  · cases initialized <;> cases forwarded <;> decide +kernel

/-- Forwarding identifies a receiving family only with its completing lower
carry, never with the preceding separated family's word at the same key. -/
example (initialized forwarded : Bool) :
    familyOf (geo initialized).cfg 2 (ordinal initialized forwarded - 1) ≠
      familyOf (geo initialized).cfg 2 (ordinal initialized forwarded) := by
  cases initialized <;> cases forwarded <;> decide +kernel

end IdealSepATests
