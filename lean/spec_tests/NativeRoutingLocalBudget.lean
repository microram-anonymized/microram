import RebuildBound.Proofs.NativeRoutingLocalBudget

/-! Uniform budgets cover every reply branch, including inconsistent replies
to a repeated coordinate; decoded memoized replay may use fewer reads. -/
namespace RebuildBound.NativeRoutingLocalBudgetTests
open Model Spec NativeRoutingActual NativeRoutingLocalBudget

private def branch : ReadTree Unit Nat :=
  .read () fun word => if word = 0 then .read () fun next => .done next.val
    else .done word.val

example : depth (.done 7 : ReadTree Unit Nat) = 0 := rfl

private theorem depth_ge_two {Q α : Type} (tree : ReadTree Q α)
    (lower : ¬ ReadTree.bounded 1 tree) : 2 ≤ depth tree := by
  by_contra h
  have hb : ReadTree.bounded (depth tree) tree := NativeRoutingLocalBudgetProof.depth_bounded tree
  exact lower (NativeRoutingActualProof.bounded_mono tree hb (by omega : depth tree ≤ 1))

example : depth branch = 2 := by
  have upper : depth branch ≤ 2 := (NativeRoutingFiniteBudget branch).2 2 (by
    simp only [branch, ReadTree.bounded]
    intro word
    split_ifs <;> simp [ReadTree.bounded])
  have lower : ¬ ReadTree.bounded 1 branch := by
    intro hb
    have hzero := hb (0 : Word64)
    simp [ReadTree.bounded] at hzero
  have htwo := depth_ge_two branch lower
  omega

/-- Repeated queries and even aliases of distinct queries always decode. -/
example (answers : NativeNormalize.Answers 64 (depth branch)) :
    ∃ result, NativeRoutingLocalBudget.replayResult (fun _ : Unit => []) branch answers = some result :=
  NativeRoutingFiniteComplete branch _ answers

private def two : ReadTree Bool (Word64 × Word64) :=
  .read false fun first => .read true fun second => .done (first, second)

example (answers : NativeNormalize.Answers 64 (depth two)) :
    ∃ result, NativeRoutingLocalBudget.replayResult (fun _ : Bool => []) two answers = some result :=
  NativeRoutingFiniteComplete two _ answers

/-- Native aliasing is allowed by the marginal law; it is not agreement. -/
example (tape : LogicalKey → Word64) :
    ReadTree.evaluate (tape ∘ fun _ : Bool => ([] : LogicalKey)) two = (tape [], tape []) := rfl

end RebuildBound.NativeRoutingLocalBudgetTests
