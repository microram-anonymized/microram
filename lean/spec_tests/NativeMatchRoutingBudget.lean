import RebuildBound.Spec.NativeMatch.RoutingBudget
import Mathlib.Tactic
namespace RebuildBound.NativeMatchRoutingBudgetRegression
open Model Spec Spec.NativeMatchRoutingBudget Spec.NativeNormalize

def first : LogicalKey := 1 :: List.replicate 15 0
def second : LogicalKey := 2 :: List.replicate 15 0
def collisionOnly : Observation := ((([],[]),false),[first,second])
def repeatedOnly : Observation := ((([],[]),false),[first,first])
def zeroStored : Tape 128 := fun _ => 0

/-- Even when a routing collision leaves the decoded result, capacity flag,
and comparison list unchanged, the actual used-key collision remains charged. -/
example : ¬bad zeroStored collisionOnly := by simp [bad,collisionOnly]
example : fullBad zeroStored collisionOnly := by
  right
  refine ⟨(first,0),?_,(second,0),?_,?_,rfl⟩
  · simp [collisionOnly,zeroStored]
  · simp [collisionOnly,zeroStored]
  · decide +kernel

/-- Repeated occurrences of one logical key do not create a normalization
collision; only two distinct user keys can trigger the extra event. -/
example : ¬fullBad zeroStored repeatedOnly := by
  simp [fullBad,bad,collision,repeatedOnly,zeroStored]
end RebuildBound.NativeMatchRoutingBudgetRegression
