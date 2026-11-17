import RebuildBound.Spec.NativeMatch.Jobs
import RebuildBound.Spec.NativeMatch.Ordinals

set_option maxRecDepth 4000
namespace RebuildBound.NativeMatchJobsTests
open Model Spec NativeMatch NativeMatchTrace NativeMatchJobTrace NativeMatchOrdinals

def a : Rec := ⟨[1], 11, false⟩
def b : Rec := ⟨[2], 22, false⟩
def state : SFin := ⟨[], [a], [[a]], [[b]], []⟩

/-- The complete first drain records A and B class tags before either
coordinated mask clears; both directions then observe that same state. -/
example : firstDrain state = [some (a,true),some (b,false)] := by decide +kernel
example : (drainEvents 1 1 state).map Event.comparison =
    [([1],[[2]]),([1],[[1]])] := by decide +kernel
example : weight 4 ((drainEvents 1 1 state).map Event.comparison) = 2 := by decide +kernel

/-- The direct layout keeps stage and radix holes in their allocated groups,
then appends the original published A tier without compacting it. -/
def tier : Page := Page.ofBucket [none,some b]
def route : SRoute := ⟨[],[[a]],[],[]⟩
example : (NativeMatchDirectJobTrace.rawPages 1 1 [tier] route).length = 3 := by decide +kernel
example : ((NativeMatchDirectJobTrace.rawPages 1 1 [tier] route).getD 2 tier).bucket.take 3 =
    [none,some b,none] := by decide +kernel

/-- Yield budgets consume only the next unexecuted operations; a zero budget
preserves both the cursor and already emitted exact-prestate events. -/
def emit (s op : Nat) : List Event := [{site := .fixedDedup, rule := .rebuild32, subject := LogicalKey.ofNat s, partners := [LogicalKey.ofNat op]}]
example : (resume (· + ·) emit 0 (atCut (· + ·) emit 0 [1,2,3] 1)).remaining = [2,3] := by
  decide +kernel
example : (resume (· + ·) emit 1 (atCut (· + ·) emit 0 [1,2,3] 1)).emitted.map Event.comparison =
    [(LogicalKey.ofNat 0,[LogicalKey.ofNat 1]),(LogicalKey.ofNat 1,[LogicalKey.ofNat 2])] := by decide +kernel
end RebuildBound.NativeMatchJobsTests
