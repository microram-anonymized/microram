import RebuildBound.Spec.ConfigurationFamily

/-! One finite structural certificate, shared by all family consumers. -/

namespace RebuildBound
open Spec Spec.ConfigurationFamily

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem ConfigurationFamilyStructural : ConfigurationFamilyStructural_statement := by
  intro initialized
  cases initialized <;>
    simp only [members, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true] <;>
    repeat' apply And.intro
  all_goals decide +kernel

end RebuildBound
