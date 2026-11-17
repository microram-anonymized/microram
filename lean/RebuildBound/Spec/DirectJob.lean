import RebuildBound.Spec.DirectJobPublication
import RebuildBound.Spec.DirectJobFailure

namespace RebuildBound.Spec

/-- The complete atomic direct-job contract: successful publication preserves
the newest full records with exact geometry and excess; execution agrees with
the unlimited analytical trace, rejects invalid structure, and reports its first
failed check without publication. Every capacity failure lies in the existing
unconditional producer/A/output witnesses.

The component statements quantify over the original inputs. No internal phase
correctness, probability law, native correspondence, or cursor API is assumed. -/
def DirectJob_statement : Prop :=
  DirectJobPublication_statement ∧
  DirectJobSimulation_statement ∧
  DirectJobFirstFailure_statement ∧
  DirectJobFailureContainment_statement

end RebuildBound.Spec
