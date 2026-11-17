import RebuildBound.Spec.DirectJobReferenceCoverage

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- The unconditional result at a potential ordinal uses precisely the full
reference prefix and the preceding family, including after earlier failure. -/
def DirectJobReferencePrefix_statement : Prop :=
  ∀ (oldWord : LogicalKey → Nat) (st : ReferenceTable) (pre : List ChainJob)
    (job : ChainJob) (rest : List ChainJob),
    (referenceResults oldWord st (pre ++ job :: rest))[pre.length]? =
      some (runJob job.geometry (pre.foldl (fun _ j => j.word) oldWord)
        job.word ((referenceChain oldWord st pre).inputs job.units))

end RebuildBound.Spec
