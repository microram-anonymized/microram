import RebuildBound.Spec.DirectJobCycle
import RebuildBound.Proofs.DirectJobReferenceCoverage

namespace RebuildBound
open Model Model.DirectJob Spec

theorem DirectJobReferencePrefix : DirectJobReferencePrefix_statement := by
  intro oldWord st pre job rest
  induction pre generalizing oldWord st with
  | nil => rfl
  | cons head tail ih =>
    simpa only [List.cons_append, List.length_cons, referenceResults,
      List.getElem?_cons_succ, List.foldl_cons, referenceChain]
      using ih head.word (referenceStep oldWord st head)

end RebuildBound
