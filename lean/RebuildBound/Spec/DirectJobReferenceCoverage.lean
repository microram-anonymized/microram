import RebuildBound.Spec.DirectJobReference
import RebuildBound.Spec.DirectJobFailure

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- On successful prefixes the total history is exactly the actual published
lanes and records, not merely a permutation of their logical contents. -/
def DirectJobReferenceAgreement_statement : Prop :=
  ∀ (oldWord : LogicalKey → Nat) (initial out : Output) (jobs : List ChainJob),
    runChain oldWord initial jobs = .published out →
    referenceChain oldWord (.ofOutput initial) jobs = .ofOutput out

/-- Exactly one reference result per potential job; execution copies or pauses
introduce no new ordinal in this logical chain. -/
def DirectJobReferenceOrdinals_statement : Prop :=
  ∀ (oldWord : LogicalKey → Nat) (st : ReferenceTable) (jobs : List ChainJob),
    (referenceResults oldWord st jobs).length = jobs.length

/-- Every actual capacity failure is one of the unconditional reference job
results, with the exact event identity. No independence or success conditioning
is needed. Scheduling this cycle into the full hierarchy remains separate. -/
def DirectJobReferenceCoverage_statement : Prop :=
  ∀ (oldWord : LogicalKey → Nat) (initial : Output) (jobs : List ChainJob) (e : CheckEvent),
    runChain oldWord initial jobs = .failed e →
    .failed e ∈ referenceResults oldWord (.ofOutput initial) jobs

end RebuildBound.Spec
