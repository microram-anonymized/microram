import RebuildBound.Spec.DirectJobReferenceCoverage

namespace RebuildBound
open Model Model.DirectJob

private theorem published_step (oldWord : Model.LogicalKey → Nat) (st : ReferenceTable)
    (job : ChainJob) (out : Output)
    (h : runJob job.geometry oldWord job.word (st.inputs job.units) = .published out) :
    referenceStep oldWord st job = .ofOutput out := by
  simp only [referenceStep, h]

theorem DirectJobReferenceAgreement : Spec.DirectJobReferenceAgreement_statement := by
  intro oldWord initial out jobs
  induction jobs generalizing oldWord initial with
  | nil =>
      intro h
      simpa only [runChain, referenceChain, LaneResult.published.injEq] using
        congrArg ReferenceTable.ofOutput (LaneResult.published.inj h)
  | cons job rest ih =>
      intro h
      simp only [runChain] at h
      cases hj : runJob job.geometry oldWord job.word (adopt initial job.units) with
      | rejected reason => simp [hj] at h
      | failed e => simp [hj] at h
      | published next =>
          rw [hj] at h
          have hs := published_step oldWord (.ofOutput initial) job next hj
          simpa only [referenceChain, hs] using ih job.word next h

theorem DirectJobReferenceOrdinals : Spec.DirectJobReferenceOrdinals_statement := by
  intro oldWord st jobs
  induction jobs generalizing oldWord st with
  | nil => rfl
  | cons job rest ih => simp only [referenceResults, List.length_cons, ih]

theorem DirectJobReferenceCoverage : Spec.DirectJobReferenceCoverage_statement := by
  intro oldWord initial jobs e
  induction jobs generalizing oldWord initial with
  | nil => simp [runChain]
  | cons job rest ih =>
      intro h
      simp only [runChain] at h
      cases hj : runJob job.geometry oldWord job.word (adopt initial job.units) with
      | rejected reason => simp [hj] at h
      | failed event =>
          have he : event = e := by simpa only [hj, LaneResult.failed.injEq] using h
          subst event
          change .failed e ∈ runJob job.geometry oldWord job.word (adopt initial job.units) :: _
          rw [hj]
          exact List.mem_cons_self
      | published next =>
          rw [hj] at h
          have hs := published_step oldWord (.ofOutput initial) job next hj
          apply List.mem_cons_of_mem
          simpa only [hs] using ih job.word next h

end RebuildBound
