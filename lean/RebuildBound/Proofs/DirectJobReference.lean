import RebuildBound.Spec.DirectJobReference
import RebuildBound.Proofs.DirectJobChain

namespace RebuildBound
open Model Model.DirectJob

private theorem fallback_records (g : Geometry) (inp : DirectJob.Inputs) :
    (referenceFallback g inp).records = inp.winners := by
  simp [referenceFallback, ReferenceTable.records, Bucket.recs]

private theorem fallback_shape (g : Geometry) (word : Model.LogicalKey → Nat) (inp : DirectJob.Inputs) :
    Spec.DirectReferenceShape g word (referenceFallback g inp) := by
  refine ⟨by simp [referenceFallback], ?_, ?_⟩
  · intro bucket hb
    simp only [referenceFallback, List.mem_replicate] at hb
    rcases hb with ⟨_, rfl⟩
    simp
  · intro v hv x hx
    simp [referenceFallback, hv, Bucket.recs] at hx

theorem DirectJobReferenceStep : Spec.DirectJobReferenceStep_statement := by
  intro oldWord st job history hhistory
  have hi : (st.inputs job.units).aRecords.Perm (DirectPrefix.winners history) := hhistory
  have hw := DirectJobChainLemmas.winners_history (st.inputs job.units) history hi
  dsimp only
  unfold referenceStep
  dsimp only
  cases hr : runJob job.geometry oldWord job.word (st.inputs job.units) with
  | rejected reason =>
      exact ⟨by simpa [fallback_records, ReferenceTable.inputs, Inputs.bRecords] using hw,
        fallback_shape _ _ _⟩
  | failed event =>
      exact ⟨by simpa [fallback_records, ReferenceTable.inputs, Inputs.bRecords] using hw,
        fallback_shape _ _ _⟩
  | published out =>
      have hp := DirectJobPublication job.geometry oldWord job.word (st.inputs job.units) out hr
      have hh := DirectJobHistoryStep job.geometry oldWord job.word (st.inputs job.units) out history hi hr
      refine ⟨by simpa [ReferenceTable.ofOutput, ReferenceTable.records, outputRecords,
        ReferenceTable.inputs, Inputs.bRecords] using hh, ?_⟩
      exact ⟨hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1⟩

theorem DirectJobReferenceHistory : Spec.DirectJobReferenceHistory_statement := by
  intro oldWord st jobs
  induction jobs generalizing oldWord st with
  | nil =>
      intro history hhistory
      simpa [referenceChain, chainRecords] using hhistory
  | cons job rest ih =>
      intro history hhistory
      have hs := (DirectJobReferenceStep oldWord st job history hhistory).1
      have ht := ih job.word (referenceStep oldWord st job)
        (history ++ DirectMasks.records job.units) hs
      simpa [referenceChain, chainRecords, List.append_assoc] using ht

theorem DirectJobReferenceKeys : Spec.DirectJobReferenceKeys_statement := by
  intro oldWord st jobs history hhistory
  have hp := DirectJobReferenceHistory oldWord st jobs history hhistory
  refine ⟨(hp.map Rec.key).nodup_iff.mpr (DirectPrefixUnique _), ?_⟩
  ext key
  simp only [List.mem_toFinset]
  exact (hp.map Rec.key).mem_iff.trans (DirectPrefixKeys _ key)

end RebuildBound
