import RebuildBound.Spec.Model.DirectJobReference
import RebuildBound.Spec.DirectJobChain

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Only main shape and home placement; reference tiers have no capacity bound. -/
def DirectReferenceShape (g : Geometry) (word : LogicalKey → Nat) (st : ReferenceTable) : Prop :=
  st.main.length = g.outputHomes ∧
  (∀ bucket ∈ st.main, bucket.length = 64) ∧
  (∀ v < g.outputHomes, ∀ x ∈ (st.main.getD v []).recs, g.home (word x.key) = v)

/-- Both branches preserve the full newest union, with the requested main shape.
No successful-production, old-tier-fit or geometry premise restricts outcomes. -/
def DirectJobReferenceStep_statement : Prop :=
  ∀ (oldWord : LogicalKey → Nat) (st : ReferenceTable) (job : ChainJob) (history : List Rec),
    st.records.Perm (DirectPrefix.winners history) →
    let next := referenceStep oldWord st job
    next.records.Perm (DirectPrefix.winners (history ++ DirectMasks.records job.units)) ∧
      DirectReferenceShape job.geometry job.word next

/-- Logical chronology is preserved on every reference outcome, including
outcomes after an earlier failure or rejection. -/
def DirectJobReferenceHistory_statement : Prop :=
  ∀ (oldWord : LogicalKey → Nat) (st : ReferenceTable) (jobs : List ChainJob) (history : List Rec),
    st.records.Perm (DirectPrefix.winners history) →
    (referenceChain oldWord st jobs).records.Perm
      (DirectPrefix.winners (history ++ chainRecords jobs))

/-- Complete key populations and uniqueness now hold without conditioning on
success. Fixed chronologies therefore give fixed key sets on all assignments;
independence of those chronologies from word families is a separate premise. -/
def DirectJobReferenceKeys_statement : Prop :=
  ∀ (oldWord : LogicalKey → Nat) (st : ReferenceTable) (jobs : List ChainJob) (history : List Rec),
    st.records.Perm (DirectPrefix.winners history) →
    let records := (referenceChain oldWord st jobs).records
    (records.map Rec.key).Nodup ∧
      (records.map Rec.key).toFinset = ((history ++ chainRecords jobs).map Rec.key).toFinset

end RebuildBound.Spec
