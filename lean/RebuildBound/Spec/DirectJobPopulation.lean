import RebuildBound.Spec.DirectJobReference
import RebuildBound.Spec.DirectJobHistoryLaw
import Mathlib.Data.Finset.Card

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Complete incoming key populations in chronological order. Repeated keys
and tombstones contribute to the same union; no disjointness is required. -/
def directPopulationUnion (populations : List (Finset LogicalKey)) : Finset LogicalKey :=
  populations.foldr (· ∪ ·) ∅

def DirectJobPopulationKeys_statement : Prop :=
  ∀ (jobs : List ChainJob) (populations : List (Finset LogicalKey)),
    List.Forall₂ (fun job keys =>
      ((DirectMasks.records job.units).map Rec.key).toFinset = keys) jobs populations →
    ((chainRecords jobs).map Rec.key).toFinset = directPopulationUnion populations

/-- The cumulative load follows from each incoming complete population. This
bound is deliberately independent of successful publication and physical order. -/
def DirectJobPopulationLoad_statement : Prop :=
  ∀ (populations : List (Finset LogicalKey)) (capacity : Nat),
    (∀ keys ∈ populations, keys.card ≤ capacity) →
    (directPopulationUnion populations).card ≤ capacity * populations.length

/-- A total reference prefix from empty automatically supplies chronology,
fixed complete A keys and the selected load bound at the next digit. Jobs may
depend on routing words as long as their complete incoming key sets match. -/
def DirectJobReferencePopulation_statement : Prop :=
  ∀ (oldWord : LogicalKey → Nat) (jobs : List ChainJob) (populations : List (Finset LogicalKey)),
    List.Forall₂ (fun job keys =>
      ((DirectMasks.records job.units).map Rec.key).toFinset = keys) jobs populations →
    (∀ keys ∈ populations, keys.card ≤ 512) →
    let st := referenceChain oldWord (.ofOutput emptyOutput) jobs
    st.records.Perm (DirectPrefix.winners (chainRecords jobs)) ∧
    (st.records.map Rec.key).toFinset = directPopulationUnion populations ∧
    (directPopulationUnion populations).card ≤ 32 * (jobs.length * 16)

/-- Discharge the history contract from a total earlier prefix and fixed
incoming key populations. Only normalized base weights and local source-key
and load premises remain; chronology and cumulative A load are derived. -/
def DirectJobHistoryPrefixValid_statement : Prop :=
  ∀ (data : DirectHistoryData) (d : Nat)
    (pre : data.Base → List ChainJob) (initialWord : data.Base → LogicalKey → Nat)
    (populations : List (Finset LogicalKey)) (priorKeys : Finset LogicalKey),
    (∑ base, data.weight base = 1) →
    (∀ base, data.before base =
      referenceChain (initialWord base) (.ofOutput emptyOutput) (pre base) ∧
      data.chronology base = chainRecords (pre base)) →
    (∀ base, List.Forall₂ (fun job keys =>
      ((DirectMasks.records job.units).map Rec.key).toFinset = keys)
      (pre base) populations) →
    (∀ keys ∈ priorKeys :: populations, keys.card ≤ 512) →
    (∀ base h, ((DirectMasks.records (data.priorUnits base (data.word h))).map
      Rec.key).toFinset = priorKeys) →
    data.KA = directPopulationUnion populations ∪ priorKeys →
    populations.length + 2 = d →
    (∀ hist word, ((DirectMasks.records (data.freshUnits hist word)).map
      Rec.key).toFinset = data.KB) →
    data.KB.card ≤ 512 → data.Valid d

end RebuildBound.Spec
