import RebuildBound.Spec.DirectJobHistoryGeometry
import RebuildBound.Proofs.DirectJobReference

namespace RebuildBound
open Model Model.DirectJob Spec

theorem DirectJobPopulationKeys : DirectJobPopulationKeys_statement := by
  intro jobs populations h
  induction h with
  | nil => simp [chainRecords, directPopulationUnion]
  | cons h _ ih =>
    simpa only [chainRecords, List.flatMap_cons, List.map_append, List.toFinset_append,
      directPopulationUnion, List.foldr_cons] using congrArg₂ (· ∪ ·) h ih

theorem DirectJobPopulationLoad : DirectJobPopulationLoad_statement := by
  intro populations capacity h
  induction populations with
  | nil => simp [directPopulationUnion]
  | cons keys rest ih =>
    have hk := h keys (by simp)
    have hr := ih (fun k hm => h k (by simp [hm]))
    have hu := Finset.card_union_le keys (directPopulationUnion rest)
    change (keys ∪ directPopulationUnion rest).card ≤ capacity * (rest.length + 1)
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem DirectJobReferencePopulationFor : DirectJobReferencePopulationFor_statement := by
  intro oldWord jobs populations capacity hkeys hload
  have hempty : (ReferenceTable.ofOutput emptyOutput).records.Perm
      (DirectPrefix.winners []) := by
    simp [ReferenceTable.ofOutput, ReferenceTable.records, emptyOutput,
      Bucket.recs, DirectPrefix.winners]
  have hh := DirectJobReferenceHistory oldWord (.ofOutput emptyOutput) jobs [] hempty
  have hk := (DirectJobReferenceKeys oldWord (.ofOutput emptyOutput) jobs [] hempty).2
  refine ⟨by simpa using hh, ?_, ?_⟩
  · simpa only [List.nil_append, DirectJobPopulationKeys jobs populations hkeys] using hk
  · simpa only [hkeys.length_eq] using DirectJobPopulationLoad populations capacity hload

theorem DirectJobReferencePopulation : DirectJobReferencePopulation_statement := by
  intro oldWord jobs populations hkeys hload
  simpa only [show ∀ n, 512 * n = 32 * (n * 16) from fun n => by omega] using
    DirectJobReferencePopulationFor oldWord jobs populations 512 hkeys hload

theorem DirectJobHistoryPrefixValidFor : DirectJobHistoryPrefixValidFor_statement := by
  intro data s load pre initialWord populations priorKeys hw hstate hkeys hload hprior hKA hd hfresh hKB
  have hpop : ∀ keys ∈ populations, keys.card ≤ load * s.U :=
    fun keys hk => hload keys (List.mem_cons_of_mem _ hk)
  constructor
  · exact hw
  · intro base
    rw [(hstate base).1, (hstate base).2]
    exact (DirectJobReferencePopulationFor (initialWord base) (pre base) populations
      (load * s.U) (hkeys base) hpop).1
  · intro base h
    rw [(hstate base).2, List.map_append, List.toFinset_append,
      DirectJobPopulationKeys (pre base) populations (hkeys base), hprior base h, hKA]
  · exact hfresh
  · rw [hKA]
    calc (directPopulationUnion populations ∪ priorKeys).card
        ≤ (directPopulationUnion populations).card + priorKeys.card := Finset.card_union_le _ _
      _ ≤ (load * s.U) * populations.length + load * s.U :=
        Nat.add_le_add (DirectJobPopulationLoad populations _ hpop) (hload _ List.mem_cons_self)
      _ = load * ((s.d - 1) * s.U) := by rw [show s.d - 1 = populations.length + 1 by omega]; ring
  · exact hKB

theorem DirectJobHistoryPrefixValid : DirectJobHistoryPrefixValid_statement := by
  intro data d pre initialWord populations priorKeys hw hstate hkeys hload hprior hKA hd hfresh hKB
  have hpop : ∀ keys ∈ populations, keys.card ≤ 512 :=
    fun keys hk => hload keys (List.mem_cons_of_mem _ hk)
  constructor
  · exact hw
  · intro base
    rw [(hstate base).1, (hstate base).2]
    exact (DirectJobReferencePopulation (initialWord base) (pre base) populations
      (hkeys base) hpop).1
  · intro base h
    rw [(hstate base).2, List.map_append, List.toFinset_append,
      DirectJobPopulationKeys (pre base) populations (hkeys base), hprior base h, hKA]
  · exact hfresh
  · rw [hKA]
    have hp := DirectJobPopulationLoad populations 512 hpop
    have hk := hload priorKeys List.mem_cons_self
    have hu := Finset.card_union_le (directPopulationUnion populations) priorKeys
    omega
  · exact hKB

end RebuildBound
