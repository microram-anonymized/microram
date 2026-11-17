import RebuildBound.Spec.DirectJobCycleGeometry
import RebuildBound.Proofs.DirectJobReference
import RebuildBound.Proofs.DirectJobCycleGeometry.Basic
import RebuildBound.Proofs.WordLocalDirect

/-! # DirectJobUniformCycle: the reference-chain word congruence.

Two direct chains with the same units whose words agree, at each ordinal,
on the records of the history and of the ordinals so far give the same total
reference chain; the initial old words need agree only on the main records of
the starting table. Each step is `DirectJobWordLocal`; the record keys of the
intermediate tables come from `DirectJobReferenceStep`. -/

namespace RebuildBound.DirectJobUniformCycleProof
open Model Model.DirectJob Spec

theorem chainRecords_for (geometry : Nat → Geometry) (first : Nat) (steps : List ((Model.LogicalKey → Nat) × List Bucket)) :
    chainRecords (directChainJobs geometry first steps) =
      steps.flatMap fun s => DirectMasks.records s.2 := by
  induction steps generalizing first with
  | nil => rfl
  | cons s rest ih =>
    obtain ⟨w, u⟩ := s
    simp only [directChainJobs, chainRecords, List.flatMap_cons] at ih ⊢
    rw [ih]

theorem forall₂_for (geometry : Nat → Geometry) (first : Nat) {steps : List ((Model.LogicalKey → Nat) × List Bucket)}
    {pops : List (Finset Model.LogicalKey)}
    (h : List.Forall₂ (fun s keys => ((DirectMasks.records s.2).map Rec.key).toFinset = keys)
      steps pops) :
    List.Forall₂ (fun job keys => ((DirectMasks.records job.units).map Rec.key).toFinset = keys)
      (directChainJobs geometry first steps) pops := by
  induction h generalizing first with
  | nil => exact .nil
  | cons hab _ ih =>
    rename_i a _ _ _
    obtain ⟨w, u⟩ := a
    exact .cons hab (ih _)

/-- A record of the steps' units lies in one ordinal's units. -/
theorem mem_steps_records {steps : List ((Model.LogicalKey → Nat) × List Bucket)} {x : Rec}
    (hx : x ∈ steps.flatMap fun s => DirectMasks.records s.2) :
    ∃ q, ∃ hq : q < steps.length, x ∈ DirectMasks.records steps[q].2 := by
  obtain ⟨s, hs, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.1 hs
  exact ⟨q, hq, hx⟩

theorem mem_records_of_perm {st : ReferenceTable} {history : List Rec}
    (hst : st.records.Perm (DirectPrefix.winners history)) {x : Rec} (hx : x ∈ st.records) :
    x ∈ history :=
  DirectJobSelectedCycleProof.mem_winners (hst.mem_iff.1 hx)

/-- **Word congruence of geometry-parametric reference chains.** -/
theorem chain_congr_for (geometry : Nat → Geometry) (first : Nat) (steps steps' : List ((Model.LogicalKey → Nat) × List Bucket))
    (ow ow' : Model.LogicalKey → Nat) (st : ReferenceTable) (history : List Rec)
    (hst : st.records.Perm (DirectPrefix.winners history))
    (how : ∀ x ∈ st.main.flatMap Bucket.recs, ow x.key = ow' x.key)
    (hlen : steps.length = steps'.length)
    (hu : ∀ p (h : p < steps.length) (h' : p < steps'.length), steps[p].2 = steps'[p].2)
    (hw : ∀ p (h : p < steps.length) (h' : p < steps'.length),
      ∀ x ∈ history ++ (steps.take (p + 1)).flatMap (fun s => DirectMasks.records s.2),
        steps[p].1 x.key = steps'[p].1 x.key) :
    referenceChain ow st (directChainJobs geometry first steps) =
      referenceChain ow' st (directChainJobs geometry first steps') := by
  induction steps generalizing steps' first ow ow' st history with
  | nil =>
    cases steps' with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons s rest ih =>
    cases steps' with
    | nil => simp at hlen
    | cons s' rest' =>
      obtain ⟨w, u⟩ := s
      obtain ⟨w', u'⟩ := s'
      have hu0 : u = u' := hu 0 (by simp) (by simp)
      subst hu0
      have hw0 : ∀ x ∈ history ++ DirectMasks.records u, w x.key = w' x.key := by
        intro x hx
        exact hw 0 (by simp) (by simp) x (by simpa using hx)
      have hrun := DirectJobWordLocal (geometry first) ow ow' w w'
        (st.inputs u) how (by
          intro x hx
          apply hw0
          rcases List.mem_append.1 hx with hx | hx
          · exact List.mem_append_left _ (mem_records_of_perm hst hx)
          · exact List.mem_append_right _ hx)
      have hstep : referenceStep ow st ⟨geometry first, w, u⟩ =
          referenceStep ow' st ⟨geometry first, w', u⟩ := by
        unfold referenceStep
        simp only
        rw [hrun]
      simp only [directChainJobs, referenceChain]
      rw [hstep]
      have hnext := (DirectJobReferenceStep ow' st ⟨geometry first, w', u⟩
        history hst).1
      refine ih (steps' := rest') (first := first + 1) (ow := w) (ow' := w')
        (st := _) (history := history ++ DirectMasks.records u) (hst := hnext) ?_
        (by simpa using hlen) (fun p h h' => hu (p + 1) (by simpa using h) (by simpa using h'))
        ?_
      · intro x hx
        exact hw0 x (mem_records_of_perm hnext (List.mem_append_left _ hx))
      · intro p h h' x hx
        have := hw (p + 1) (by simpa using h) (by simpa using h') x
          (by simpa [List.take_succ_cons, List.flatMap_cons, List.append_assoc] using hx)
        simpa using this

/-- The legacy constructor is exactly the selected specialization. -/
theorem directChainJobs_selected (first : Nat) (steps : List ((Model.LogicalKey → Nat) × List Bucket)) :
    directChainJobs selectedDirectGeometry first steps = selectedChainJobs first steps := by
  induction steps generalizing first with
  | nil => rfl
  | cons step rest ih =>
    obtain ⟨word, units⟩ := step
    simp only [directChainJobs, selectedChainJobs, ih]

theorem chainRecords_selected (first : Nat) (steps : List ((Model.LogicalKey → Nat) × List Bucket)) :
    chainRecords (selectedChainJobs first steps) =
      steps.flatMap fun s => DirectMasks.records s.2 := by
  simpa only [directChainJobs_selected] using chainRecords_for selectedDirectGeometry first steps

theorem forall₂_selected (first : Nat) {steps : List ((Model.LogicalKey → Nat) × List Bucket)}
    {pops : List (Finset Model.LogicalKey)}
    (h : List.Forall₂ (fun s keys => ((DirectMasks.records s.2).map Rec.key).toFinset = keys)
      steps pops) :
    List.Forall₂ (fun job keys => ((DirectMasks.records job.units).map Rec.key).toFinset = keys)
      (selectedChainJobs first steps) pops := by
  simpa only [directChainJobs_selected] using forall₂_for selectedDirectGeometry first h

theorem chain_congr (first : Nat) (steps steps' : List ((Model.LogicalKey → Nat) × List Bucket))
    (ow ow' : Model.LogicalKey → Nat) (st : ReferenceTable) (history : List Rec)
    (hst : st.records.Perm (DirectPrefix.winners history))
    (how : ∀ x ∈ st.main.flatMap Bucket.recs, ow x.key = ow' x.key)
    (hlen : steps.length = steps'.length)
    (hu : ∀ p (h : p < steps.length) (h' : p < steps'.length), steps[p].2 = steps'[p].2)
    (hw : ∀ p (h : p < steps.length) (h' : p < steps'.length),
      ∀ x ∈ history ++ (steps.take (p + 1)).flatMap (fun s => DirectMasks.records s.2),
        steps[p].1 x.key = steps'[p].1 x.key) :
    referenceChain ow st (selectedChainJobs first steps) =
      referenceChain ow' st (selectedChainJobs first steps') := by
  simpa only [directChainJobs_selected] using
    chain_congr_for selectedDirectGeometry first steps steps' ow ow' st history hst how hlen hu hw

end RebuildBound.DirectJobUniformCycleProof
