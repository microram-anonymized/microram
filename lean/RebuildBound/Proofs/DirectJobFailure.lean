import RebuildBound.Spec.DirectJobFailure
import RebuildBound.Proofs.DirectJobPublication
import RebuildBound.Proofs.DirectJobFinishBounds

namespace RebuildBound
open Model Model.DirectJob

namespace DirectJobFailureLemmas

theorem first_failure (trace : List CheckEvent) (e : CheckEvent)
    (h : firstFailure trace = some e) : e ∈ trace ∧ e.capacity < e.occupancy := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  exact ⟨hm, by simpa [CheckEvent.passed] using hp⟩

end DirectJobFailureLemmas

theorem DirectJobBAnalytical : Spec.DirectJobBAnalytical_statement := by
  intro g word inp
  unfold buildB
  rw [DirectJobDrainSimulation]
  cases hf : firstFailure (analyticalB g word inp).trace <;>
    simp [analyticalB, analyticalBTable] at hf ⊢ <;> rw [hf]

theorem DirectJobSimulation : Spec.DirectJobSimulation_statement := by
  intro g oldWord word inp
  unfold runJob
  split
  · rfl
  · split
    · rfl
    · split
      · rename_i hd
        simp only [analyticalJob, hd, ↓reduceIte]
        rw [DirectJobBAnalytical]
        cases firstFailure (analyticalB g word inp).trace <;> rfl
      · rename_i hd
        simp only [analyticalJob, hd, ↓reduceIte,
          DirectJobFinishLemmas.firstFailure_append]
        rw [DirectJobASimulation]
        cases firstFailure (analyticalA g word inp.aMain).trace with
        | some e => rfl
        | none =>
          simp only [Option.or]
          rw [DirectJobBAnalytical]
          cases firstFailure (analyticalB g word inp).trace with
          | some e => rfl
          | none =>
            simp only [distributeABounded]
            cases firstFailure (distributeA g word
                (aOperational (analyticalA g word inp.aMain).state inp.aTier
                  (analyticalBTable g word inp).tier)).trace with
            | some e => rfl
            | none =>
              dsimp only
              rw [DirectJobFinishSimulation]
              cases firstFailure (analyticalFinish g word (analyticalBTable g word inp)
                  (analyticalA g word inp.aMain).state.main
                  (distributeA g word (aOperational (analyticalA g word inp.aMain).state
                    inp.aTier (analyticalBTable g word inp).tier)).leaves).trace <;> rfl

theorem DirectJobRangeFailure : Spec.DirectJobRangeFailure_statement := by
  intro g word inp bTier e he
  unfold distributeABounded at he
  cases hf : firstFailure (distributeA g word
      (aOperational (analyticalA g word inp.aMain).state inp.aTier bTier)).trace with
  | none => simp [hf] at he
  | some event =>
    simp only [hf, Except.error.injEq] at he
    subst event
    obtain ⟨hm, hfail⟩ := DirectJobFailureLemmas.first_failure _ e hf
    unfold aRangeWitness
    cases hr : g.ranges with
    | direct => simp [distributeA, hr] at hm
    | dfs i r p =>
      simp only [distributeA, hr, List.mem_map] at hm
      obtain ⟨⟨node, ordinal⟩, hnode, heq⟩ := hm
      subst e
      let pred := fun x : Rec => g.home (word x.key) / 2 ^ i / 2 ^ (r - node.1) == node.2
      have hsub : (aOperational (analyticalA g word inp.aMain).state inp.aTier bTier).Sublist
          (aResidual (analyticalA g word inp.aMain).state inp.aTier) := List.filter_sublist
      have hsub := hsub.filter pred
      have hcount := hsub.length_le
      refine ⟨⟨⟨.distributeA, .dfs node.1 node.2, ordinal⟩,
        ((aResidual (analyticalA g word inp.aMain).state inp.aTier).filter pred).length,
        min p (64 * 2 ^ (r - node.1))⟩, ?_, ?_⟩
      · simp only [distributeA, hr, List.mem_map]
        exact ⟨(node, ordinal), hnode, rfl⟩
      · exact lt_of_lt_of_le hfail hcount

theorem DirectJobFirstFailure : Spec.DirectJobFirstFailure_statement := by
  intro g oldWord word inp e
  have hiff : runJob g oldWord word inp = .failed e ↔
      g.Valid ∧ inp.Valid g oldWord ∧
        firstFailure (analyticalJob g word inp).trace = some e := by
    rw [DirectJobSimulation]
    by_cases hg : g.Valid
    · by_cases hi : inp.Valid g oldWord
      · simp only [hg, hi, not_true_eq_false, ite_false, true_and]
        cases firstFailure (analyticalJob g word inp).trace <;> simp
      · simp [hg, hi]
    · simp [hg]
  refine ⟨hiff, ?_⟩
  intro hf
  obtain ⟨hm, hcap⟩ := DirectJobFailureLemmas.first_failure _ e (hiff.mp hf).2.2
  exact ⟨hm, hcap, by intro out; rw [hf]; intro h; cases h⟩

theorem DirectJobFailureContainment : Spec.DirectJobFailureContainment_statement := by
  intro g oldWord word inp e hs
  have hv := ((DirectJobFirstFailure g oldWord word inp e).1.mp hs)
  obtain ⟨hg, hi, _⟩ := hv
  unfold runJob at hs
  simp only [hg, hi, not_true_eq_false, ite_false] at hs
  unfold failureWitness
  by_cases hd : g.digit = 1
  · simp only [hd, ↓reduceIte] at hs
    cases hb : buildB g word inp with
    | ok b => simp [hb] at hs
    | error event =>
      exact Or.inl ((DirectJobBFailure g word inp hi.2.2.2.2.1).mp ⟨event, hb⟩)
  · simp only [hd, ↓reduceIte] at hs
    have hd' : 2 ≤ g.digit := by have := hg.1; omega
    cases ha : prepareA g word inp.aMain with
    | error event =>
      have hf := DirectJobAFailureCheck g word inp.aMain event ha
      exact Or.inr (Or.inl ⟨event, hf.1, hf.2.1⟩)
    | ok a =>
      simp only [ha] at hs
      have hea := DirectJobPublicationLemmas.prepare_success g word inp.aMain a ha
      cases hb : buildB g word inp with
      | error event =>
        exact Or.inl ((DirectJobBFailure g word inp hi.2.2.2.2.1).mp ⟨event, hb⟩)
      | ok b =>
        simp only [hb] at hs
        cases hl : distributeABounded g word (aOperational a inp.aTier b.tier) with
        | error event =>
          rw [hea] at hl
          exact Or.inr (Or.inr (Or.inl (DirectJobRangeFailure g word inp b.tier event hl)))
        | ok leaves =>
          simp only [hl] at hs
          cases ho : finishBounded g word b a.main leaves with
          | ok out => simp [ho] at hs
          | error event =>
            have hel := DirectJobPublicationLemmas.distribution_success g word _ leaves hl
            rw [hel, hea] at ho
            exact Or.inr (Or.inr (Or.inr
              (DirectJobFinishFailureExcess g oldWord word inp b event hg hd' hi hb ho)))

end RebuildBound
