import RebuildBound.Spec.DirectJobProbability
import RebuildBound.Proofs.DirectJobFailure
import RebuildBound.Proofs.FiniteLaw
import RebuildBound.Proofs.P8a
import RebuildBound.Proofs.P7fin
import RebuildBound.Proofs.StageAvg

open MeasureTheory
open scoped ENNReal NNReal
namespace RebuildBound
open Model Model.DirectJob Spec

theorem DirectJobBCount : Spec.DirectJobBCount_statement := by
  intro g word inp
  rw [DirectJobBExcess, G1Proof.list_sum_range, Finset.sum_range]
  rfl

private theorem event_budget {Hist Word Value : Type} [Fintype Hist] [Fintype Word]
    (weight : Hist → ℝ≥0∞) (wordFn : Word → Value)
    (E B A U : Hist → Value → Prop) (bB bA bUnion : ℝ≥0∞)
    (hcover : ∀ hist h, E hist (wordFn h) → (B hist (wordFn h) ∨ A hist (wordFn h)) ∨ U hist (wordFn h))
    (hB : FiniteLawProof.prob weight wordFn B ≤ bB)
    (hA : FiniteLawProof.prob weight wordFn A ≤ bA)
    (hU : FiniteLawProof.prob weight wordFn U ≤ bUnion) :
    FiniteLawProof.prob weight wordFn E ≤ bB + bA + bUnion := by
  calc
    FiniteLawProof.prob weight wordFn E ≤
        FiniteLawProof.prob weight wordFn (fun hist w => (B hist w ∨ A hist w) ∨ U hist w) :=
      FiniteLawProof.prob_mono weight wordFn hcover
    _ ≤ FiniteLawProof.prob weight wordFn (fun hist w => B hist w ∨ A hist w) +
        FiniteLawProof.prob weight wordFn U := FiniteLawProof.prob_or weight wordFn _ _
    _ ≤ (FiniteLawProof.prob weight wordFn B + FiniteLawProof.prob weight wordFn A) +
        FiniteLawProof.prob weight wordFn U := add_le_add (FiniteLawProof.prob_or weight wordFn _ _) le_rfl
    _ ≤ bB + bA + bUnion := add_le_add (add_le_add hB hA) hU

theorem DirectJobFailureProbability : Spec.DirectJobFailureProbability_statement := by
  intro Hist Word ih iw weight wordFn g oldWord inputs bB bA bUnion hB hA hUnion
  classical
  -- The statement's indicators use the standard instances; `prob`'s are classical.
  have h := @event_budget Hist Word (Model.LogicalKey → Nat) ih iw weight wordFn
    (fun hist w => ∃ e, runJob g (oldWord hist) w (inputs hist w) = .failed e)
    (fun hist w => g.bCapacity < bExcess g w (inputs hist w))
    (fun hist w => (inputs hist w).aTier.length ≤ g.aTierCapacity ∧
      (aRouteWitness g w (inputs hist w) ∨ aRangeWitness g w (inputs hist w)))
    (fun hist w => g.outputCapacity < (inputs hist w).excess g w) bB bA bUnion
    (fun hist h he => by
      obtain ⟨e, he⟩ := he
      have hfit := ((DirectJobFirstFailure g (oldWord hist) (wordFn h)
        (inputs hist (wordFn h)) e).1.mp he).2.1.2.2.1
      have hf := DirectJobFailureContainment g (oldWord hist) (wordFn h) (inputs hist (wordFn h)) e he
      rcases hf with hb | ha | hr | hu
      · exact Or.inl (Or.inl hb)
      · exact Or.inl (Or.inr ⟨hfit, Or.inl ha⟩)
      · exact Or.inl (Or.inr ⟨hfit, Or.inr hr⟩)
      · exact Or.inr hu)
    (by unfold FiniteLawProof.prob; convert hB)
    (by unfold FiniteLawProof.prob; convert hA)
    (by unfold FiniteLawProof.prob; convert hUnion)
  unfold FiniteLawProof.prob at h
  convert h

end RebuildBound
