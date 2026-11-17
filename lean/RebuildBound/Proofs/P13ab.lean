import RebuildBound.Proofs.NetworkAverage
import RebuildBound.Proofs.P12ab
import RebuildBound.Proofs.P12a
import RebuildBound.Spec.P13

/-!
# P13ab: the shadow comparison with a drain-only terminal node (conditional on P13b, P13c)

P12ab's proof with `rRangeCount0`, `radixTermTest0`, `rFirstArrivalTest0`; P12a is the
library's proof.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P13abProof

open RebuildBound.Spec RebuildBound.P11aProof RebuildBound.P11abProof RebuildBound.X1Proof

variable {r b : ℕ}

lemma radixTermTest0_reads (P : ℕ) (pe q : I) (L lo : ℕ) (R : Bits b) :
    ∀ x y : States (RNode r b), (∀ v : RNode r b, InRange lo R v.2 → ∀ s, x (v, s) = y (v, s)) →
      radixTermTest0 P pe q L lo R x = radixTermTest0 P pe q L lo R y := by
  unfold radixTermTest0
  have := thinAll_readsOnly (T := fun v : RNode r b => InRange lo R v.2)
    (f := termTest P pe L lo R ∘ sumAlong (fun V : RNode r b => V.2))
    (by
      intro x y hxy
      simp only [Function.comp]
      apply termTest_reads
      intro p hp s
      unfold sumAlong
      exact Finset.sum_congr rfl fun V hV => hxy V (by
        rw [Finset.mem_filter] at hV; have h2 : V.2 = p := hV.2
        rw [h2]; exact hp) s)
    (allRNodes r b) (fun _ => q)
  exact fun x y hxy => this x y hxy

end RebuildBound.P13abProof

open RebuildBound.Spec RebuildBound.P11aProof RebuildBound.P11abProof RebuildBound.P12abProof
  RebuildBound.P13abProof in
theorem RebuildBound.P13ab_of (hb : RebuildBound.Spec.P13b_statement)
    (hc : RebuildBound.Spec.P13c_statement) : RebuildBound.Spec.P13ab_statement := by
  intro K _ _ r b C pos ρ hV lo hlo early P L R q a hq hd hcard he
  have step1 := hb C pos ρ hV lo hlo.le early P L R q a hq hd hcard he
  have step2 : wordAvg (fun h => radixTermTest0 P (q a * halfPow (b - lo)) (q a) L lo R
        (rnetState ρ pos lo h b)) =
      wordAvg (fun h => rFirstArrivalTest0 C P L lo R (q a)
        (fun V => ((ρ.mainAt h lo).filter (fun x => rdest pos h (lo + 1) x = V)).card)) := by
    rw [← wordAvg_condAvg (lo + 1) (fun h => radixTermTest0 P (q a * halfPow (b - lo)) (q a) L lo R
      (rnetState ρ pos lo h b))]
    apply RebuildBound.NetworkAverage.wordAvg_congr
    intro h
    rw [RebuildBound.P12a C pos ρ hV lo R _ (radixTermTest0_reads _ _ _ _ _ _) (lo + 1) (by omega)
      (by omega) h, RebuildBound.P12abProof.rnetState_lo_succ hV lo h]
    rfl
  have mono := (hc (r := r) (b := b) C P L lo R (q a)).1
  refine step1.trans (step2.le.trans ?_)
  apply RebuildBound.NetworkAverage.wordAvg_mono
  intro h
  apply mono
  intro V
  exact Finset.card_le_card (fun x hx => by simp only [Finset.mem_filter] at hx ⊢; exact ⟨Finset.mem_univ _, hx.2⟩)
