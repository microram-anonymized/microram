import RebuildBound.Proofs.NetworkAverage
import RebuildBound.Proofs.P11a
import RebuildBound.Proofs.P11b
import RebuildBound.Proofs.P11c
import RebuildBound.Proofs.ShadowNet.Glue

/-!
# P11ab: the shadow comparison for one range

Chain: P11b (conditioning order), then P11a at stage `lo + 1` (exactness), then
the phantom comparison: after stage `lo + 1` the node states are the capped
arrivals `arr` of the keys of `mainAt lo`, and `arr ≤ rawArrivals`, so P11c's
monotonicity of `firstArrivalTest` finishes. The averaging of conditional
averages is `wordAvg_condAvg`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P11abProof

open RebuildBound.Spec RebuildBound.P11aProof

variable {K : Type} [Fintype K] [DecidableEq K] {b : ℕ}

lemma netState_lo_succ {C : ℕ} {pos : K → Bits b} {ρ : BlindRoute K b} (hV : ρ.Valid C pos)
    {lo : ℕ} (hlo : lo < b) (h : K → Bits b) :
    netState ρ pos lo h (lo + 1) =
      capAll (allNodes b) C (mainEmbed (fun V => ((ρ.mainAt h lo).filter
        (fun x => dest pos h (lo + 1) x = V)).card)) := by
  have hu : upd h ⟨lo, hlo⟩ (fun x => h x ⟨lo, hlo⟩) = h := by
    funext x
    simp [upd]
  have := netState_succ hV lo h hlo le_rfl (fun x => h x ⟨lo, hlo⟩)
  rw [hu] at this
  rw [this]
  congr 1
  funext q
  obtain ⟨v, s⟩ := q
  rw [cnt_apply]
  cases s
  · simp only [mainEmbed]
    congr 1
    refine Finset.filter_congr fun x hx => ?_
    simp [slotOf, hx]
  · simp only [mainEmbed]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    simp [slotOf, hx]

end RebuildBound.P11abProof

open RebuildBound.Spec RebuildBound.P11aProof RebuildBound.P11abProof in
theorem RebuildBound.P11ab : RebuildBound.Spec.P11ab_statement := by
  intro K _ _ b C pos ρ hV lo hlo early P L R hd hc he
  have hN0 : (Fintype.card (K → Bits b) : ℝ≥0∞)⁻¹ * 1 ≠ 0 := by simp
  have step1 := RebuildBound.P11b C pos ρ hV lo hlo.le early P L R hd hc he
  have step2 : wordAvg (fun h => termTest P (halfPow (b - lo)) L lo R (netState ρ pos lo h b)) =
      wordAvg (fun h => firstArrivalTest C P L lo R
        (fun V => ((ρ.mainAt h lo).filter (fun x => dest pos h (lo + 1) x = V)).card)) := by
    rw [← wordAvg_condAvg (lo + 1) (fun h => termTest P (halfPow (b - lo)) L lo R
      (netState ρ pos lo h b))]
    apply RebuildBound.NetworkAverage.wordAvg_congr
    intro h
    rw [RebuildBound.P11a C pos ρ hV lo R _ (termTest_reads _ _ _ _ _) (lo + 1) (by omega)
      (by omega) h, netState_lo_succ hV hlo h]
    rfl
  have mono := (RebuildBound.P11c_class (b := b) C P L lo R).1
  refine step1.trans (step2.le.trans ?_)
  apply RebuildBound.NetworkAverage.wordAvg_mono
  intro h
  apply mono
  intro V
  exact Finset.card_le_card (fun x hx => by simp only [Finset.mem_filter] at hx ⊢; exact ⟨Finset.mem_univ _, hx.2⟩)
