import RebuildBound.Proofs.NetworkAverage
import RebuildBound.Proofs.ShadowNet.Glue
import RebuildBound.Spec.P12

/-!
# P12ab: the shadow comparison in `r` blocks (conditional on P12a, P12b, P12c)

The `r`-block version of `P11ab`: P12b, then P12a at stage `lo + 1` (with the
locality of `radixTermTest`), then the node states after stage `lo + 1` are
`capAll (mainEmbed (arrivals of the main keys))`, which are at most the phantom
arrivals; P12c's monotonicity finishes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P12abProof

open RebuildBound.Spec RebuildBound.P11aProof RebuildBound.P11abProof RebuildBound.X1Proof

variable {K : Type} [Fintype K] [DecidableEq K] {r b : ℕ}

omit [Fintype K] in
lemma rnetState_lo_succ {C : ℕ} {pos : K → RNode r b} {ρ : RRoute K r b} (hV : ρ.Valid C pos)
    (lo : ℕ) (h : K → Bits b) :
    rnetState ρ pos lo h (lo + 1) =
      capAll (allRNodes r b) C (mainEmbed (fun V =>
        ((ρ.mainAt h lo).filter (fun x => rdest pos h (lo + 1) x = V)).card)) := by
  have hl : (allRNodes r b).Nodup := Finset.nodup_toList _
  have hsub : ρ.mainAt h (lo + 1) ⊆ ρ.mainAt h lo := hV.mono h lo
  funext q
  obtain ⟨v, s⟩ := q
  have hv : v ∈ allRNodes r b := Finset.mem_toList.mpr (Finset.mem_univ _)
  rw [capAll_mem _ hl _ _ hv]
  have hcount := hV.count h lo v
  cases s
  · rw [capAt_main]
    show ((ρ.mainAt h (lo + 1)).filter (fun x => rdest pos h (lo + 1) x = v)).card = _
    rw [hcount, min_comm]
    rfl
  · rw [capAt_shadow]
    show ((ρ.mainAt h lo \ ρ.mainAt h (lo + 1)).filter
      (fun x => rdest pos h (lo + 1) x = v)).card = _
    have e1 := card_sdiff_filter hsub (fun x => rdest pos h (lo + 1) x = v)
    simp only [mainEmbed]
    omega

lemma radixTermTest_reads (C P : ℕ) (pe q : I) (L lo : ℕ) (R : Bits b) :
    ∀ x y : States (RNode r b), (∀ v : RNode r b, InRange lo R v.2 → ∀ s, x (v, s) = y (v, s)) →
      radixTermTest C P pe q L lo R x = radixTermTest C P pe q L lo R y := by
  unfold radixTermTest
  have := thinAll_readsOnly (T := fun v : RNode r b => InRange lo R v.2)
    (f := termTest P pe L lo R ∘ capAll (allNodes b) C ∘ sumAlong (fun V : RNode r b => V.2))
    (by
      intro x y hxy
      simp only [Function.comp]
      apply termTest_reads
      intro p hp s
      apply capAll_congr_node
      intro s'
      unfold sumAlong
      exact Finset.sum_congr rfl fun V hV => hxy V (by
        rw [Finset.mem_filter] at hV; have h2 : V.2 = p := hV.2
        rw [h2]; exact hp) s')
    (allRNodes r b) (fun _ => q)
  exact fun x y hxy => this x y hxy

end RebuildBound.P12abProof

open RebuildBound.Spec RebuildBound.P11aProof RebuildBound.P11abProof RebuildBound.P12abProof in
theorem RebuildBound.P12ab_of (ha : RebuildBound.Spec.P12a_statement)
    (hb : RebuildBound.Spec.P12b_statement) (hc : RebuildBound.Spec.P12c_statement) :
    RebuildBound.Spec.P12ab_statement := by
  intro K _ _ r b C pos ρ hV lo hlo early P L R q a hq hd hcard he
  have step1 := hb C pos ρ hV lo hlo.le early P L R q a hq hd hcard he
  have step2 : wordAvg (fun h => radixTermTest C P (q a * halfPow (b - lo)) (q a) L lo R
        (rnetState ρ pos lo h b)) =
      wordAvg (fun h => rFirstArrivalTest C P L lo R (q a)
        (fun V => ((ρ.mainAt h lo).filter (fun x => rdest pos h (lo + 1) x = V)).card)) := by
    rw [← wordAvg_condAvg (lo + 1) (fun h => radixTermTest C P (q a * halfPow (b - lo)) (q a) L lo R
      (rnetState ρ pos lo h b))]
    apply RebuildBound.NetworkAverage.wordAvg_congr
    intro h
    rw [ha C pos ρ hV lo R _ (radixTermTest_reads _ _ _ _ _ _ _) (lo + 1) (by omega)
      (by omega) h, rnetState_lo_succ hV lo h]
    rfl
  have mono := (hc (r := r) (b := b) C P L lo R (q a)).1
  refine step1.trans (step2.le.trans ?_)
  apply RebuildBound.NetworkAverage.wordAvg_mono
  intro h
  apply mono
  intro V
  exact Finset.card_le_card (fun x hx => by simp only [Finset.mem_filter] at hx ⊢; exact ⟨Finset.mem_univ _, hx.2⟩)
