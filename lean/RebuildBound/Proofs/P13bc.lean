import RebuildBound.Proofs.P12b
import RebuildBound.Proofs.P12c
import RebuildBound.Spec.P13

/-!
# P13b, P13c: P12b and P12c for a terminal radix node without its cap

P12b's proof with the radix node's shed term removed from the range count
(`rest0` is only the late binary sheds) and the cap removed from the terminal
test; P12c's with `capAll (allNodes b) C` dropped from the terminal class
membership. No obstacle.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P13bcProof

open RebuildBound.Spec RebuildBound.X1Proof RebuildBound.P11aProof RebuildBound.P11bProof
  RebuildBound.P12bProof RebuildBound.P12cProof RebuildBound.P11cProof RebuildBound.P6Proof

section Route

variable {K : Type} [DecidableEq K] {r b : ℕ} {C : ℕ} {pos : K → RNode r b}
  {ρ : RRoute K r b}

/-- The range count without the early keys: the late binary sheds. -/
def rest0 (ρ : RRoute K r b) (lo : ℕ) (R : Bits b) (a : Fin r) (h : K → Bits b)
    (c : K → Fin r) : ℕ :=
  ((ρ.mainAt h lo \ ρ.mainAt h b).filter (fun x => InRange lo R (h x) ∧ c x = a)).card

lemma rRangeCount0_sw (hv : ρ.Valid C pos) (lo : ℕ)
    (early : (K → Bits b) → Finset K) (R : Bits b) (a : Fin r)
    (hdisj : ∀ h, Disjoint (early h) (ρ.mainAt h lo))
    (hearly : ∀ h h', AgreeBelow lo h h' → early h = early h') (h g : K → Bits b)
    (c : K → Fin r) :
    rRangeCount0 ρ lo early R a (sw lo (early h) h g) c =
      ((early h).filter (fun x => InRange lo R (g x) ∧ c x = a)).card +
        rest0 ρ lo R a h c := by
  have hA : AgreeBelow lo h (sw lo (early h) h g) := agreeBelow_sw lo (early h) h g
  have hE : early (sw lo (early h) h g) = early h := (hearly _ _ hA).symm
  have hM : ∀ x ∈ ρ.mainAt h lo, sw lo (early h) h g x = h x := by
    intro x hx
    have hx' : x ∉ early h := Finset.disjoint_right.mp (hdisj h) hx
    simp [sw, hx']
  have hst := rstate_eq_of hv lo h _ hA hM
  have hmain : ∀ j, ρ.mainAt (sw lo (early h) h g) j = ρ.mainAt h j := fun j => by
    simp only [RRoute.mainAt, hst j]
  have e1 : (early h).filter (fun x => InRange lo R (sw lo (early h) h g x) ∧ c x = a) =
      (early h).filter (fun x => InRange lo R (g x) ∧ c x = a) := by
    apply Finset.filter_congr
    intro x hx
    simp only [sw, hx, ↓reduceIte, inRange_mix]
  have e2 : (ρ.mainAt h lo \ ρ.mainAt h b).filter
        (fun x => InRange lo R (sw lo (early h) h g x) ∧ c x = a) =
      (ρ.mainAt h lo \ ρ.mainAt h b).filter (fun x => InRange lo R (h x) ∧ c x = a) := by
    apply Finset.filter_congr
    intro x hx
    rw [hM x (Finset.mem_sdiff.mp hx).1]
  unfold rRangeCount0 rest0
  rw [hE, hmain lo, hmain b, e1, e2]

lemma rest0_update (hv : ρ.Valid C pos) {lo : ℕ} (R : Bits b) (a : Fin r)
    (h : K → Bits b) {x0 : K} (hx0 : x0 ∉ ρ.mainAt h lo) (c : K → Fin r) (u : Fin r) :
    rest0 ρ lo R a h (Function.update c x0 u) = rest0 ρ lo R a h c := by
  unfold rest0
  congr 1
  refine Finset.filter_congr fun x hx => ?_
  have : x ≠ x0 := fun e => hx0 (e ▸ (Finset.mem_sdiff.mp hx).1)
  rw [Function.update_of_ne this]

lemma sum_shadow0 (hv : ρ.Valid C pos) {lo : ℕ} (hlo : lo ≤ b) (R : Bits b) (a : Fin r)
    (h : K → Bits b) (c : K → Fin r) :
    ∑ v ∈ rangeHomes lo R, (sumAlong (fun V : RNode r b => V.2)
      (cnt ((ρ.mainAt h lo).filter (fun x => c x = a))
        (fun x => (rdest pos h b x, slotOf (ρ.mainAt h b) x)))) (v, .shadow) =
      rest0 ρ lo R a h c := by
  rw [sumAlong_cnt]
  simp only [cnt_apply, rdest_b]
  have hs : ∀ v, ((ρ.mainAt h lo).filter (fun x => c x = a)).filter
        (fun x => (h x, slotOf (ρ.mainAt h b) x) = (v, Slot.shadow)) =
      (ρ.mainAt h lo \ ρ.mainAt h b).filter (fun x => h x = v ∧ c x = a) := by
    intro v
    ext x
    by_cases hx : x ∈ ρ.mainAt h b
    · simp [slotOf, hx]
    · simp [slotOf, hx]
      tauto
  simp only [hs]
  unfold rest0
  have hmaps : ((((ρ.mainAt h lo \ ρ.mainAt h b).filter
      (fun x => InRange lo R (h x) ∧ c x = a)) : Finset K) : Set K).MapsTo h
        (rangeHomes lo R) := by
    intro x hx
    simp [rangeHomes, (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2.1]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro x _
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨⟨hx ▸ (Finset.mem_filter.mp hv).2, hc⟩, hx⟩
  · exact fun hx => ⟨hx.2, hx.1.2⟩

lemma radixTermTest0_eq [Fintype K] (hv : ρ.Valid C pos) {lo : ℕ} (hlo : lo ≤ b)
    (q : Fin r → I) (hq : ∑ a, (q a : ℝ) = 1) (P L : ℕ) (R : Bits b) (a : Fin r) (pe : I)
    (h : K → Bits b) :
    radixTermTest0 P pe (q a) L lo R (rnetState ρ pos lo h b) =
      classAvg q (fun c => ∫⁻ e, ((e + rest0 ρ lo R a h c - L : ℕ) : ℝ≥0∞) ∂(binomial P pe)) := by
  unfold radixTermTest0
  rw [rnetState_eq_cnt hv lo h hlo, ← classAvg_cnt_filter q hq (allRNodes r b)
    (Finset.nodup_toList _) _ (fun x => Finset.mem_toList.mpr (Finset.mem_univ _)) a]
  congr 1
  funext c
  simp only [Function.comp_apply]
  unfold termTest
  rw [sum_shadow0 hv hlo R a h c]

end Route

lemma radixTerm0_class {r b : ℕ} (P L lo : ℕ) (pe q : I) (R : Bits b) :
    ClassT (fun _ : RNode r b => (⊤ : ℕ∞)) (radixTermTest0 (r := r) P pe q L lo R) ∧
      CountBounded (P : ℝ≥0∞) (radixTermTest0 (r := r) P pe q L lo R) := by
  obtain ⟨h0, k0⟩ := termTest_class P pe L lo R
  have h2 := RebuildBound.X1_add (fun V : RNode r b => V.2) _ h0
  have k2 := RebuildBound.P6_bound.2.2.1 (P : ℝ≥0∞) (fun V : RNode r b => V.2) _ k0
  exact ⟨RebuildBound.P6_thinAll _ _ (allRNodes r b) _ h2, thinAll_bound' _ _ _ _ k2⟩

end RebuildBound.P13bcProof

open RebuildBound.Spec RebuildBound.X1Proof RebuildBound.P11aProof RebuildBound.P11bProof
  RebuildBound.P12bProof RebuildBound.P13bcProof in
theorem RebuildBound.P13b : RebuildBound.Spec.P13b_statement := by
  intro K _ _ r b C pos ρ hv lo hlo early P L R q a hq hdisj hcard hearly
  set Φ : (K → Bits b) → ℝ≥0∞ := fun h =>
    classAvg q (fun c => ((rRangeCount0 ρ lo early R a h c - L : ℕ) : ℝ≥0∞)) with hΦ
  set T : (K → Bits b) → ℝ≥0∞ := fun h =>
    radixTermTest0 P (q a * halfPow (b - lo)) (q a) L lo R (rnetState ρ pos lo h b) with hT
  have perh : ∀ h, ∑ g, Φ (sw lo (early h) h g) ≤ Fintype.card (K → Bits b) * T h := by
    intro h
    calc ∑ g, Φ (sw lo (early h) h g)
        = ∑ g : K → Bits b, classAvg q (fun c => ((((early h).filter
            (fun x => InRange lo R (g x) ∧ c x = a)).card + rest0 ρ lo R a h c - L : ℕ) :
              ℝ≥0∞)) := by
          simp only [hΦ, rRangeCount0_sw hv lo early R a hdisj hearly h]
      _ = classAvg q (fun c => ∑ g : K → Bits b, (((((early h).filter (fun x => c x = a)).filter
            (fun x => InRange lo R (g x))).card + rest0 ρ lo R a h c - L : ℕ) : ℝ≥0∞)) := by
          rw [sum_classAvg]
          congr 1
          funext c
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.filter_filter]
          congr 4
          exact Finset.filter_congr fun x _ => and_comm
      _ = classAvg q (fun c => Fintype.card (K → Bits b) * ∫⁻ e,
            ((e + rest0 ρ lo R a h c - L : ℕ) : ℝ≥0∞)
              ∂(binomial ((early h).filter (fun x => c x = a)).card (halfPow (b - lo)))) := by
          congr 1
          funext c
          exact sum_count_binomial (InRange lo R) (halfPow (b - lo)) (card_inRange_eq lo hlo R)
            _ (fun e => ((e + rest0 ρ lo R a h c - L : ℕ) : ℝ≥0∞))
      _ = Fintype.card (K → Bits b) * classAvg q (fun c => ∫⁻ e,
            ((e + rest0 ρ lo R a h c - L : ℕ) : ℝ≥0∞)
              ∂(binomial (early h).card (q a * halfPow (b - lo)))) := by
          rw [classAvg_const_mul, classAvg_early q hq a (halfPow (b - lo)) (early h)
            (fun e c => ((e + rest0 ρ lo R a h c - L : ℕ) : ℝ≥0∞))
            (fun e c x hx u => by
              simp only [rest0_update hv R a h (Finset.disjoint_left.mp (hdisj h) hx)])]
      _ ≤ Fintype.card (K → Bits b) * classAvg q (fun c => ∫⁻ e,
            ((e + rest0 ρ lo R a h c - L : ℕ) : ℝ≥0∞)
              ∂(binomial P (q a * halfPow (b - lo)))) := by
          gcongr
          refine classAvg_mono q fun c => ?_
          exact lintegral_binomial_mono _ (fun e e' he => Nat.cast_le.mpr (by omega)) (hcard h)
      _ = Fintype.card (K → Bits b) * T h := by
          simp only [hT]
          rw [radixTermTest0_eq hv hlo q hq]
  exact RebuildBound.NetworkAverage.wordAvg_le_of_involution
    (swp lo early) (swp_involutive lo early hearly) Φ T perh

open RebuildBound.Spec RebuildBound.P12cProof RebuildBound.P13bcProof RebuildBound.P6Proof in
theorem RebuildBound.P13c : RebuildBound.Spec.P13c_statement := by
  intro r b C P L lo R q
  obtain ⟨h0, k0⟩ := radixTerm0_class (r := r) P L lo (q * halfPow (b - lo)) q R
  obtain ⟨h1, k1⟩ := rForest_class C R P _ h0 k0 (lo + 1)
  have h2 := RebuildBound.P6_capAll _ (allRNodes r b) C h1
  have k2 := capAll_bound' P C (allRNodes r b) _ k1
  exact RebuildBound.P6_embed _ P h2 k2
