import RebuildBound.Proofs.P12b.Class
import RebuildBound.Proofs.ShadowNet.Swap

/-!
# P12b: the conditioning order and the class average

`wordAvg (classAvg (rRangeCount - L)₊) ≤ wordAvg radixTermTest(final node states)`.

Proof outline, for fixed words `h`; `E = early h`, `rest h c` the range count
without the early keys (late binary sheds and radix sheds).

1. **Swap** (P11b's `swp`): `|H| · Σ_h F h = Σ_h Σ_g F (sw (early h) h g)`, where
   `sw` replaces the bits `≥ lo` of the early keys of `h` by those of `g`.
2. **Invariance** (`rRangeCount_sw`): `sw (early h) h g` agrees with `h` below
   `lo` and on main after stage `lo`, so by blindness the route runs the same:
   the count is `#{x ∈ E : InRange (g x) ∧ c x = a} + rest h c`.
3. **Words of the early keys** (P11b's `sum_count_binomial`, for each class
   assignment `c`): the early count is `Bin(#{x ∈ E : c x = a}, 2^-(b-lo))`.
4. **Classes of the early keys** (`classAvg_early`): `rest h` does not read the
   classes of `E` (disjoint from main after stage `lo`), so averaging them gives
   `Bin(|E|, q_a 2^-(b-lo))`; pad to `Bin(P, ·)` (`lintegral_binomial_mono`).
5. **Classes of the rest** (`radixTermTest_eq`): the final node states are the
   count vector of main after stage `lo`; averaging the classes is the thinning
   of every node by `q a` (`classAvg_cnt_filter`), and the sum into the radix
   node, the cap and the shadow sum over the range give `rest h c`.

Probability API: the binomial side is measure-based (`binomial`, `lintegral`,
X1's Pascal rule); the word and class averages are the finite sums of
`wordAvg` and `classAvg`, handled by explicit involutions (`Equiv.sum_comp`). No
obstacle beyond X1's (no recurrence in `n` for `binomial n p` in Mathlib).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P12bProof

open RebuildBound.Spec RebuildBound.X1Proof RebuildBound.P11aProof RebuildBound.P11bProof

section Route

variable {K : Type} [DecidableEq K] {r b : ℕ} {C : ℕ} {pos : K → RNode r b}
  {ρ : RRoute K r b}

lemma rmainAt_sub (hv : ρ.Valid C pos) (h : K → Bits b) {lo j : ℕ} (hj : lo ≤ j) :
    ρ.mainAt h j ⊆ ρ.mainAt h lo := by
  induction j, hj using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ j _ ih => exact (hv.mono h j).trans ih

/-- The route runs the same under words that agree below `lo` and on the keys of
main after stage `lo`. -/
lemma rstate_eq_of (hv : ρ.Valid C pos) (lo : ℕ) (h h' : K → Bits b)
    (hA : AgreeBelow lo h h') (hM : ∀ x ∈ ρ.mainAt h lo, h' x = h x) :
    ∀ j, ρ.state h' j = ρ.state h j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    show ρ.step j (ρ.state h' j) h' = ρ.step j (ρ.state h j) h
    rw [ih]
    refine (hv.blind j _ h h' ?_).symm
    intro x hx i hi
    rcases lt_or_ge j lo with hjl | hjl
    · exact hA x i (lt_of_le_of_lt hi hjl)
    · have hx' : x ∈ ρ.mainAt h lo := rmainAt_sub hv h hjl hx
      rw [hM x hx']

/-- The range count without the early keys: the late binary sheds and the radix
node's sheds at the range's buckets. -/
def rest (ρ : RRoute K r b) (C lo : ℕ) (R : Bits b) (a : Fin r) (h : K → Bits b)
    (c : K → Fin r) : ℕ :=
  ((ρ.mainAt h lo \ ρ.mainAt h b).filter (fun x => InRange lo R (h x) ∧ c x = a)).card +
    ∑ p ∈ rangeHomes lo R, (((ρ.mainAt h b).filter (fun x => h x = p ∧ c x = a)).card - C)

/-- The range count after the swap: the early keys counted by their `g`-words,
plus the rest under `h`. -/
lemma rRangeCount_sw (hv : ρ.Valid C pos) (lo : ℕ) (hlo : lo ≤ b)
    (early : (K → Bits b) → Finset K) (R : Bits b) (a : Fin r)
    (hdisj : ∀ h, Disjoint (early h) (ρ.mainAt h lo))
    (hearly : ∀ h h', AgreeBelow lo h h' → early h = early h') (h g : K → Bits b)
    (c : K → Fin r) :
    rRangeCount ρ C lo early R a (sw lo (early h) h g) c =
      ((early h).filter (fun x => InRange lo R (g x) ∧ c x = a)).card +
        rest ρ C lo R a h c := by
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
  have e3 : ∀ p, (ρ.mainAt h b).filter (fun x => sw lo (early h) h g x = p ∧ c x = a) =
      (ρ.mainAt h b).filter (fun x => h x = p ∧ c x = a) := by
    intro p
    apply Finset.filter_congr
    intro x hx
    rw [hM x (rmainAt_sub hv h hlo hx)]
  unfold rRangeCount rest
  rw [hE, hmain lo, hmain b, e1, e2]
  simp only [e3]
  ring

/-- The rest does not read the classes of the keys outside main after stage `lo`. -/
lemma rest_update (hv : ρ.Valid C pos) {lo : ℕ} (hlo : lo ≤ b) (R : Bits b) (a : Fin r)
    (h : K → Bits b) {x0 : K} (hx0 : x0 ∉ ρ.mainAt h lo) (c : K → Fin r) (u : Fin r) :
    rest ρ C lo R a h (Function.update c x0 u) = rest ρ C lo R a h c := by
  unfold rest
  have e1 : (ρ.mainAt h lo \ ρ.mainAt h b).filter
        (fun x => InRange lo R (h x) ∧ Function.update c x0 u x = a) =
      (ρ.mainAt h lo \ ρ.mainAt h b).filter (fun x => InRange lo R (h x) ∧ c x = a) := by
    refine Finset.filter_congr fun x hx => ?_
    have : x ≠ x0 := fun e => hx0 (e ▸ (Finset.mem_sdiff.mp hx).1)
    rw [Function.update_of_ne this]
  have e2 : ∀ p, (ρ.mainAt h b).filter (fun x => h x = p ∧ Function.update c x0 u x = a) =
      (ρ.mainAt h b).filter (fun x => h x = p ∧ c x = a) := by
    intro p
    refine Finset.filter_congr fun x hx => ?_
    have : x ≠ x0 := fun e => hx0 (e ▸ rmainAt_sub hv h hlo hx)
    rw [Function.update_of_ne this]
  rw [e1]
  simp only [e2]

/-! ### The radix terminal test as a class average -/

omit [DecidableEq K] in
lemma rdest_b (pos : K → RNode r b) (h : K → Bits b) (x : K) : (rdest pos h b x).2 = h x :=
  funext fun i => by simp [rdest]

lemma rnetState_eq_cnt (hv : ρ.Valid C pos) (lo : ℕ) (h : K → Bits b) {j : ℕ} (hlo : lo ≤ j) :
    rnetState ρ pos lo h j =
      cnt (ρ.mainAt h lo) (fun x => (rdest pos h j x, slotOf (ρ.mainAt h j) x)) := by
  funext q
  obtain ⟨v, s⟩ := q
  rw [cnt_apply]
  cases s
  · rw [filter_slot_main (rmainAt_sub hv h hlo)]
    rfl
  · rw [filter_slot_shadow]
    rfl

lemma capAll_shadow (C : ℕ) (y : States (Bits b)) (v : Bits b) :
    capAll (allNodes b) C y (v, .shadow) = y (v, .shadow) + (y (v, .main) - C) := by
  rw [capAll_mem (allNodes b) (Finset.nodup_toList _) C y
    (Finset.mem_toList.mpr (Finset.mem_univ v)), capAt_shadow]

/-- The shadow sum over the range, after the sum into the radix nodes and the cap,
of the class-`a` keys of main after stage `lo`, is the rest. -/
lemma sum_shadow_cap (hv : ρ.Valid C pos) {lo : ℕ} (hlo : lo ≤ b) (R : Bits b) (a : Fin r)
    (h : K → Bits b) (c : K → Fin r) :
    ∑ v ∈ rangeHomes lo R, capAll (allNodes b) C (sumAlong (fun V : RNode r b => V.2)
      (cnt ((ρ.mainAt h lo).filter (fun x => c x = a))
        (fun x => (rdest pos h b x, slotOf (ρ.mainAt h b) x)))) (v, .shadow) =
      rest ρ C lo R a h c := by
  have hsub := rmainAt_sub hv h hlo
  rw [sumAlong_cnt]
  simp only [capAll_shadow, cnt_apply, rdest_b]
  have hs : ∀ v, ((ρ.mainAt h lo).filter (fun x => c x = a)).filter
        (fun x => (h x, slotOf (ρ.mainAt h b) x) = (v, Slot.shadow)) =
      (ρ.mainAt h lo \ ρ.mainAt h b).filter (fun x => h x = v ∧ c x = a) := by
    intro v
    ext x
    by_cases hx : x ∈ ρ.mainAt h b
    · simp [slotOf, hx]
    · simp [slotOf, hx]
      tauto
  have hm : ∀ v, ((ρ.mainAt h lo).filter (fun x => c x = a)).filter
        (fun x => (h x, slotOf (ρ.mainAt h b) x) = (v, Slot.main)) =
      (ρ.mainAt h b).filter (fun x => h x = v ∧ c x = a) := by
    intro v
    ext x
    by_cases hx : x ∈ ρ.mainAt h b
    · simp [slotOf, hx, hsub hx]
      tauto
    · simp [slotOf, hx]
  simp only [hs, hm]
  rw [Finset.sum_add_distrib]
  unfold rest
  congr 1
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

lemma radixTermTest_eq [Fintype K] (hv : ρ.Valid C pos) {lo : ℕ} (hlo : lo ≤ b)
    (q : Fin r → I) (hq : ∑ a, (q a : ℝ) = 1) (P L : ℕ) (R : Bits b) (a : Fin r) (pe : I)
    (h : K → Bits b) :
    radixTermTest C P pe (q a) L lo R (rnetState ρ pos lo h b) =
      classAvg q (fun c => ∫⁻ e, ((e + rest ρ C lo R a h c - L : ℕ) : ℝ≥0∞) ∂(binomial P pe)) := by
  unfold radixTermTest
  rw [rnetState_eq_cnt hv lo h hlo, ← classAvg_cnt_filter q hq (allRNodes r b)
    (Finset.nodup_toList _) _ (fun x => Finset.mem_toList.mpr (Finset.mem_univ _)) a]
  congr 1
  funext c
  simp only [Function.comp_apply]
  unfold termTest
  rw [sum_shadow_cap hv hlo R a h c]

end Route

/-! ### Exchanging the word sum and the class average -/

lemma sum_classAvg {K α : Type} [Fintype K] [DecidableEq K] [Fintype α] {r : ℕ} (q : Fin r → I)
    (F : α → (K → Fin r) → ℝ≥0∞) :
    ∑ g, classAvg q (F g) = classAvg q (fun c => ∑ g, F g c) := by
  simp only [classAvg_eq, Finset.mul_sum]
  exact Finset.sum_comm

end RebuildBound.P12bProof

open RebuildBound.Spec RebuildBound.X1Proof RebuildBound.P11aProof RebuildBound.P11bProof
  RebuildBound.P12bProof in
theorem RebuildBound.P12b : RebuildBound.Spec.P12b_statement := by
  intro K _ _ r b C pos ρ hv lo hlo early P L R q a hq hdisj hcard hearly
  set Φ : (K → Bits b) → ℝ≥0∞ := fun h =>
    classAvg q (fun c => ((rRangeCount ρ C lo early R a h c - L : ℕ) : ℝ≥0∞)) with hΦ
  set T : (K → Bits b) → ℝ≥0∞ := fun h =>
    radixTermTest C P (q a * halfPow (b - lo)) (q a) L lo R (rnetState ρ pos lo h b) with hT
  have perh : ∀ h, ∑ g, Φ (sw lo (early h) h g) ≤ Fintype.card (K → Bits b) * T h := by
    intro h
    calc ∑ g, Φ (sw lo (early h) h g)
        = ∑ g : K → Bits b, classAvg q (fun c => ((((early h).filter
            (fun x => InRange lo R (g x) ∧ c x = a)).card + rest ρ C lo R a h c - L : ℕ) :
              ℝ≥0∞)) := by
          simp only [hΦ, rRangeCount_sw hv lo hlo early R a hdisj hearly h]
      _ = classAvg q (fun c => ∑ g : K → Bits b, (((((early h).filter (fun x => c x = a)).filter
            (fun x => InRange lo R (g x))).card + rest ρ C lo R a h c - L : ℕ) : ℝ≥0∞)) := by
          rw [sum_classAvg]
          congr 1
          funext c
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.filter_filter]
          congr 4
          exact Finset.filter_congr fun x _ => and_comm
      _ = classAvg q (fun c => Fintype.card (K → Bits b) * ∫⁻ e,
            ((e + rest ρ C lo R a h c - L : ℕ) : ℝ≥0∞)
              ∂(binomial ((early h).filter (fun x => c x = a)).card (halfPow (b - lo)))) := by
          congr 1
          funext c
          exact sum_count_binomial (InRange lo R) (halfPow (b - lo)) (card_inRange_eq lo hlo R)
            _ (fun e => ((e + rest ρ C lo R a h c - L : ℕ) : ℝ≥0∞))
      _ = Fintype.card (K → Bits b) * classAvg q (fun c => ∫⁻ e,
            ((e + rest ρ C lo R a h c - L : ℕ) : ℝ≥0∞)
              ∂(binomial (early h).card (q a * halfPow (b - lo)))) := by
          rw [classAvg_const_mul, classAvg_early q hq a (halfPow (b - lo)) (early h)
            (fun e c => ((e + rest ρ C lo R a h c - L : ℕ) : ℝ≥0∞))
            (fun e c x hx u => by
              simp only [rest_update hv hlo R a h (Finset.disjoint_left.mp (hdisj h) hx)])]
      _ ≤ Fintype.card (K → Bits b) * classAvg q (fun c => ∫⁻ e,
            ((e + rest ρ C lo R a h c - L : ℕ) : ℝ≥0∞)
              ∂(binomial P (q a * halfPow (b - lo)))) := by
          gcongr
          refine classAvg_mono q fun c => ?_
          exact lintegral_binomial_mono _ (fun e e' he => Nat.cast_le.mpr (by omega)) (hcard h)
      _ = Fintype.card (K → Bits b) * T h := by
          simp only [hT]
          rw [radixTermTest_eq hv hlo q hq]
  exact RebuildBound.NetworkAverage.wordAvg_le_of_involution
    (swp lo early) (swp_involutive lo early hearly) Φ T perh
