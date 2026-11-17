import RebuildBound.Spec.P11
import RebuildBound.Proofs.X1
import RebuildBound.Proofs.NetworkAverage
import RebuildBound.Proofs.ShadowNet.Swap

/-!
# P11b: the conditioning order

`wordAvg (rangeCount - L)₊ ≤ wordAvg termTest(late sheds)`.

Proof outline. Write `F h = (rangeCount h - L)₊` and `T h` for the terminal test.

1. **Swap.** `sw lo E h g` replaces, for the keys of `E`, the bits `≥ lo` of `h`
   by those of `g`. The map `(h, g) ↦ (sw (early h) h g, sw (early h) g h)` is an
   involution of `H × H` (`H` the word assignments), because `early` is fixed by
   the bits below `lo`. Hence `|H| · Σ_h F h = Σ_h Σ_g F (sw (early h) h g)`.
2. **Invariance.** `sw (early h) h g` agrees with `h` below `lo` and on the keys of
   main after stage `lo` (disjoint from the early list), so by blindness the route
   runs the same (`state_eq_of`), the late count is that of `h`, and the early
   count is the number of early keys whose `g`-word lies in the range.
3. **Counting.** For a fixed finset `E`, the number of keys of `E` whose uniform
   word satisfies `Q` is `Bin(|E|, p)` when `Q` has probability `p`
   (`sum_count_binomial`, by induction on `E`, resampling one coordinate).
   `InRange lo R` has `2^lo` of the `2^b` words, so `p = 2^-(b-lo)`.
4. **Padding.** `|early h| ≤ P` and stochastic monotonicity of `Bin(n, p)` in `n`
   (`lintegral_binomial_mono`, X1), and the shadow sum over the range's homes is
   the late count (`sum_shadow_eq`).

Probability API: the binomial side stays measure-based (`binomial`, `lintegral`,
X1's `lintegral_binomial_succ`); the averages over words are the finite sums of
`wordAvg`, handled with `Equiv.sum_comp` on explicit involutions. No obstacle.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P11bProof

open RebuildBound.Spec RebuildBound.X1Proof

/-! ### Step 3: the counting lemma -/

/-! ### The range has probability `2^-(b-lo)` -/

/-! ### Steps 1 and 2: the swap and the invariance of the route -/

section Route

variable {K : Type} [DecidableEq K] {b : ℕ}

variable {C : ℕ} {pos : K → Bits b} {ρ : BlindRoute K b}

lemma mainAt_sub (hv : ρ.Valid C pos) (h : K → Bits b) {lo j : ℕ} (hj : lo ≤ j) :
    ρ.mainAt h j ⊆ ρ.mainAt h lo := by
  induction j, hj using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ j _ ih => exact (hv.mono h j).trans ih

/-- The route runs the same under words that agree below `lo` and on the keys of
main after stage `lo`. -/
lemma state_eq_of (hv : ρ.Valid C pos) (lo : ℕ) (h h' : K → Bits b)
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
    · have hx' : x ∈ ρ.mainAt h lo := mainAt_sub hv h hjl hx
      rw [hM x hx']

/-- The range count after the swap: the early keys counted by their `g`-words,
plus the late count of `h`. -/
lemma rangeCount_sw (hv : ρ.Valid C pos) (lo : ℕ) (early : (K → Bits b) → Finset K)
    (R : Bits b) (hdisj : ∀ h, Disjoint (early h) (ρ.mainAt h lo))
    (hearly : ∀ h h', AgreeBelow lo h h' → early h = early h') (h g : K → Bits b) :
    rangeCount ρ lo early R (sw lo (early h) h g) =
      ((early h).filter (fun x => InRange lo R (g x))).card +
      ((ρ.mainAt h lo \ ρ.mainAt h b).filter (fun x => InRange lo R (h x))).card := by
  have hA : AgreeBelow lo h (sw lo (early h) h g) := agreeBelow_sw lo (early h) h g
  have hE : early (sw lo (early h) h g) = early h := (hearly _ _ hA).symm
  have hM : ∀ x ∈ ρ.mainAt h lo, sw lo (early h) h g x = h x := by
    intro x hx
    have hx' : x ∉ early h := Finset.disjoint_right.mp (hdisj h) hx
    simp [sw, hx']
  have hst := state_eq_of hv lo h _ hA hM
  have hmain : ∀ j, ρ.mainAt (sw lo (early h) h g) j = ρ.mainAt h j := fun j => by
    simp only [BlindRoute.mainAt, hst j]
  have e1 : (early h).filter (fun x => InRange lo R (sw lo (early h) h g x)) =
      (early h).filter (fun x => InRange lo R (g x)) := by
    apply Finset.filter_congr
    intro x hx
    simp only [sw, hx, ↓reduceIte]
    exact inRange_mix lo R (h x) (g x)
  have e2 : (ρ.mainAt h lo \ ρ.mainAt h b).filter
        (fun x => InRange lo R (sw lo (early h) h g x)) =
      (ρ.mainAt h lo \ ρ.mainAt h b).filter (fun x => InRange lo R (h x)) := by
    apply Finset.filter_congr
    intro x hx
    rw [hM x (Finset.mem_sdiff.mp hx).1]
  unfold rangeCount
  rw [hE, hmain lo, hmain b, e1, e2]

/-- Step 4: the shadow counts over the range's homes add up to the late count. -/
lemma sum_shadow_eq (ρ : BlindRoute K b) (pos : K → Bits b) (lo : ℕ) (R : Bits b)
    (h : K → Bits b) :
    ∑ v ∈ rangeHomes lo R, netState ρ pos lo h b (v, .shadow) =
      ((ρ.mainAt h lo \ ρ.mainAt h b).filter (fun x => InRange lo R (h x))).card := by
  have hdest : ∀ x, dest pos h b x = h x := fun x => funext fun i => by simp [dest, i.isLt]
  simp only [netState, hdest]
  have hmaps : ((((ρ.mainAt h lo \ ρ.mainAt h b).filter (fun x => InRange lo R (h x))) :
      Finset K) : Set K).MapsTo h (rangeHomes lo R) := by
    intro x hx
    simp [rangeHomes, (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro x _
  constructor
  · intro hx
    exact ⟨hx ▸ (Finset.mem_filter.mp hv).2, hx⟩
  · exact fun hx => hx.2

lemma termTest_eq (P : ℕ) (p : I) (L lo : ℕ) (R : Bits b) (ρ : BlindRoute K b)
    (pos : K → Bits b) (h : K → Bits b) :
    termTest P p L lo R (netState ρ pos lo h b) =
      ∫⁻ e, (((e + ((ρ.mainAt h lo \ ρ.mainAt h b).filter
        (fun x => InRange lo R (h x))).card) - L : ℕ) : ℝ≥0∞) ∂(binomial P p) := by
  unfold termTest
  rw [sum_shadow_eq]

end Route

end RebuildBound.P11bProof

open RebuildBound.Spec RebuildBound.X1Proof RebuildBound.P11bProof in
theorem RebuildBound.P11b : RebuildBound.Spec.P11b_statement := by
  intro K _ _ b C pos ρ hv lo hlo early P L R hdisj hcard hearly
  apply RebuildBound.NetworkAverage.wordAvg_le_of_involution
    (swp lo early) (swp_involutive lo early hearly)
  intro h
  simp only [swp]
  set s := ((ρ.mainAt h lo \ ρ.mainAt h b).filter (fun x => InRange lo R (h x))).card
  have hF : ∀ g, ((rangeCount ρ lo early R (sw lo (early h) h g) - L : ℕ) : ℝ≥0∞) =
      ((((early h).filter (fun x => InRange lo R (g x))).card + s - L : ℕ) : ℝ≥0∞) :=
    fun g => by rw [rangeCount_sw hv lo early R hdisj hearly h g]
  rw [Finset.sum_congr rfl fun g _ => hF g]
  refine (sum_count_binomial (InRange lo R) (halfPow (b - lo)) (card_inRange_eq lo hlo R)
      (early h) (fun e : ℕ => (((e + s) - L : ℕ) : ℝ≥0∞))).le.trans ?_
  rw [termTest_eq]
  exact mul_le_mul_of_nonneg_left (lintegral_binomial_mono _
    (fun e e' he => Nat.cast_le.mpr (by omega)) (hcard h)) zero_le
