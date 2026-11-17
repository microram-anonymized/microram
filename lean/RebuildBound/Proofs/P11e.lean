import RebuildBound.Proofs.P11e.Stage
import RebuildBound.Proofs.ShadowLaw.Tree

/-!
# P11e: the forest identity

`∫ firstArrivalTest N ∂(Po(λ)^⊗) = stopLoss (rangeLaw C λ P 2^-(b-lo) 2^lo (b-lo)) L`.

Proof outline. Node states are read as vectors of node pairs `y v = (main, shadow)`
(`toS`), and every law along the way is a product law `Measure.pi ν` of node pairs.

1. **Start.** The capped first arrivals are `toS (fun v => capPair C (N v, 0))`, so
   the start law is `Measure.pi (fun _ => shadowTree C λ 1)` (`Measure.pi_map_pi`).
2. **One stage** (`lintegral_backStage`, `P11e/Stage.lean`). Against a product law,
   thinning every node replaces each node law by its bind with `thinPair half`
   (one coordinate at a time, `lintegral_pi_update`); the addition along bit `j`
   and the cap act on pairs by `stageMap`, whose image law is again a product
   (`map_pairMap`, grouping each node with bit `j` of `R` with its sibling).
3. **The stage laws** `lawAt j`: `shadowTree C λ (j - lo)` at the nodes that agree
   with `R` on bits `lo + 1, …, j - 1`, and `δ (0, 0)` elsewhere. One stage maps
   `lawAt j` to `lawAt (j + 1)`: two independent thinned depth-`(j - lo)` trees are
   added and capped, which is the `shadowTree` recursion.
4. **Terminal test.** The homes of the range carry independent
   `shadowTree C λ (b - lo)` states, so the sum of their shadows has law
   `natConvPow` (`lintegral_sum_snd`, by resampling one coordinate at a time), and
   the independent early count gives the convolution with `Bin(P, 2^-(b-lo))`.

Probability API: measure-based throughout (`Measure.pi`, `Measure.bind`,
`Measure.conv`, `binomial`, `poissonMeasure`, `lintegral`). Obstacle recorded: Mathlib
has no `lintegral` analogue of `integral_fintype_prod_eq_prod` and no grouping
lemma for `Measure.pi` over the blocks of a partition, so the product-law facts are
proved on singletons (`Measure.ext_of_singleton`, `Measure.pi_singleton`), which the
discrete state space allows.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

set_option linter.unusedSectionVars false

namespace RebuildBound.P11eProof

open RebuildBound.Spec

variable {b : ℕ}

/-! ### The backward recursion of `forestTest` -/

lemma forestTest_self (C : ℕ) (R : Bits b) (φ : States (Bits b) → ℝ≥0∞) :
    forestTest C R φ b = φ := by
  simp [forestTest]

lemma forestTest_succ (C : ℕ) (R : Bits b) (φ : States (Bits b) → ℝ≥0∞) (j : ℕ) (hj : j < b) :
    forestTest C R φ j = backStage C R j (forestTest C R φ (j + 1)) := by
  unfold forestTest
  obtain ⟨n, hn⟩ : ∃ n, b - j = n + 1 := ⟨b - j - 1, by omega⟩
  have hn' : b - (j + 1) = n := by omega
  rw [hn, hn', List.range_succ_eq_map, List.foldr_cons, List.foldr_map, Nat.add_zero]
  congr 1
  congr 1
  funext i ψ
  rw [show j + (i + 1) = j + 1 + i by omega]

/-! ### The stage laws -/

/-- The backward forest test from stage `j` integrates against the stage law of `j` to
the terminal test against the stage law of `b`. -/
lemma lintegral_forestTest (C : ℕ) (lam : ℝ≥0) (lo : ℕ) (R : Bits b)
    (φ : States (Bits b) → ℝ≥0∞) :
    ∀ n j, j + n = b → lo < j →
      ∫⁻ y, forestTest C R φ j (toS y) ∂(Measure.pi (lawAt C lam lo R j)) =
        ∫⁻ y, φ (toS y) ∂(Measure.pi (lawAt C lam lo R b))
  | 0, j, h, _ => by
    obtain rfl : j = b := by omega
    rw [forestTest_self]
  | n + 1, j, h, hlo => by
    have hj : j < b := by omega
    rw [forestTest_succ C R φ j hj,
      lintegral_backStage C R j hj _ (isProb_lawAt C lam lo R j) _,
      stepLaw_lawAt C lam lo R j hj hlo]
    exact lintegral_forestTest C lam lo R φ n (j + 1) (by omega) (by omega)

/-! ### The terminal test -/

end RebuildBound.P11eProof

open RebuildBound.Spec RebuildBound.P11eProof in
theorem RebuildBound.P11e : RebuildBound.Spec.P11e_statement := by
  intro b C P L lo R lam hlo
  unfold firstArrivalTest
  have h0 : ∀ N : Bits b → ℕ,
      capAll (allNodes b) C (mainEmbed N) = toS (fun v => capPair C (N v, 0)) :=
    fun N => capAll_mainEmbed C _ (by intro v; simp [allNodes]) N
  simp_rw [h0]
  rw [← lintegral_map (f := fun y => forestTest C R (termTest P (halfPow (b - lo)) L lo R) (lo + 1)
    (toS y)) Measurable.of_discrete Measurable.of_discrete]
  have h1 : (poissonVec (fun _ : Bits b => lam)).map (fun N v => capPair C (N v, 0)) =
      Measure.pi (lawAt C lam lo R (lo + 1)) := by
    rw [lawAt_initial]
    exact poissonVec_map_capPair C lam
  have hS : ∀ v ∈ rangeHomes lo R, lawAt C lam lo R b v = shadowTree C lam (b - lo) := by
    intro v hv
    unfold lawAt
    rw [ite_eq_left]
    intro i h1 _
    exact (Finset.mem_filter.1 hv).2 i h1.le
  have := isProb_shadowTree C lam (b - lo)
  rw [h1, lintegral_forestTest C lam lo R _ (b - (lo + 1)) (lo + 1) (by omega) (by omega),
    lintegral_termTest P _ L lo R _ (isProb_lawAt C lam lo R b) _ hS, card_rangeHomes lo R hlo.le]
  rfl
