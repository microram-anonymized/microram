import RebuildBound.Proofs.P12e.Stage

/-!
# P12e: the forest identity in `r` blocks with a terminal radix

`∫ rFirstArrivalTest N ∂(Po(λ)^⊗) = stopLoss (rangeLawR C λ P 2^lo (b-lo) r q) L`.

Proof outline. As in P11e (`Proofs/P11e.lean`), node states are read as vectors of
node pairs `y v = (main, shadow)` (`toS`), and every law along the way is a product
law `Measure.pi ν` of node pairs over `RNode r b = Fin r × Bits b`.

1. **Start.** The capped first arrivals have the product law
   `Measure.pi (fun _ => shadowTree C λ 1)`.
2. **One stage** (`lintegral_rBackStage`, `P12e/Stage.lean`). The block index is
   inert: in every block the stage acts as P11e's binary stage.
3. **The stage laws** `lawAtR j (i, W) = lawAt j W`, P11e's stage law in every block,
   so P11e's `stepLaw_lawAt` gives the recursion.
4. **The radix terminal test** (`lintegral_radixTermTest`). Thinning every node by `q`
   replaces each node law by its bind with `thinPair q`. Adding the `r` blocks at
   each bucket maps the product law to the product of the `r`-fold pair convolutions
   (`map_blockSum`, `P12e/Block.lean`), the cap maps it to a product law again, and
   P11e's `lintegral_termTest` gives the stop-loss, where the cap's shadow count
   `s ↦ s.2 + (s.1 - C)` turns `pairConvPow` into `radixRoot`.

Probability API: measure-based throughout (`Measure.pi`, `Measure.bind`,
`Measure.conv`, `binomial`, `poissonMeasure`, `lintegral`). Obstacle recorded: as in
P11e, Mathlib has no grouping or currying lemma for `Measure.pi` in this discrete
setting that composes directly with `Measure.map`, so `map_curry` is proved on
singletons (`Measure.ext_of_singleton`), and `map_sum_pi` through
`Measure.ext_of_lintegral` from the `lintegral` form `lintegral_sum_pair`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

set_option linter.unusedSectionVars false

namespace RebuildBound.P12eProof

open RebuildBound.Spec RebuildBound.P11eProof

variable {r b : ℕ}

/-! ### The backward recursion of `rForestTest` -/

lemma rForestTest_self (C : ℕ) (R : Bits b) (φ : States (RNode r b) → ℝ≥0∞) :
    rForestTest C R φ b = φ := by
  simp [rForestTest]

lemma rForestTest_succ (C : ℕ) (R : Bits b) (φ : States (RNode r b) → ℝ≥0∞) (j : ℕ)
    (hj : j < b) :
    rForestTest C R φ j = rBackStage C R j (rForestTest C R φ (j + 1)) := by
  unfold rForestTest
  obtain ⟨n, hn⟩ : ∃ n, b - j = n + 1 := ⟨b - j - 1, by omega⟩
  have hn' : b - (j + 1) = n := by omega
  rw [hn, hn', List.range_succ_eq_map, List.foldr_cons, List.foldr_map, Nat.add_zero]
  congr 1
  congr 1
  funext i ψ
  rw [show j + (i + 1) = j + 1 + i by omega]

/-! ### The stage laws -/

/-- The law of the node pairs after stage `j`: P11e's stage law in every block. -/
noncomputable def lawAtR (C : ℕ) (lam : ℝ≥0) (lo : ℕ) (R : Bits b) (j : ℕ) (v : RNode r b) :
    Measure (ℕ × ℕ) :=
  lawAt C lam lo R j v.2

lemma isProb_lawAtR (C : ℕ) (lam : ℝ≥0) (lo : ℕ) (R : Bits b) (j : ℕ) (v : RNode r b) :
    IsProbabilityMeasure (lawAtR C lam lo R j v) :=
  isProb_lawAt C lam lo R j v.2

lemma stepLawR_lawAtR (C : ℕ) (lam : ℝ≥0) (lo : ℕ) (R : Bits b) (j : ℕ) (hj : j < b)
    (hlo : lo < j) :
    stepLawR C ⟨j, hj⟩ (R ⟨j, hj⟩) (lawAtR (r := r) C lam lo R j) =
      lawAtR (r := r) C lam lo R (j + 1) := by
  funext v
  exact congrFun (stepLaw_lawAt C lam lo R j hj hlo) v.2

/-- The backward forest test from stage `j` integrates against the stage law of `j` to
the terminal test against the stage law of `b`. -/
lemma lintegral_rForestTest (C : ℕ) (lam : ℝ≥0) (lo : ℕ) (R : Bits b)
    (φ : States (RNode r b) → ℝ≥0∞) :
    ∀ n j, j + n = b → lo < j →
      ∫⁻ y, rForestTest C R φ j (toS y) ∂(Measure.pi (lawAtR C lam lo R j)) =
        ∫⁻ y, φ (toS y) ∂(Measure.pi (lawAtR C lam lo R b))
  | 0, j, h, _ => by
    obtain rfl : j = b := by omega
    rw [rForestTest_self]
  | n + 1, j, h, hlo => by
    have hj : j < b := by omega
    rw [rForestTest_succ C R φ j hj,
      lintegral_rBackStage C R j hj _ (isProb_lawAtR C lam lo R j) _,
      stepLawR_lawAtR C lam lo R j hj hlo]
    exact lintegral_rForestTest C lam lo R φ n (j + 1) (by omega) (by omega)

/-! ### The radix terminal test -/

lemma sumAlong_snd_toS (y : RNode r b → ℕ × ℕ) :
    sumAlong (fun V : RNode r b => V.2) (toS y) = toS (fun W => ∑ i, y (i, W)) := by
  rw [sumAlong_toS]
  congr 1
  funext W
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp

lemma capAll_allNodes_toS (C : ℕ) (z : Bits b → ℕ × ℕ) :
    capAll (allNodes b) C (toS z) = toS (fun W => capPair C (z W)) := by
  rw [capAll_toS]
  congr 1
  funext W
  simp [allNodes]

/-- The radix terminal test against a product law whose node laws depend only on the
in-block bucket and are `μ` on the range. -/
lemma lintegral_radixTermTest (C P : ℕ) (pe q : I) (L lo : ℕ) (R : Bits b) (hlo : lo ≤ b)
    (κ : Bits b → Measure (ℕ × ℕ)) (hκ : ∀ W, IsProbabilityMeasure (κ W))
    (μ : Measure (ℕ × ℕ)) [IsProbabilityMeasure μ] (hS : ∀ W ∈ rangeHomes lo R, κ W = μ) :
    ∫⁻ y, radixTermTest C P pe q L lo R (toS y) ∂(Measure.pi (fun v : RNode r b => κ v.2)) =
      stopLoss (binomial P pe ∗ natConvPow
        ((pairConvPow (μ.bind (thinPair q)) r).map fun s => s.2 + (s.1 - C)) (2 ^ lo)) L := by
  have hth : ∀ W, IsProbabilityMeasure ((κ W).bind (thinPair q)) := fun _ => inferInstance
  unfold radixTermTest
  rw [lintegral_thinAll q _ (allRNodes r b) (Finset.nodup_toList _) _ (fun _ => inferInstance)]
  simp only [mem_allRNodes, ite_true, Function.comp_apply, sumAlong_snd_toS,
    capAll_allNodes_toS]
  rw [← lintegral_map (f := fun w => termTest P pe L lo R (toS w)) Measurable.of_discrete
    Measurable.of_discrete]
  have hmap : (Measure.pi (fun v : RNode r b => (κ v.2).bind (thinPair q))).map
      (fun y W => capPair C (∑ i, y (i, W))) =
      Measure.pi (fun W => (pairConvPow ((κ W).bind (thinPair q)) r).map (capPair C)) := by
    have he : (fun (y : RNode r b → ℕ × ℕ) W => capPair C (∑ i, y (i, W))) =
        (fun z W => capPair C (z W)) ∘ (fun y W => ∑ i, y (i, W)) := rfl
    rw [he, ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
      map_blockSum r (fun W => (κ W).bind (thinPair q)),
      Measure.pi_map_pi (f := fun _ (s : ℕ × ℕ) => capPair C s)
        (fun _ => Measurable.of_discrete.aemeasurable)]
  rw [hmap]
  have hS' : ∀ W ∈ rangeHomes lo R, (pairConvPow ((κ W).bind (thinPair q)) r).map (capPair C) =
      (pairConvPow (μ.bind (thinPair q)) r).map (capPair C) := by
    intro W hW
    rw [hS W hW]
  rw [lintegral_termTest P pe L lo R _ (fun _ => inferInstance) _ hS', card_rangeHomes lo R hlo,
    Measure.map_map measurable_snd Measurable.of_discrete]
  rfl

end RebuildBound.P12eProof

open RebuildBound.Spec RebuildBound.P11eProof RebuildBound.P12eProof in
theorem RebuildBound.P12e : RebuildBound.Spec.P12e_statement := by
  intro r b C P L lo R q lam hlo _hr
  unfold rFirstArrivalTest
  have h0 : ∀ N : RNode r b → ℕ,
      capAll (allRNodes r b) C (mainEmbed N) = toS (fun v => capPair C (N v, 0)) :=
    fun N => capAll_mainEmbed C _ (by intro v; simp [allRNodes]) N
  simp_rw [h0]
  rw [← lintegral_map (f := fun y => rForestTest C R
    (radixTermTest C P (q * halfPow (b - lo)) q L lo R) (lo + 1) (toS y))
    Measurable.of_discrete Measurable.of_discrete]
  have h1 : (poissonVec (fun _ : RNode r b => lam)).map (fun N v => capPair C (N v, 0)) =
      Measure.pi (lawAtR C lam lo R (lo + 1)) := by
    rw [poissonVec_map_capPair]
    congr 1
    funext v
    exact (congrFun (lawAt_initial C lam lo R) v.2).symm
  have hS : ∀ v ∈ rangeHomes lo R, lawAt C lam lo R b v = shadowTree C lam (b - lo) := by
    intro v hv
    unfold lawAt
    rw [ite_eq_left]
    intro i h1 _
    exact (Finset.mem_filter.1 hv).2 i h1.le
  have := isProb_shadowTree C lam (b - lo)
  rw [h1, lintegral_rForestTest C lam lo R _ (b - (lo + 1)) (lo + 1) (by omega) (by omega)]
  exact lintegral_radixTermTest C P _ q L lo R hlo.le (lawAt C lam lo R b)
    (isProb_lawAt C lam lo R b) _ hS
