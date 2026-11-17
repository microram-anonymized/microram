import RebuildBound.Spec.Prob.Poisson

/-!
# P6: closure of class 𝒯, extended (trusted statements)

X1 (`Spec/Phase0.lean`) proves closure under one cap, one thinning and one
addition. P6 adds:

* **Several nodes.** Thinning a list of nodes, and capping a list of nodes at
  threshold `⊤`. A terminal radix node is `thinAll` over its `r` children,
  `sumAlong` into the node and one cap, so these and X1 cover it.
* **Mixtures** `ψ x = ∫ φ_z x dν(z)` over a mixing law `ν` that does not depend
  on the state `x`, with thresholds shared by all `φ_z`. This covers the
  independent early count `E ∼ Bin(P, p)` and independent external inputs.
* **The finiteness bound** `φ x ≤ K + Σ x` (`CountBounded`): caps and addition
  keep the total count, thinning cannot raise it, and a probability mixture
  averages the constant.
* **The first-arrival interface.** Restricted to main counts `N` and zero
  shadows, a test of `𝒯(⊤)` is nondecreasing and directionally convex in `N`,
  which is the hypothesis of P5a.
* **The terminal test** after averaging the early count: the stop-loss
  `E (E + Σ_v R_v - L)₊` with `E ∼ Bin(P, p)` is in `𝒯(⊤)` and bounded by
  `P + Σ x`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- **P6, thinning several nodes** preserves `𝒯(c)`. -/
def P6_thinAll_statement : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (c : ι → ℕ∞) (φ : States ι → ℝ≥0∞) (l : List ι) (p : ι → I),
    ClassT c φ → ClassT c (thinAll l p φ)

/-- **P6, capping several nodes** preserves `𝒯(⊤)`. -/
def P6_capAll_statement : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (φ : States ι → ℝ≥0∞) (l : List ι) (C : ℕ),
    ClassT ⊤ φ → ClassT ⊤ (φ ∘ capAll l C)

/-- **P6, mixtures.** A mixture of tests of `𝒯(c)` under a law that does not
depend on the state is in `𝒯(c)`. -/
def P6_mix_statement : Prop :=
  ∀ {ι Z : Type} [DecidableEq ι] [MeasurableSpace Z] (c : ι → ℕ∞)
    (φ : Z → States ι → ℝ≥0∞) (ν : Measure Z),
    (∀ z, ClassT c (φ z)) → (∀ x, Measurable fun z => φ z x) →
    ClassT c (fun x => ∫⁻ z, φ z x ∂ν)

/-- **P6, the finiteness bound** is preserved by a cap, a thinning, an addition
and a probability mixture (whose constant is averaged). -/
def P6_bound_statement : Prop :=
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (K : ℝ≥0∞) (φ : States ι → ℝ≥0∞) (a : ι) (C : ℕ),
    CountBounded K φ → CountBounded K (φ ∘ capAt a C)) ∧
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (K : ℝ≥0∞) (φ : States ι → ℝ≥0∞) (a : ι) (p : I),
    CountBounded K φ → CountBounded K (thinAt a p φ)) ∧
  (∀ {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] (K : ℝ≥0∞)
    (parent : κ → ι) (φ : States ι → ℝ≥0∞),
    CountBounded K φ → CountBounded K (φ ∘ sumAlong parent)) ∧
  (∀ {ι Z : Type} [Fintype ι] [MeasurableSpace Z] (K : Z → ℝ≥0∞) (φ : Z → States ι → ℝ≥0∞)
    (ν : Measure Z), IsProbabilityMeasure ν → Measurable K →
    (∀ z, CountBounded (K z) (φ z)) → (∀ x, Measurable fun z => φ z x) →
    CountBounded (∫⁻ z, K z ∂ν) (fun x => ∫⁻ z, φ z x ∂ν))

/-- **P6, the first-arrival interface.** A test of `𝒯(⊤)` restricted to main
counts `N` and zero shadows is nondecreasing and directionally convex in `N`,
and keeps its finiteness bound. -/
def P6_embed_statement : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (φ : States ι → ℝ≥0∞) (K : ℝ≥0∞),
    ClassT ⊤ φ → CountBounded K φ →
    Monotone (φ ∘ mainEmbed) ∧ DirConvex (φ ∘ mainEmbed) ∧
      ∀ N : ι → ℕ, φ (mainEmbed N) ≤ K + ∑ a, (N a : ℝ≥0∞)

/-- The terminal test after averaging an independent early count
`E ∼ Bin(P, p)`: the expected stop-loss `E (E + Σ_v R_v - L)₊`. -/
noncomputable def earlyStopLoss {ι : Type*} [Fintype ι] (P : ℕ) (p : I) (L : ℕ)
    (x : States ι) : ℝ≥0∞ :=
  ∫⁻ e, (((e + ∑ a, x (a, .shadow)) - L : ℕ) : ℝ≥0∞) ∂(binomial P p)

/-- **P6, the terminal test.** The averaged stop-loss is in `𝒯(⊤)` and bounded
by `P + Σ x`. -/
def P6_terminal_statement : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ℕ) (p : I) (L : ℕ),
    ClassT ⊤ (earlyStopLoss (ι := ι) P p L) ∧ CountBounded P (earlyStopLoss (ι := ι) P p L)

end RebuildBound.Spec
