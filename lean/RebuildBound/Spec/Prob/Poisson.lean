import RebuildBound.Spec.Prob.Tests

/-!
# Laws of count vectors and test bounds (trusted spec)

Definitions behind packages P5 and P6.

* `convList`: the law of `V₁ + ⋯ + Vₙ` for independent `Vᵢ ∼ μᵢ`.
* `unitLaw p`: the law of the unit vector `e_K` when `K = k` with probability
  `p k`; one key's contribution to a vector of arrival counts.
* `poissonVec ν`: independent `Po(ν k)` coordinates.
* `CountBounded K φ`: the finiteness bound `φ x ≤ K + Σ x` that the backward
  tests carry alongside class membership.
* `mainEmbed N`: the node states with main counts `N` and no shadows, i.e. the
  first counted arrivals before their cap.
* `thinAll`: binomial thinning of every node of a list, one after the other.

Nothing here mentions the rebuild model.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- `convList [μ₁, …, μₙ]` is the law of `V₁ + ⋯ + Vₙ` for independent
`Vᵢ ∼ μᵢ`. The empty sum is `0`. -/
noncomputable def convList {κ : Type*} [Countable κ] :
    List (Measure (κ → ℕ)) → Measure (κ → ℕ)
  | [] => Measure.dirac 0
  | μ :: μs => μ ∗ convList μs

/-- The law of the unit vector `e_K` for a random coordinate `K` with
`P(K = k) = p k`. -/
noncomputable def unitLaw {κ : Type*} [Fintype κ] [DecidableEq κ] (p : κ → ℝ≥0) :
    Measure (κ → ℕ) :=
  ∑ k, (p k : ℝ≥0∞) • Measure.dirac (unitVec k)

/-- Independent Poisson coordinates, coordinate `k` with mean `ν k`. -/
noncomputable def poissonVec {κ : Type*} [Fintype κ] (ν : κ → ℝ≥0) : Measure (κ → ℕ) :=
  Measure.pi fun k => poissonMeasure (ν k)

/-- The finiteness bound carried by the backward tests: `φ x ≤ K + Σ_q x q`, the constant `K` standing for the
early count. -/
def CountBounded {ι : Type*} [Fintype ι] (K : ℝ≥0∞) (φ : States ι → ℝ≥0∞) : Prop :=
  ∀ x, φ x ≤ K + ∑ q, (x q : ℝ≥0∞)

/-- The node states with main counts `N` and zero shadow counts. -/
def mainEmbed {ι : Type*} (N : ι → ℕ) : States ι
  | (a, .main) => N a
  | (_, .shadow) => 0

/-- Thin the nodes of the list `l` one after the other, node `b` with survival
probability `p b`. -/
noncomputable def thinAll {ι : Type*} [DecidableEq ι] (l : List ι) (p : ι → I)
    (φ : States ι → ℝ≥0∞) : States ι → ℝ≥0∞ :=
  l.foldr (fun b ψ => thinAt b (p b) ψ) φ

/-- Cap the nodes of the list `l` one after the other, each at capacity `C`. -/
def capAll {ι : Type*} [DecidableEq ι] (l : List ι) (C : ℕ) (x : States ι) : States ι :=
  l.foldr (fun a y => capAt a C y) x

end RebuildBound.Spec
