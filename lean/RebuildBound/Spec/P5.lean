import RebuildBound.Spec.Prob.Poisson

/-!
# P5: per-key Poisson replacement, splitting and padding (trusted statements)

The completed-A proof uses them in this order at the first
counted arrivals, whose backward test `f` is nondecreasing, directionally
convex and finite (package P6):

1. **P5a.** Replace every key's increment `Vᵢ` by an independent compound
   Poisson sum `Vᵢ₁ + ⋯ + Vᵢ_K`, `K ∼ Po(1)`, one key at a time. Each step
   applies X2 to `f` itself at a base point that holds the other keys'
   contributions, so no averaged test needs to be finite.
2. **P5b, splitting.** A key whose increment is a unit vector `e_K` with
   `P(K = k) = p k` becomes independent `Po(p k)` coordinates.
3. **P5b, sums.** Independent Poisson vectors add their means.
4. **P5b, padding.** Raising the means only increases a nondecreasing test.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec

/-- **P5a, key-by-key Pois(1) replacement.** For a finite-valued directionally
convex `f` and independent increments `Vᵢ ∼ μᵢ`:
`E f(x + V₁ + ⋯ + Vₙ) ≤ E f(x + W₁ + ⋯ + Wₙ)`, with independent `Wᵢ` of the
compound Poisson laws `compoundPoisson 1 μᵢ`. -/
def P5a_statement : Prop :=
  ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (f : (κ → ℕ) → ℝ≥0∞),
    DirConvex f → (∀ y, f y ≠ ∞) →
    ∀ (μs : List (Measure (κ → ℕ))), (∀ μ ∈ μs, IsProbabilityMeasure μ) →
    ∀ (x : κ → ℕ),
      ∫⁻ v, f (x + v) ∂(convList μs) ≤
        ∫⁻ v, f (x + v) ∂(convList (μs.map (compoundPoisson 1)))

/-- **P5b, Poisson splitting.** A `Po(r)` number of independent unit vectors,
each `e_k` with probability `p k`, has independent `Po(r * p k)` coordinates. -/
def P5b_split_statement : Prop :=
  ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (r : ℝ≥0) (p : κ → ℝ≥0),
    ∑ k, p k = 1 → compoundPoisson r (unitLaw p) = poissonVec (fun k => r * p k)

/-- **P5b, sums of Poisson vectors.** Independent Poisson vectors add their
means coordinatewise. -/
def P5b_conv_statement : Prop :=
  ∀ {κ : Type} [Fintype κ] (ν ν' : κ → ℝ≥0),
    poissonVec ν ∗ poissonVec ν' = poissonVec (ν + ν')

/-- **P5b, padding of means.** For a nondecreasing test, raising every Poisson
mean can only increase its expectation. -/
def P5b_pad_statement : Prop :=
  ∀ {κ : Type} [Fintype κ] (f : (κ → ℕ) → ℝ≥0∞), Monotone f →
    ∀ (ν ν' : κ → ℝ≥0), ν ≤ ν' →
      ∫⁻ y, f y ∂(poissonVec ν) ≤ ∫⁻ y, f y ∂(poissonVec ν')

end RebuildBound.Spec
