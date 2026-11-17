import RebuildBound.Spec.Prob.Tests

/-!
# First closure and replacement lemmas of the shadow comparison (trusted statements)

Two foundational statements that the later packages extend:

* **X1**, closure of class 𝒯 under the backward operations of the shadow
  comparison: the cap (including the case `U = C - 1`), binomial thinning and
  addition of children; and membership of the terminal stop-loss test.
  Package P6 extends it (the radix node, mixtures).
* **X2**, one-key Pois(1) replacement:
  `E f(x + V) ≤ E f(x + V₁ + ⋯ + V_K)` for directionally convex `f` and
  `K ∼ Po(1)` independent of the i.i.d. `Vᵢ`. Package P5a extends it.

In the backward pass through one tree stage, a parent test `φ ∈ 𝒯` becomes
`φ ∘ capAt a C` at each parent `a` (X1_cap), then `· ∘ sumAlong parent` (X1_add),
then `thinAt b p ·` at each child `b` (X1_thin). A cap turns the threshold of
its node into `⊤`, and addition needs `⊤` everywhere, which is why the
thresholds are explicit.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- **X1, cap.** If `φ ∈ 𝒯(c)` and the capacity `C` is at most node `a`'s
threshold, then the test through the cap at `a` is in `𝒯` with threshold `⊤`
at `a`. -/
def X1_cap_statement : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (c : ι → ℕ∞) (φ : States ι → ℝ≥0∞) (a : ι) (C : ℕ),
    ClassT c φ → (C : ℕ∞) ≤ c a → ClassT (Function.update c a ⊤) (φ ∘ capAt a C)

/-- **X1, thinning.** Binomial thinning of one node preserves `𝒯(c)`. -/
def X1_thin_statement : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (c : ι → ℕ∞) (φ : States ι → ℝ≥0∞) (a : ι) (p : I),
    ClassT c φ → ClassT c (thinAt a p φ)

/-- **X1, addition.** Adding children into parents preserves `𝒯(⊤)`. -/
def X1_add_statement : Prop :=
  ∀ {κ ι : Type} [Fintype κ] [DecidableEq κ] [DecidableEq ι] (parent : κ → ι)
    (φ : States ι → ℝ≥0∞),
    ClassT ⊤ φ → ClassT ⊤ (φ ∘ sumAlong parent)

/-- **X1, terminal test.** A convex nondecreasing function of the total shadow
count, such as the stop-loss `(E + Σ_v R_v - L)₊` for a fixed early count `E`,
is in `𝒯(⊤)`. This is also the non-vacuity witness for `ClassT`. -/
def X1_terminal_statement : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (g : ℕ → ℝ≥0∞),
    Monotone g → (∀ n, g (n + 1) + g (n + 1) ≤ g (n + 2) + g n) →
    ClassT ⊤ (fun x : States ι => g (∑ a, x (a, .shadow)))

/-- **X2, one-key Pois(1) replacement.** For a finite-valued directionally
convex `f` on `κ → ℕ`, a probability law `μ` of the increment `V` and a base
point `x`: `E f(x + V) ≤ E f(x + V₁ + ⋯ + V_K)` with `K ∼ Po(1)`. -/
def X2_statement : Prop :=
  ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (f : (κ → ℕ) → ℝ≥0∞),
    DirConvex f → (∀ y, f y ≠ ∞) →
    ∀ (μ : Measure (κ → ℕ)) [IsProbabilityMeasure μ] (x : κ → ℕ),
      ∫⁻ v, f (x + v) ∂μ ≤ ∫⁻ v, f (x + v) ∂(compoundPoisson 1 μ)

end RebuildBound.Spec
