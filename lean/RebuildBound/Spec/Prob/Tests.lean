import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Group.Convolution

/-!
# Test functions on count vectors (trusted spec)

Definitions behind the shadow comparison of `REPORT.tex` (subsection "A shadow
process counts each shed key once").

* `DirConvex`: directional convexity on `κ → ℕ`, in the subtraction-free
  unit-increment form, so it is meaningful for `ℝ≥0∞`-valued functions.
* `States ι`: a vector of node states. Node `a` has a main count
  `x (a, .main)` and a shadow count `x (a, .shadow)`.
* `ClassT c φ`: the class 𝒯 of backward tests. `c a` is the main-count
  threshold below which condition 3 is required at node `a`; `⊤` requires it
  everywhere.
* The backward operations: `capAt` (cap a node at capacity `C`), `thinAt`
  (binomial thinning of a node), `sumAlong` (add children into parents).
* `convPow`, `compoundPoisson`: laws of `V₁ + ⋯ + V_k` and of
  `V₁ + ⋯ + V_K` with `K ∼ Po(r)`.

Nothing here mentions the rebuild model.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- The unit vector `e_k` of `κ → ℕ`. -/
def unitVec {κ : Type*} [DecidableEq κ] (k : κ) : κ → ℕ :=
  Pi.single k 1

/-- Directional convexity on the lattice `κ → ℕ`: for unit increments `e_k` and
`e_l`, equal or not, `f (x + e_k) + f (x + e_l) ≤ f (x + e_k + e_l) + f x`. -/
def DirConvex {κ : Type*} [DecidableEq κ] (f : (κ → ℕ) → ℝ≥0∞) : Prop :=
  ∀ (x : κ → ℕ) (k l : κ),
    f (x + unitVec k) + f (x + unitVec l) ≤ f (x + unitVec k + unitVec l) + f x

/-- The two counts of a node state. -/
inductive Slot
  | main
  | shadow
  deriving DecidableEq, Repr

-- `deriving Fintype` fails on this Mathlib release, so the instance is by hand.
instance : Fintype Slot :=
  ⟨{.main, .shadow}, fun s => by cases s <;> simp⟩

/-- A vector of node states over the nodes `ι`: `x (a, .main)` is the main count
`M_a` and `x (a, .shadow)` the shadow count `R_a` of node `a`. Counts are
unbounded here; the cap is what keeps a main count at most `C`. -/
abbrev States (ι : Type*) := ι × Slot → ℕ

/-- The class 𝒯 of backward tests, with main-count thresholds `c`:

1. `φ` is nondecreasing in every main and every shadow count;
2. `φ` is directionally convex;
3. at node `a`, a shadow record counts at least as much as a main record,
   wherever `M_a < c a`. -/
structure ClassT {ι : Type*} [DecidableEq ι] (c : ι → ℕ∞) (φ : States ι → ℝ≥0∞) :
    Prop where
  mono : Monotone φ
  dirConvex : DirConvex φ
  main_le_shadow : ∀ (x : States ι) (a : ι), (x (a, .main) : ℕ∞) < c a →
    φ (x + unitVec (a, .main)) ≤ φ (x + unitVec (a, .shadow))

/-- Replace the main and shadow counts of node `a` by `m` and `r`. -/
def setNode {ι : Type*} [DecidableEq ι] (a : ι) (m r : ℕ) (x : States ι) : States ι :=
  Function.update (Function.update x (a, .main) m) (a, .shadow) r

/-- The cap at node `a` with capacity `C`: of the `M_a` main arrivals it keeps
`min M_a C` as main records and sheds the other `(M_a - C)₊` into the shadow
count. The backward test through the cap is `φ ∘ capAt a C`. -/
def capAt {ι : Type*} [DecidableEq ι] (a : ι) (C : ℕ) (x : States ι) : States ι :=
  setNode a (min (x (a, .main)) C) (x (a, .shadow) + (x (a, .main) - C)) x

/-- Binomial thinning of node `a`: each main and each shadow record of node `a`
survives independently with probability `p`. `thinAt a p φ x` is the
expectation of `φ` after thinning. -/
noncomputable def thinAt {ι : Type*} [DecidableEq ι] (a : ι) (p : I)
    (φ : States ι → ℝ≥0∞) (x : States ι) : ℝ≥0∞ :=
  ∫⁻ m, ∫⁻ r, φ (setNode a m r x) ∂(binomial (x (a, .shadow)) p)
    ∂(binomial (x (a, .main)) p)

/-- Adding children into parents: child node `b` feeds parent node `parent b`, main
counts into main counts and shadow counts into shadow counts. The backward
test through the addition is `φ ∘ sumAlong parent`. -/
def sumAlong {κ ι : Type*} [Fintype κ] [DecidableEq ι] (parent : κ → ι) (x : States κ) :
    States ι :=
  fun q => ∑ b ∈ Finset.univ.filter (fun b => parent b = q.1), x (b, q.2)

/-- `convPow μ k` is the law of `V₁ + ⋯ + V_k` for independent `Vᵢ ∼ μ`. -/
noncomputable def convPow {κ : Type*} [Countable κ] (μ : Measure (κ → ℕ)) :
    ℕ → Measure (κ → ℕ)
  | 0 => Measure.dirac 0
  | k + 1 => convPow μ k ∗ μ

/-- The compound Poisson law: the law of `V₁ + ⋯ + V_K` for independent
`Vᵢ ∼ μ` and an independent `K ∼ Po(r)`. -/
noncomputable def compoundPoisson {κ : Type*} [Countable κ] (r : ℝ≥0)
    (μ : Measure (κ → ℕ)) : Measure (κ → ℕ) :=
  Measure.sum fun k => poissonMeasure r {k} • convPow μ k

end RebuildBound.Spec
