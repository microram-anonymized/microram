import RebuildBound.Spec.P8bRate
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-! # A finite correlated Poisson star

Each edge has one shared Poisson primitive, counted whole in both its center
and leaf. All primitive draws are independent. Feasibility is explicit so
truncated NNReal subtraction cannot hide a negative private rate. This package
lifts the pair comparison, supplies the stop-loss test, and checks the interval
rates at four abstract parameter choices taken from an earlier dense
shared-stash analysis. These reusable lemmas do not identify the current
engine's raw-count law with this star or certify a numerical series.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace RebuildBound.Spec

/-- Independent finite Poisson draws, using the measure-based API. -/
noncomputable def finPoissonIntegral :
    (n : ℕ) → (Fin n → ℝ≥0) → ((Fin n → ℕ) → ℝ≥0∞) → ℝ≥0∞
  | 0, _, f => f (fun i => Fin.elim0 i)
  | n + 1, nu, f =>
      ∫⁻ k, finPoissonIntegral n (fun i => nu i.succ)
        (fun x => f (Fin.cons k x)) ∂poissonMeasure (nu 0)

def starCounts {n : ℕ} (a : ℕ) (b y : Fin n → ℕ) : Option (Fin n) → ℕ
  | none => a + ∑ i, y i
  | some i => b i + y i

noncomputable def poissonStarExpectation (n : ℕ) (mu : ℝ≥0)
    (lambda gamma : Fin n → ℝ≥0)
    (f : (Option (Fin n) → ℕ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ a, finPoissonIntegral n (fun i => lambda i - gamma i) (fun b =>
    finPoissonIntegral n gamma (fun y => f (starCounts a b y)))
    ∂poissonMeasure (mu - ∑ i, gamma i)

def StarIncreasingDifferences {n : ℕ}
    (f : (Option (Fin n) → ℕ) → ℝ≥0∞) : Prop :=
  ∀ (x : Option (Fin n) → ℕ) (i : Fin n),
    SharedIncreasingDifferences (fun a b =>
      f (Function.update (Function.update x none a) (some i) b))

def P8bStar_statement : Prop :=
  ∀ (n : ℕ) (mu : ℝ≥0) (lambda gamma gamma' : Fin n → ℝ≥0)
    (f : (Option (Fin n) → ℕ) → ℝ≥0∞),
    gamma ≤ gamma' → (∑ i, gamma' i) ≤ mu → gamma' ≤ lambda →
    StarIncreasingDifferences f →
    poissonStarExpectation n mu lambda gamma f ≤
      poissonStarExpectation n mu lambda gamma' f

/-- Stop loss of the sum of per-bin capacity excesses. -/
def starStopLoss (n C S : ℕ) (x : Option (Fin n) → ℕ) : ℝ≥0∞ :=
  (((∑ v, (x v - C)) - S : ℕ) : ℝ≥0∞)

def P8bStarStopLoss_statement : Prop :=
  ∀ (n C S : ℕ), StarIncreasingDifferences (starStopLoss n C S)

def DenseStarShape (d t : ℕ) : Prop :=
  (d = 4 ∧ t = 2) ∨ (d = 6 ∧ t = 2) ∨
  (d = 8 ∧ t = 2) ∨ (d = 8 ∧ t = 4)

noncomputable def denseStarCenter (L : ℝ≥0) (d t : ℕ) (theta : ℝ≥0) : ℝ≥0 :=
  L * (1 - theta * ((t - 1 : ℕ) : ℝ≥0) /
    (((d - 1 : ℕ) : ℝ≥0) * (t : ℝ≥0)))

noncomputable def denseStarShared (L : ℝ≥0) (d : ℕ) (theta : ℝ≥0) : ℝ≥0 :=
  L * theta / ((d - 1 : ℕ) : ℝ≥0)

/-- Independent low/high endpoint rounding keeps the padded private rates
nonnegative at any marginal scale L (including the numerical certifier's
slightly padded scale), including the final overlap interval's endpoint theta=1. -/
def P8bStarRates_statement : Prop :=
  ∀ (L : ℝ≥0) (d t j : ℕ) (theta : ℝ≥0),
    DenseStarShape d t → j < 32 →
    (j : ℝ≥0) / 32 ≤ theta → theta ≤ ((j + 1 : ℕ) : ℝ≥0) / 32 →
    theta ≤ 1 ∧
    theta * ((t - 1 : ℕ) : ℝ≥0) /
      (((d - 1 : ℕ) : ℝ≥0) * (t : ℝ≥0)) ≤ 1 ∧
    denseStarCenter L d t theta ≤ denseStarCenter L d t ((j : ℝ≥0) / 32) ∧
    denseStarShared L d theta ≤ denseStarShared L d (((j + 1 : ℕ) : ℝ≥0) / 32) ∧
    ((d / t - 1 : ℕ) : ℝ≥0) *
      denseStarShared L d (((j + 1 : ℕ) : ℝ≥0) / 32) ≤
      denseStarCenter L d t ((j : ℝ≥0) / 32) ∧
    denseStarShared L d (((j + 1 : ℕ) : ℝ≥0) / 32) ≤ L

end RebuildBound.Spec
