import RebuildBound.Spec.Prob.Poisson
import RebuildBound.Spec.Prob.Series

/-!
# P7 and P8a: the positive series and one complete population (trusted)

Two probability facts used by the top-finish bound.

* **P7, the positive series** (`eq:general-series`). For independent
  `Z_v ∼ Po(λ)` on the homes of a set `J`,
  `E (Σ_{v ∈ J} (Z_v - C)₊ - S)₊ ≤ Φ_K(|J|, C, λ, S)` for every cutoff `K > S`.
  No condition on `λ` or `C` is needed: `W(2) ≤ 2^-C e^λ` holds for every
  `λ ≥ 0`.
* **P8a, one complete population** (`prop:general-tiers` for one
  population, and `lem:restricted-excess`). A fixed list of keys has
  independent categorical homes on `ι`, key `i` at home `v` with probability
  `pᵢ v ≤ p_*`. The home-count vector is `Y = Σᵢ e_{hᵢ}`, whose law is
  `convList (ps.map unitLaw)`. If `|keys| · p_* ≤ λ`, then the stop-loss of
  the excess restricted to a home set `J` is at most the same stop-loss
  under independent `Po(λ)` counts. The masses need not be uniform, so
  G1′ can reuse it at `p_* = 1/((d-1)U)`.

Integer events follow: `P(R_J > s) ≤ E (R_J - s)₊` because `R_J` is an
integer, so `P(R_J > s) ≤ Φ_K(|J|, C, λ, s)` (the form G3 uses).

P7 is split in two packages:
* **P7alg**, pure algebra: the `n`-fold Cauchy power of the pmf of `(Z - C)₊`
  is coefficientwise at most `c_k` (`(q₀ + W)^n ≼ (1 + W)^n ≼ exp(n W)`);
* **P7**, from P7alg: the law of the restricted excess under `poissonVec` is
  that Cauchy power, so its stop-loss is the finite sum up to `K` plus a tail
  bounded through `E 2^X ≤ (1 + 2^-C e^λ)^|J| ≤ exp(|J| 2^-C e^λ)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec

/-- The stop-loss test `(Σ_{v ∈ J} (y_v - C)₊ - S)₊` of the excess restricted
to the home set `J`. -/
def restrictedStopLoss {ι : Type*} (J : Finset ι) (C S : ℕ) (y : ι → ℕ) : ℝ≥0∞ :=
  ((∑ v ∈ J, (y v - C) - S : ℕ) : ℝ≥0∞)

/-- **P7, the positive series.** Under independent `Po(λ)` counts, the
stop-loss of the excess restricted to `J` is at most `Φ_K(|J|, C, λ, S)` for
every cutoff `K > S`. -/
def P7_statement : Prop :=
  ∀ {ι : Type} [Fintype ι] (J : Finset ι) (C S K : ℕ) (lam : ℝ≥0), S < K →
    ∫⁻ z, restrictedStopLoss J C S z ∂(poissonVec (fun _ : ι => lam)) ≤
      ENNReal.ofReal (Phi K J.card C lam S)

/-- The pmf of `(Z - C)₊` for `Z ∼ Po(λ)`: `q₀ = P(Z ≤ C)` and `q_j = w_j`. -/
noncomputable def excessPmf (C : ℕ) (lam : ℝ) : ℕ → ℝ
  | 0 => ∑ z ∈ Finset.range (C + 1), Real.exp (-lam) * lam ^ z / (z.factorial : ℝ)
  | j + 1 => seriesW C lam (j + 1)

/-- The `n`-fold Cauchy (convolution) power of a sequence: the coefficients of
`(Σ_j q_j z^j)^n`. -/
noncomputable def cauchyPow (q : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => ∑ ij ∈ Finset.antidiagonal k, cauchyPow q n ij.1 * q ij.2

/-- **P7alg, the majorization** `(q₀ + W)^n ≼ (1 + W)^n ≼ exp(n W)`: every
coefficient of the `n`-fold power of the excess pmf is at most `c_k`. -/
def P7alg_statement : Prop :=
  ∀ (n C k : ℕ) (lam : ℝ), 0 ≤ lam → cauchyPow (excessPmf C lam) n k ≤ seriesCoeff n C lam k

/-- **P8a, one complete population.** Independent categorical homes with
masses at most `p_*` and `|keys| · p_* ≤ λ`: the restricted stop-loss is at
most its value under independent `Po(λ)` counts. -/
def P8a_statement : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (J : Finset ι) (C S : ℕ) (pstar lam : ℝ≥0)
    (ps : List (ι → ℝ≥0)),
    (∀ p ∈ ps, ∑ v, p v = 1) → (∀ p ∈ ps, ∀ v, p v ≤ pstar) →
    (ps.length : ℝ≥0) * pstar ≤ lam →
    ∫⁻ y, restrictedStopLoss J C S y ∂(convList (ps.map unitLaw)) ≤
      ∫⁻ z, restrictedStopLoss J C S z ∂(poissonVec (fun _ : ι => lam))

end RebuildBound.Spec
