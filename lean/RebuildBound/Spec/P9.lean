import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Mixed allocation (P9, trusted statements)

A public allocation splits one capacity among finitely many capped sources.
Only marginal tail bounds are used: sources and ranges may be arbitrarily
correlated. Events and counts are on the original probability space, never a
law conditioned on successful execution. The final infimum is over public
allocations, not an allocation selected from the observed counts.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec

def cappedTail (c : ℕ) (b : ℕ → ℝ≥0∞) (s : ℕ) : ℝ≥0∞ :=
  if c ≤ s then 0 else min 1 (b s)

noncomputable def mixedAllocationBound {ι : Type} [Fintype ι] (S : ℕ)
    (c : ι → ℕ) (b : ι → ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  min 1 (⨅ a : {a : ι → ℕ // ∑ i, a i = S}, ∑ i, cappedTail (c i) (b i) (a.val i))

def P9_alloc_statement : Prop :=
  ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ι → Ω → ℕ) (c : ι → ℕ) (S : ℕ)
    (b : ι → ℕ → ℝ≥0∞) (F : Set Ω),
    (∀ i s, s ≤ S → μ {ω | s < T i ω} ≤ b i s) →
    (∀ ω ∈ F, S < ∑ i, min (T i ω) (c i)) →
    ∀ a : ι → ℕ, (∑ i, a i) = S →
      μ F ≤ min 1 (∑ i, cappedTail (c i) (b i) (a i))

def P9_statement : Prop :=
  ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ι → Ω → ℕ) (c : ι → ℕ) (S : ℕ)
    (b : ι → ℕ → ℝ≥0∞) (F : Set Ω),
    (∀ i s, s ≤ S → μ {ω | s < T i ω} ≤ b i s) →
    (∀ ω ∈ F, S < ∑ i, min (T i ω) (c i)) →
    μ F ≤ mixedAllocationBound S c b

def P9_ranges_statement : Prop :=
  ∀ {Ω ρ ι : Type} [MeasurableSpace Ω] [Fintype ρ] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ρ → ι → Ω → ℕ) (c : ρ → ι → ℕ) (S : ρ → ℕ)
    (b : ρ → ι → ℕ → ℝ≥0∞) (F : Set Ω),
    (∀ q i s, s ≤ S q → μ {ω | s < T q i ω} ≤ b q i s) →
    (∀ ω ∈ F, ∃ q, S q < ∑ i, min (T q i ω) (c q i)) →
    μ F ≤ min 1 (∑ q, mixedAllocationBound (S q) (c q) (b q))

end RebuildBound.Spec
