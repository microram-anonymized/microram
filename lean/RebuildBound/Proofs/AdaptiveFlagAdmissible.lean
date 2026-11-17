import RebuildBound.Proofs.AdaptiveFlagAdmissible.Semantics
import RebuildBound.Proofs.Adaptive

/-!
# Package AdaptiveFlagAdmissible

Statements in `Spec/AdaptiveNative.lean`.

* `AdaptiveFlagAdmissibleStep`: a client whose flags follow the engine's rule
  (`FlagRule`) on every branch, at the all-zero words, meets the adaptive
  setting. The separate `Semantics` module mirrors `AdaptiveAdmissibleStep`
  (`Proofs/AdaptiveReplay.lean`),
  with the unshadowed promise of each replayed run given by `FlagSoundness31`
  at the all-zero words instead of by an all-false flag.
* `AdaptiveTwoClients31`: two clients with the same public shape are each
  within `h · 2^-64` of the same simulator law (`AdaptiveOblivious31`), so
  within `2 · h · 2^-64` of each other.

No probability obstacle: the second theorem only chains two inequalities in
`ℝ≥0∞`.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Model.Adaptive

/-! ### Two clients through one encoding -/

theorem AdaptiveTwoClients31 : AdaptiveTwoClients31_statement := by
  intro h hh U U' g m a a' S n hshape hset hset' Ω Ω' _ _ μ μ' _ _ tape dtape words tape' dtape'
    words' hprem hprem' V _ obs obs' ι hobs hobs' hι hagree hagree' A hA
  obtain ⟨h1, h2⟩ :=
    AdaptiveOblivious31 h hh U g m a S n hset μ tape dtape words hprem obs ι hobs hι hagree A hA
  obtain ⟨h1', h2'⟩ :=
    AdaptiveOblivious31 h hh U' g m a' S n hset' μ' tape' dtape' words' hprem' obs' ι hobs' hι
      hagree' A hA
  rw [hshape] at h1' h2'
  set e : ℝ≥0∞ := (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64)
  rw [two_mul]
  constructor
  · calc μ (obs ⁻¹' A) ≤ _ := h1
      _ ≤ μ' (obs' ⁻¹' A) + e + e := by gcongr
      _ = μ' (obs' ⁻¹' A) + (e + e) := add_assoc _ _ _
  · calc μ' (obs' ⁻¹' A) ≤ _ := h1'
      _ ≤ μ (obs ⁻¹' A) + e + e := by gcongr
      _ = μ (obs ⁻¹' A) + (e + e) := add_assoc _ _ _

end RebuildBound
