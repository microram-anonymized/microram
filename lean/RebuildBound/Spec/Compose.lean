import RebuildBound.Spec.Model.ConfigRows
import RebuildBound.Spec.Selected
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The composition over a horizon (trusted, package G4a)

`REPORT.tex`, Theorem `thm:abstract-composition` with the exposure count of
Proposition `prop:ordinal-exposures`.

* **Expo**: for every valid configuration (fanouts at least two, positive
  load and level-one carry width), summing any
  per-class bound over the potential jobs equals summing it over the classes
  weighted by the report's counts `n_(ℓ,d)(H)`, `m_L(H)` and one
  initialization. So the floor formula counts the potential ordinals of each
  digit exactly, at every seed and horizon.
* **G4a**: on any probability space, if every capacity failure in the
  horizon lies in the event of some potential job (the composition's
  covering premise: a first failure implies its job's reference event, and
  every job that can fail is a potential one), and each potential job's
  event has probability at most its class's bound, then the failure
  probability is at most `min(1, Σ n · b)` over `exposures`. No independence
  between jobs is assumed; the jobs' events are evaluated on reference
  inputs, so the law is never conditioned on earlier success.
* **SelExpo**: the two selected configurations (`uniformConfig`, six levels
  of fanout eight; `halfFanoutConfig`, fanouts 4, 4, 4, 8, 8, 8; both with
  `U_1 = 16`, top digit 8, `2^32` accesses after a direct initialization).
  Their separated classes (levels 2 to `L - 1`, digits 2 and up), in
  exposure order, have exactly the counts that `Spec/Selected.lean`
  transcribed from the Python ledger, and the top has 257 ordinals.

The per-class bounds come from the per-role job theorems (SJob, G3, …) once
each potential job's event is known to have its role's law. That link, and
the covering premise, come from the hierarchy model (`Spec/Model/Hierarchy.lean`).
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Model

/-- The exposure-weighted sum `Σ n · b(class)` of per-class bounds. -/
noncomputable def Config.exposureSum (cfg : Config) (b : JobClass → ℝ≥0∞) : ℝ≥0∞ :=
  (cfg.exposures.map fun p => (p.2 : ℝ≥0∞) * b p.1).sum

/-- The counts of a configuration's separated classes (levels 2 to `L - 1`,
digits 2 and up), in exposure order. -/
def Config.separatedCounts (cfg : Config) : List Nat :=
  cfg.exposures.filterMap fun p =>
    match p.1 with
    | .ordinary ℓ d => if 2 ≤ ℓ ∧ 2 ≤ d then some p.2 else none
    | _ => none

/-- The rows of a configuration match its separated classes position by
position: as many rows as classes, and the row paired with class `(ℓ, d)` has
digit `d`, carry width `U_ℓ` and a valid geometry. -/
def Config.RowsMatch (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  cfg.separatedClasses.length = rows.length ∧
    ∀ q ∈ cfg.separatedClasses.zip rows,
      q.2.1.d = q.1.2 ∧ q.2.1.U = cfg.carry q.1.1 ∧ q.2.1.Valid

instance (cfg : Config) (rows : List (SepGeom × Nat)) : Decidable (cfg.RowsMatch rows) :=
  inferInstanceAs (Decidable (_ ∧ _))

end RebuildBound.Model

namespace RebuildBound.Spec

open RebuildBound.Model

/-- **Expo**: the exposure counts are the numbers of potential jobs of each
class. -/
def Expo_statement : Prop :=
  ∀ cfg : Config, cfg.Valid → ∀ b : JobClass → ℝ≥0∞,
    (cfg.potentialJobs.map fun j => b (cfg.classOf j)).sum = cfg.exposureSum b

/-- **G4a**: the conditional composition over the horizon. -/
def G4a_statement : Prop :=
  ∀ cfg : Config, cfg.Valid →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (fails : Set Ω) (event : JobId → Set Ω) (b : JobClass → ℝ≥0∞),
    (∀ ω ∈ fails, ∃ j ∈ cfg.potentialJobs, ω ∈ event j) →
    (∀ j ∈ cfg.potentialJobs, μ (event j) ≤ b (cfg.classOf j)) →
    μ fails ≤ min 1 (cfg.exposureSum b)

/-- The uniform selected configuration: six levels of fanout eight. -/
def uniformConfig : Config :=
  { fanouts := [8, 8, 8, 8, 8], carry1 := 16, topDigit := 8, load := 32,
    horizon := 2 ^ 32, initialized := true }

/-- The half-fanout selected configuration: fanouts 4, 4, 4, 8, 8, 8. -/
def halfFanoutConfig : Config :=
  { fanouts := [4, 4, 4, 8, 8, 8], carry1 := 16, topDigit := 8, load := 32,
    horizon := 2 ^ 32, initialized := true }

/-- **SelExpo**: the selected configurations' separated counts are the ones
`Spec/Selected.lean` transcribed, each row's geometry belongs to the class it
is paired with, and the top has 257 ordinals. -/
def SelExpo_statement : Prop :=
  uniformSeparated.map Prod.snd = uniformConfig.separatedCounts ∧
    halfFanoutSeparated.map Prod.snd = halfFanoutConfig.separatedCounts ∧
    uniformConfig.RowsMatch uniformSeparated ∧
    halfFanoutConfig.RowsMatch halfFanoutSeparated ∧
    uniformConfig.ordinals uniformConfig.levels = 257 ∧
    halfFanoutConfig.ordinals halfFanoutConfig.levels = 257

end RebuildBound.Spec
