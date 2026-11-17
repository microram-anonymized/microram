import RebuildBound.Spec.NativeMatch
import RebuildBound.Proofs.IdealKeyLaw

/-!
# From one comparison to an inventory of comparisons

The random-function and permutation bounds share everything after the single
comparison, so that part is stated once, for any measure `ν` on any sample
space and any stored-key map `stored ω`. Its input is the one-comparison bound:
when the subject is not a partner, the rule accepts with probability at most
`partners ^ count / 2 ^ bits`. A union bound over a fixed comparison list then
charges `weight / 2 ^ bits`, capped at one by `matchBound`, and integrating
fixed lists against an independent environment whose lists all have weight at
most `budget` gives `matchBound count width budget`.
-/
namespace RebuildBound
open Spec Spec.NativeMatch Spec.NativeNormalize MeasureTheory
open scoped ENNReal

namespace NativeMatchProof

/-- A larger weight gives a larger bound. -/
theorem matchBound_mono (count width : Nat) {a b : Nat} (h : a ≤ b) :
    matchBound count width a ≤ matchBound count width b := by
  unfold matchBound
  gcongr

section Union

variable {Ω Key : Type} [MeasurableSpace Ω] (ν : Measure Ω) (count width : Nat)
  (stored : Ω → Key → Fingerprint (width * count))
  (hone : ∀ (x : Key) (P : List Key), x ∉ P →
    ν {ω | segMatch (stored ω x) (P.map (stored ω))} ≤
      ((P.length ^ count : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (width * count))
include hone

/-- Union bound over a fixed comparison list. -/
theorem list_le (cmp : List (Comparison Key)) :
    ν {ω | ∃ c ∈ cmp, falseMatch (stored ω) c} ≤
      (weight count cmp : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (width * count) := by
  induction cmp with
  | nil => simp
  | cons a l ih =>
    have hsplit : {ω | ∃ c ∈ a :: l, falseMatch (stored ω) c} =
        {ω | falseMatch (stored ω) a} ∪ {ω | ∃ c ∈ l, falseMatch (stored ω) c} := by
      ext ω
      simp
    have ha : ν {ω | falseMatch (stored ω) a} ≤
        ((a.2.length ^ count : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (width * count) := by
      by_cases hc : a.1 ∈ a.2
      · simp [falseMatch, hc]
      · exact (measure_mono fun ω h => h.2).trans (hone a.1 a.2 hc)
    rw [hsplit]
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add ha ih).trans_eq ?_
    simp [weight, ENNReal.add_div]

/-- The list bound capped at one. -/
theorem section_le [IsProbabilityMeasure ν] (cmp : List (Comparison Key)) :
    ν {ω | ∃ c ∈ cmp, falseMatch (stored ω) c} ≤ matchBound count width (weight count cmp) :=
  le_min prob_le_one (list_le ν count width stored hone cmp)

omit hone in
/-- The environment event is a countable union of measurable rectangles. -/
theorem event_measurable [Countable Key] {Env : Type} [MeasurableSpace Env]
    (hmeas : ∀ c, MeasurableSet {ω | falseMatch (stored ω) c})
    (cmp : Env → List (Comparison Key)) (hcmp : ∀ l, MeasurableSet {env | cmp env = l}) :
    MeasurableSet {p : Env × Ω | ∃ c ∈ cmp p.1, falseMatch (stored p.2) c} := by
  have : {p : Env × Ω | ∃ c ∈ cmp p.1, falseMatch (stored p.2) c} =
      ⋃ l : List (Comparison Key),
        {env | cmp env = l} ×ˢ ⋃ c ∈ {c | c ∈ l}, {ω | falseMatch (stored ω) c} := by
    ext ⟨env, ω⟩
    simp
  rw [this]
  exact MeasurableSet.iUnion fun l =>
    (hcmp l).prod (MeasurableSet.biUnion (Set.to_countable _) fun c _ => hmeas c)

/-- Comparison lists drawn from an independent environment, each of weight at
most `budget`. -/
theorem env_le [IsProbabilityMeasure ν] [Countable Key] {Env : Type} [MeasurableSpace Env]
    (μ : Measure Env) [IsProbabilityMeasure μ]
    (hmeas : ∀ c, MeasurableSet {ω | falseMatch (stored ω) c}) (budget : Nat)
    (cmp : Env → List (Comparison Key)) (hcmp : ∀ l, MeasurableSet {env | cmp env = l})
    (hw : ∀ env, weight count (cmp env) ≤ budget) :
    (μ.prod ν) {p | ∃ c ∈ cmp p.1, falseMatch (stored p.2) c} ≤
      matchBound count width budget :=
  IdealKeyLawProof.section_bound μ ν _ (event_measurable count width stored hmeas cmp hcmp) _ fun env =>
    (section_le ν count width stored hone (cmp env)).trans (matchBound_mono count width (hw env))

end Union

end NativeMatchProof

end RebuildBound
