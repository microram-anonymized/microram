import RebuildBound.Spec.NativeNormalizePairs
import RebuildBound.Proofs.NativeMatch

/-! Local pair collisions specialize the existing independent comparison
bound to one segment and one partner. The probability law is unconditional;
neither distinct pairs nor independence of their collision events is needed.
Probability obstacles: none. -/
namespace RebuildBound
open Model Spec Spec.NativeNormalize Spec.NativeNormalizePairs Spec.NativeMatch MeasureTheory
open scoped ENNReal

namespace NativeNormalizePairsProof

def comparisons {Key : Type} (pairs : Pairs Key) : List (Comparison Key) :=
  pairs.map fun p => (p.1, [p.2])

lemma comparisons_weight {Key : Type} (pairs : Pairs Key) :
    weight 1 (comparisons pairs) = pairs.length := by
  induction pairs with
  | nil => simp [comparisons, weight]
  | cons pair pairs ih =>
    change 1 + weight 1 (comparisons pairs) = pairs.length + 1
    rw [ih, Nat.add_comm]

lemma event_append {Key Stored : Type} (stored : Key → Stored) (left right : Pairs Key) :
    PairBad stored (left ++ right) ↔ PairBad stored left ∨ PairBad stored right := by
  simp only [PairBad, List.mem_append]
  aesop

lemma section_measurable (bits : Nat) (pairs : Pairs LogicalKey) :
    MeasurableSet {stored : Tape bits | PairBad stored pairs} := by
  have heq : {stored : Tape bits | PairBad stored pairs} =
      ⋃ pair ∈ {p | p ∈ pairs}, {stored | pair.1 ≠ pair.2 ∧ stored pair.1 = stored pair.2} := by
    ext stored
    simp [PairBad, and_left_comm]
  rw [heq]
  refine MeasurableSet.biUnion (Set.to_countable _) fun pair _ => ?_
  by_cases h : pair.1 = pair.2
  · simp [h]
  · simpa [h] using measurableSet_eq_fun
      (measurable_pi_apply (X := fun _ : LogicalKey => Fingerprint bits) pair.1)
      (measurable_pi_apply (X := fun _ : LogicalKey => Fingerprint bits) pair.2)

lemma event_measurable {Env : Type} [MeasurableSpace Env] (bits : Nat)
    (pairs : Env → Pairs LogicalKey) (hpairs : ∀ l, MeasurableSet {env | pairs env = l}) :
    MeasurableSet {p : Env × Tape bits | PairBad p.2 (pairs p.1)} := by
  have heq : {p : Env × Tape bits | PairBad p.2 (pairs p.1)} =
      ⋃ l : Pairs LogicalKey, {env | pairs env = l} ×ˢ {stored | PairBad stored l} := by
    ext ⟨env, stored⟩
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun l => (hpairs l).prod (section_measurable bits l)

local instance : MeasurableSpace (Pairs LogicalKey) := ⊤
local instance : DiscreteMeasurableSpace (Pairs LogicalKey) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List (Comparison LogicalKey)) := ⊤
local instance : DiscreteMeasurableSpace (List (Comparison LogicalKey)) := ⟨fun _ => trivial⟩

lemma bound {Env : Type} [MeasurableSpace Env] (μ : Measure Env) [IsProbabilityMeasure μ]
    (bits budget : Nat) (pairs : Env → Pairs LogicalKey)
    (hpairs : ∀ l, MeasurableSet {env | pairs env = l})
    (hbudget : ∀ env, (pairs env).length ≤ budget) :
    (μ.prod (tapeLaw bits)) {p | PairBad p.2 (pairs p.1)} ≤ pairBound bits budget := by
  have hm : Measurable pairs := measurable_to_countable' hpairs
  have hcmp : Measurable (fun env => comparisons (pairs env)) :=
    (measurable_of_countable comparisons).comp hm
  have hb := NativeMatchIndependent μ 1 bits budget (fun env => comparisons (pairs env))
    (fun l => hcmp (measurableSet_singleton l))
    (fun env => by simpa [comparisons_weight] using hbudget env)
  have hsub : {p : Env × Tape (bits * 1) | PairBad p.2 (pairs p.1)} ⊆
      {p | ∃ c ∈ comparisons (pairs p.1), falseMatch (count := 1) (width := bits) p.2 c} := by
    rintro p ⟨pair, hpair, hne, heq⟩
    refine ⟨(pair.1, [pair.2]), List.mem_map.mpr ⟨pair, hpair, rfl⟩, ?_⟩
    constructor
    · simpa using hne
    · apply NativeMatchSound 1 bits
      simp [heq]
  have h := (measure_mono hsub).trans hb
  convert h using 1
  · exact congrArg (fun n => (μ.prod (tapeLaw n)) {p | PairBad p.2 (pairs p.1)})
      (Nat.mul_one bits).symm
  · simp only [pairBound, matchBound, Nat.mul_one]

end NativeNormalizePairsProof

theorem NativeNormalizePairsEvent : Spec.NativeNormalizePairsEvent_statement := by
  constructor
  · exact NativeNormalizePairsProof.event_append
  · intro Key Stored stored hinj pairs hbad
    obtain ⟨pair, _, hne, heq⟩ := hbad
    exact hne (hinj heq)

theorem NativeNormalizePairsMeasurable : Spec.NativeNormalizePairsMeasurable_statement :=
  NativeNormalizePairsProof.event_measurable

theorem NativeNormalizePairsBound : Spec.NativeNormalizePairsBound_statement :=
  NativeNormalizePairsProof.bound

end RebuildBound
