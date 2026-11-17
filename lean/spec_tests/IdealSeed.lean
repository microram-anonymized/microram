import RebuildBound.Proofs.IdealSeed
import RebuildBound.Proofs.IdealKeyLaw
import RebuildBound.Proofs.Key
import Mathlib.Probability.Distributions.Geometric

/-! Independent seeds with infinite support choose arbitrarily long exact
keys. This tests the mixture law, not the hierarchy's remaining exposure law. -/
namespace IdealSeedTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open MeasureTheory ProbabilityTheory IdealKey
open scoped ENNReal

noncomputable def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
noncomputable def coins : Measure Nat := geometricMeasure half
instance : IsProbabilityMeasure coins := by unfold coins; infer_instance

theorem seed_positive (seed : Nat) : 0 < coins {seed} := by
  rw [coins, geometricMeasure_singleton (show half ≠ 0 by
    intro h; have := congrArg Subtype.val h; norm_num [half] at this)]
  exact ENNReal.ofReal_pos.mpr (geometricMeasure_pos
    (by intro h; have := congrArg Subtype.val h; norm_num [half] at this)
    (by intro h; have := congrArg Subtype.val h; norm_num [half] at this) seed)

def key (seed : Nat) : LogicalKey := List.replicate (65 + seed) 0

theorem no_dictionary (dictionary : Finset LogicalKey) :
    ∃ seed, key seed ∉ dictionary ∧ 0 < coins {seed} := by
  refine ⟨dictionary.sup List.length + 1, ?_, seed_positive _⟩
  intro h
  have hlen := Finset.le_sup (f := List.length) h
  simp only [key, List.length_replicate] at hlen
  omega

example (seed : Nat) : LogicalKey.ofNat (LogicalKey.toNat (key seed)) = key seed :=
  LogicalKeyRoundtrip.1 _

def observedWord (seed : Nat) (tape : Tape) : Word64 := tape (.inl ((2, 7), key seed))

theorem read_measurable : Measurable (Function.uncurry observedWord) :=
  IdealSeedMeasurable Nat Word64 observedWord (fun _ => measurable_pi_apply _)

theorem read_slice (seed : Nat) : tapeLaw.map (observedWord seed) = wordLaw :=
  Measure.infinitePi_map_eval (fun _ : Coord => wordLaw) _

/-- Uniformity holds jointly with the private seed, not just after forgetting
it. There is no finite dictionary containing the keys of all positive-mass seeds. -/
example : (coins.prod tapeLaw).map (fun p => (p.1, observedWord p.1 p.2)) =
    coins.prod wordLaw ∧ (coins.prod tapeLaw).map (Function.uncurry observedWord) = wordLaw :=
  IdealSeedExact Nat coins Word64 wordLaw observedWord read_measurable read_slice

/-- A tape-derived value need not be an independent seed: its read is diagonal.
This negative pointwise witness prevents identifying that experiment with the
independent product construction merely because the marginals are uniform. -/
example : ∃ (seed : Word64) (tape : Tape), seed ≠ tape (.inr (0, 0)) := by
  exact ⟨0, fun _ => 1, by decide +kernel⟩

example : tapeLaw.map (fun tape => (tape (.inr (0, 0)), tape (.inr (0, 0)))) =
    wordLaw.map (fun word => (word, word)) := IdealKeyRepeated _

/-- The diagonal law is genuinely different from independent draws: the
off-diagonal rectangle has positive product mass and zero diagonal mass. -/
example : (wordLaw.prod wordLaw) ({0} ×ˢ {1}) ≠ 0 ∧
    wordLaw.map (fun word => (word, word)) ({0} ×ˢ {1}) = 0 := by
  constructor
  · rw [Measure.prod_prod]
    apply mul_ne_zero <;> simp [wordLaw, uniformOn_eq_zero_iff Set.finite_univ]
  · rw [Measure.map_apply (by fun_prop)
      ((measurableSet_singleton (0 : Word64)).prod (measurableSet_singleton (1 : Word64)))]
    have he : (fun word : Word64 => (word, word)) ⁻¹' ({0} ×ˢ {1}) = ∅ := by
      ext word
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h
      subst word
      decide +kernel
    rw [he, measure_empty]

/-- Weighted and zero-error coupling interfaces handle events depending on
the private seed, without imposing a finite seed support. -/
example (event : Set (Nat × Tape)) (hevent : MeasurableSet event)
    (budget : Nat → ℝ≥0∞)
    (hbudget : ∀ seed, tapeLaw (Prod.mk seed ⁻¹' event) ≤ budget seed) :
    (coins.prod tapeLaw) event ≤ ∫⁻ seed, budget seed ∂coins :=
  IdealSeedBound Nat coins event hevent budget hbudget

example (event : Set Word64) (hevent : MeasurableSet event) :
    (coins.prod tapeLaw) (Function.uncurry observedWord ⁻¹' event) ≤ wordLaw event + 0 ∧
      wordLaw event ≤ (coins.prod tapeLaw) (Function.uncurry observedWord ⁻¹' event) + 0 := by
  apply IdealSeedFailure Nat coins Word64 wordLaw observedWord observedWord ∅
    read_measurable read_measurable MeasurableSet.empty read_slice
    (fun _ _ _ => rfl) 0
  · intro seed; simp
  · exact hevent

end IdealSeedTests
