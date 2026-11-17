import RebuildBound.Spec.Model.Key
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.UniformOn

/-!
# Canonical ideal routing law for arbitrary byte keys

Only the coordinate type is discrete. The tape has the product sigma algebra.
Family identities are the model's unbounded (level, ordinal) pairs; adopted
copies must use the same pair. Dummy coordinates have their own tagged domain.
This interface proves the common experiment, not hierarchy freshness or loads.
-/
namespace RebuildBound.Spec.IdealKey
open Model MeasureTheory ProbabilityTheory
open scoped ENNReal

abbrev Family := Nat × Nat
abbrev Coord := (Family × LogicalKey) ⊕ (Nat × Nat)
abbrev Tape := Coord → Word64

instance : MeasurableSpace Coord := ⊤
instance : DiscreteMeasurableSpace Coord := ⟨fun _ => trivial⟩

noncomputable def wordLaw : Measure Word64 := uniformOn Set.univ
noncomputable def tapeLaw : Measure Tape := Measure.infinitePi fun _ => wordLaw

instance wordLaw_probability : IsProbabilityMeasure wordLaw := by
  unfold wordLaw
  infer_instance

instance tapeLaw_probability : IsProbabilityMeasure tapeLaw := by
  unfold tapeLaw
  infer_instance

end RebuildBound.Spec.IdealKey

namespace RebuildBound.Spec
open Model MeasureTheory ProbabilityTheory IdealKey
open scoped ENNReal

def IdealKeyProbability_statement : Prop := IsProbabilityMeasure tapeLaw

def IdealKeyRestriction_statement : Prop :=
  ∀ I : Finset IdealKey.Coord,
    tapeLaw.map I.restrict = Measure.pi (fun _ : I => wordLaw) ∧
    tapeLaw.map I.restrict = uniformOn (Set.univ : Set (I → Word64))

def IdealKeySelection_statement : Prop :=
  ∀ (ι : Type) [Fintype ι] (pick : ι → IdealKey.Coord), Function.Injective pick →
    tapeLaw.map (fun tape i => tape (pick i)) = Measure.pi (fun _ : ι => wordLaw)

def IdealKeyRepeated_statement : Prop :=
  ∀ c : IdealKey.Coord, tapeLaw.map (fun tape => (tape c, tape c)) =
    wordLaw.map (fun word => (word, word))

def IdealKeyBlocks_statement : Prop :=
  ∀ S T : Set IdealKey.Coord, Disjoint S T →
    IndepFun S.domRestrict T.domRestrict tapeLaw ∧
    tapeLaw.map (fun tape => (S.domRestrict tape, T.domRestrict tape)) =
      (Measure.infinitePi (fun _ : S => wordLaw)).prod
        (Measure.infinitePi (fun _ : T => wordLaw))

def IdealKeyConsistent_statement : Prop :=
  ∀ (I J : Finset IdealKey.Coord) (hIJ : I ⊆ J) (tape : Tape),
    (fun i : I => J.restrict tape ⟨i.val, hIJ i.property⟩) = I.restrict tape

def IdealKeyDynamic_statement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (tape : Ω → Tape), Measurable tape →
    ∀ pick : Ω → IdealKey.Coord, Measurable pick →
      Measurable (fun ω => tape ω (pick ω))

def IdealKeySelectedKeys_statement : Prop :=
  ∀ (Environment : Type) (keys : Environment → Finset LogicalKey)
    (family : Family) (e : Environment),
    tapeLaw.map (fun tape (key : keys e) => tape (.inl (family, key.val))) =
      Measure.pi (fun _ : keys e => wordLaw)

/-- Sectionwise bounds need no measurable choice of finite witnesses. The
outside environment is explicitly independent of this fresh tape. -/
def IdealKeySections_statement : Prop :=
  ∀ (Environment : Type) [MeasurableSpace Environment]
    (μ : Measure Environment) [IsProbabilityMeasure μ]
    (event : Set (Environment × Tape)), MeasurableSet event → ∀ bound : ℝ≥0∞,
    (∀ e, ∃ (I : Finset IdealKey.Coord) (localEvent : Set (I → Word64)),
      MeasurableSet localEvent ∧ Prod.mk e ⁻¹' event = I.restrict ⁻¹' localEvent ∧
      (Measure.pi (fun _ : I => wordLaw)) localEvent ≤ bound) →
    (μ.prod tapeLaw) event ≤ bound

/-- A fresh block and its complete outside environment are restrictions of one
canonical tape. Bounds are integrated over that actual split. -/
def IdealKeyOutsideSections_statement : Prop :=
  ∀ (fresh : Set IdealKey.Coord)
    (event : Set ((↥(freshᶜ) → Word64) × (fresh → Word64))),
    MeasurableSet event → ∀ bound : ℝ≥0∞,
    (∀ outside, (Measure.infinitePi (fun _ : fresh => wordLaw))
      (Prod.mk outside ⁻¹' event) ≤ bound) →
    tapeLaw ((fun tape => ((freshᶜ).domRestrict tape, fresh.domRestrict tape)) ⁻¹' event)
      ≤ bound

end RebuildBound.Spec
