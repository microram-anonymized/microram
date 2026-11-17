import RebuildBound.Proofs.FiniteCoupling

/-! # HierarchyLevelOne: the uniform law along a coordinate selection.

`map_uniform_of_split`: the first component of a split of a finite uniform
space is uniform. `map_uniform_comp_injective`: restricting a uniform
function along an injective index map is uniform. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.HierarchyLevelOneProof

/-- The pushforward of the uniform law along the first component of a split
`A ≃ B × U` is uniform. -/
theorem map_uniform_of_split {A B U : Type} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [DiscreteMeasurableSpace A] [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B] [Fintype U] [Nonempty U]
    (split : A ≃ B × U) (f : A → B) (hf : ∀ a, (split a).1 = f a) :
    (ProbabilityTheory.uniformOn (Set.univ : Set A)).map f =
      ProbabilityTheory.uniformOn (Set.univ : Set B) := by
  rw [Measure.ext_iff_singleton]
  intro b
  rw [Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton b)]
  have hset : f ⁻¹' {b} = {a | (split a).1 = b} := by
    ext a
    simp [hf]
  rw [hset, DirectJobUniformProof.uniform_projection split b, ProbabilityTheory.uniformOn_univ,
    Measure.count_singleton, one_div]

/-- Restricting a uniform function along an injective map of finite index
types is uniform. -/
theorem map_uniform_comp_injective {I J X : Type} [Fintype I] [DecidableEq I] [Fintype J]
    [Fintype X] [Nonempty X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (ι : J → I) (hι : Function.Injective ι) :
    (ProbabilityTheory.uniformOn (Set.univ : Set (I → X))).map (fun f => f ∘ ι) =
      ProbabilityTheory.uniformOn (Set.univ : Set (J → X)) := by
  classical
  let e : J ≃ Set.range ι := Equiv.ofInjective ι hι
  let split : (I → X) ≃ (J → X) × ({i // i ∉ Set.range ι} → X) :=
    (Equiv.piEquivPiSubtypeProd (· ∈ Set.range ι) fun _ => X).trans
      (Equiv.prodCongr (Equiv.arrowCongr e.symm (Equiv.refl X)) (Equiv.refl _))
  exact map_uniform_of_split split _ fun f => rfl

end RebuildBound.HierarchyLevelOneProof

namespace RebuildBound.HierarchyLevelOneProof

/-- A bijection of finite spaces carries the uniform law to the uniform law. -/
theorem map_uniform_equiv {A B : Type} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [DiscreteMeasurableSpace A] [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (e : A ≃ B) :
    (ProbabilityTheory.uniformOn (Set.univ : Set A)).map e =
      ProbabilityTheory.uniformOn (Set.univ : Set B) :=
  map_uniform_of_split (e.trans (Equiv.prodPUnit B).symm) e fun _ => rfl

end RebuildBound.HierarchyLevelOneProof
