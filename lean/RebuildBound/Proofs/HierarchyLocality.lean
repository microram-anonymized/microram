import RebuildBound.Proofs.HierarchyLocality.Time
import RebuildBound.Spec.HierarchyLaws31

/-!
# HierarchyLocality: word locality of the tables along the cones

Part (1), for every configuration, shapes and trace (`table_congr`): induction
on `(ℓ, v)` (strong on the level, then on the ordinal), mirroring `table` and
`cone`. The induction hypotheses give the level's previous table and the carry
equal under both tapes (their cones are sublists of `cone ℓ v`); the head
`(ℓ, v)` of the cone gives agreement of `jobWord ℓ v` on `jobKeys ℓ v`, which
contains the keys of every record the step reads; one reference congruence per
role closes the step (`step_congr`). Level one's old word is read only at A's
main keys: either A is empty, or `(1, v - 1)` heads `cone 1 (v - 1)` and its
own table's keys are in `jobKeys 1 (v - 1)`.

Part (2) (`family_ne`): the level-one time is kept by every forward, never
grows along a cone from a coordinate at or above its seeded counter, and
`time ℓ (v - 1) < time ℓ v`.
-/

namespace RebuildBound.HierarchyLocalityProof
open Model Model.DirectJob Model.Hierarchy Spec

theorem timeFacts_uniform : TimeFacts uniformConfig := by
  refine ⟨?_, ?_, ?_⟩ <;> intro ℓ h1 h2 <;>
    (have : ℓ ≤ 6 := by simp [Config.levels, uniformConfig] at h2; omega) <;>
    interval_cases ℓ <;> first | decide | (simp [Config.levels, uniformConfig] at h2)

theorem timeFacts_half : TimeFacts halfFanoutConfig := by
  refine ⟨?_, ?_, ?_⟩ <;> intro ℓ h1 h2 <;>
    (have : ℓ ≤ 7 := by simp [Config.levels, halfFanoutConfig] at h2; omega) <;>
    interval_cases ℓ <;> first | decide | (simp [Config.levels, halfFanoutConfig] at h2)

/-- The locality proof works for arbitrary execution shapes. -/
theorem localityFor (cfg : Config) (sh : Shapes) (hf : TimeFacts cfg) :
    HierarchyLocalityFor cfg sh :=
  ⟨fun tr words words' ℓ v h => table_congr cfg sh tr words words' ℓ v h, family_ne cfg hf⟩

theorem localityAt (cfg : Config) (rows : List (SepGeom × Nat)) (hf : TimeFacts cfg) :
    HierarchyLocalityAt cfg rows :=
  localityFor cfg (hierarchyShapes cfg rows) hf

end RebuildBound.HierarchyLocalityProof

open RebuildBound.HierarchyLocalityProof in
theorem RebuildBound.HierarchyLocality : RebuildBound.Spec.HierarchyLocality_statement :=
  ⟨localityAt _ _ timeFacts_uniform, localityAt _ _ timeFacts_half⟩
