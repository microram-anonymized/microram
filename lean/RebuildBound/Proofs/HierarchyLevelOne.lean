import RebuildBound.Proofs.HierarchyLevelOne.Coords
import RebuildBound.Proofs.HierarchyLevelOne.Uniform
import RebuildBound.Proofs.DirectJobUniformCycle.Keys
import RebuildBound.Spec.HierarchyLaws31
import RebuildBound.Spec.HierarchyLevelOneGeometry

/-! # HierarchyLevelOne: level one's cycles on the family tape.

Cycle `c`'s tape is the restriction of the family tape to the coordinates
`(familyOf 1 (cycleOrdinal c j), k)` for `k ∈ cycleKeys … j`. The families
are coordinates of the horizon (`Coords.lean`), distinct across a cycle's
positions (`familyOfAux_injective`), so the restriction is a coordinate
selection along an injective index map and carries the uniform law to the
uniform law (`Uniform.lean`). -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.HierarchyLevelOneProof
open Model Model.Hierarchy Spec DirectJobUniformCycleProof

section
variable (cfg : Config) (hs : StepFacts cfg) (N : Nat) (tr : Trace) (hN : TracePremises cfg N tr)
include hs

theorem family_mem (c : Nat) (j : Fin (cfg.cycleLength c)) :
    familyOf cfg 1 (cfg.cycleOrdinal c j) ∈ cfg.coordinates.toFinset := by
  rw [List.mem_toFinset]
  apply mem_coordinates
  apply familyOfAux_inRange cfg hs
  have hj := j.2
  simp only [Config.cycleLength] at hj
  refine ⟨le_rfl, by simp [Config.levels], ?_, ?_⟩ <;>
    simp only [Config.cycleOrdinal] <;> omega

omit hs in
include hN in
theorem key_below (c : Nat) (j : Fin (cfg.cycleLength c)) (k : LogicalKey)
    (hk : k ∈ cycleKeys (cycleUnits cfg tr c).units j) : k.toNat < N := by
  obtain ⟨p, -, hp⟩ := (mem_cycleKeys _ j k).1 hk
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hp)
  exact hN.keys _ x hx

/-- The index map of cycle `c` into the family tape's coordinates. -/
def index (c : Nat) :
    (Σ j : Fin (cycleUnits cfg tr c).n, cycleKeys (cycleUnits cfg tr c).units j) → Coord cfg × KeyIndex N :=
  fun x => (⟨familyOf cfg 1 (cfg.cycleOrdinal c x.1), family_mem cfg hs c x.1⟩,
    ⟨x.2.1, key_below cfg N tr hN c x.1 x.2.1 x.2.2⟩)

theorem index_injective (c : Nat) : Function.Injective (index cfg hs N tr hN c) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  simp only [index, Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hj : j = j' := by
    have := familyOfAux_injective cfg _ _ _ _ h1
    simp only [Config.cycleOrdinal] at this
    exact Fin.ext (by omega)
  subst hj
  have : k = k' := Subtype.ext h2
  subst this
  rfl

/-- The restriction of the family tape to cycle `c`. -/
def restrict (c : Nat) (t : FamilyTape cfg N) : CycleTape (cycleUnits cfg tr c).units :=
  fun j k => t ⟨familyOf cfg 1 (cfg.cycleOrdinal c j), family_mem cfg hs c j⟩
    ⟨k.1, key_below cfg N tr hN c j k.1 k.2⟩

theorem restrict_eq (c : Nat) :
    restrict cfg hs N tr hN c =
      Equiv.piCurry (fun _ _ => Fin (2 ^ 64)) ∘ (fun f => f ∘ index cfg hs N tr hN c) ∘
        (Equiv.curry (Coord cfg) (KeyIndex N) (Fin (2 ^ 64))).symm := rfl

theorem map_restrict (c : Nat) :
    (ProbabilityTheory.uniformOn (Set.univ : Set (FamilyTape cfg N))).map
        (restrict cfg hs N tr hN c) =
      ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape (cycleUnits cfg tr c).units)) := by
  classical
  have h1 := map_uniform_equiv (Equiv.curry (Coord cfg) (KeyIndex N) (Fin (2 ^ 64))).symm
  have h3 := map_uniform_equiv (Equiv.piCurry fun (j : Fin (cycleUnits cfg tr c).n)
    (_ : cycleKeys (cycleUnits cfg tr c).units j) => Fin (2 ^ 64))
  have h2 := map_uniform_comp_injective (X := Fin (2 ^ 64)) _ (index_injective cfg hs N tr hN c)
  rw [restrict_eq, ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    ← Measure.map_map Measurable.of_discrete Measurable.of_discrete, h1, h2, h3]

end

/-- Cycle restriction uses the actual incoming population bound. -/
theorem levelOneGeometryFor (cfg : Config) (keyCapacity : Nat) (hs : StepFacts cfg) :
    HierarchyLevelOneGeometryFor cfg keyCapacity := by
  intro N tr _ hN Ω _ μ _ tape words ht
  refine ⟨fun c ω => restrict cfg hs N tr hN c (tape ω), fun c _ => le_rfl,
    fun c _ j u hu => hN.nodup _ u hu, fun c _ j => ?_, fun c _ => ⟨?_, ?_⟩,
    fun c _ j ω k hk => ?_⟩
  · calc (unitKeys ((cycleUnits cfg tr c).units j)).card
        ≤ ((DirectMasks.records (tr.units (c * cfg.fanout 1 + j))).map Rec.key).length :=
          List.toFinset_card_le _
      _ ≤ cfg.load * cfg.carry1 := by rw [List.length_map]; exact hN.load _
  · exact (Measurable.of_discrete (f := restrict cfg hs N tr hN c)).comp ht.measurable
  · show μ.map (restrict cfg hs N tr hN c ∘ tape) = _
    rw [← Measure.map_map Measurable.of_discrete ht.measurable, ht.uniform]
    exact map_restrict cfg hs N tr hN c
  · exact ht.agree ω ⟨_, family_mem cfg hs c j⟩ k _

/-- The selected interface is the 512-record specialization. -/
theorem levelOneFor (cfg : Config) (keyCapacity : Nat) (hs : StepFacts cfg)
    (hload : cfg.load * cfg.carry1 = 512) : HierarchyLevelOneFor cfg keyCapacity := by
  simpa only [HierarchyLevelOneGeometryFor, HierarchyLevelOneFor, hload] using
    levelOneGeometryFor cfg keyCapacity hs

theorem levelOneAt (cfg : Config) (rows : List (SepGeom × Nat)) (hs : StepFacts cfg)
    (hload : cfg.load * cfg.carry1 = 512) : HierarchyLevelOneAt cfg rows :=
  levelOneFor cfg (2 ^ 27) hs hload

theorem stepFacts_uniform : StepFacts uniformConfig := by
  intro ℓ h1 h2
  have : ℓ < 6 := h2
  interval_cases ℓ <;> decide

theorem stepFacts_half : StepFacts halfFanoutConfig := by
  intro ℓ h1 h2
  have : ℓ < 7 := h2
  interval_cases ℓ <;> decide

end RebuildBound.HierarchyLevelOneProof

theorem RebuildBound.HierarchyLevelOneGeometry :
    RebuildBound.Spec.HierarchyLevelOneGeometry_statement :=
  HierarchyLevelOneProof.levelOneGeometryFor

theorem RebuildBound.HierarchyLevelOne : RebuildBound.Spec.HierarchyLevelOne_statement :=
  ⟨HierarchyLevelOneProof.levelOneAt _ _ HierarchyLevelOneProof.stepFacts_uniform (by decide),
    HierarchyLevelOneProof.levelOneAt _ _ HierarchyLevelOneProof.stepFacts_half (by decide)⟩
