import RebuildBound.Spec.Hierarchy

/-! Uniform level-one tape projections at the configuration's actual incoming
load. The projection depends on chronological key populations and family
coordinates, independently of the direct job's routing plan. This interface
supplies no cycle-failure or numerical bound. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy

/-- Every level-one cycle is a uniform restriction of the family tape. Unit
populations obey the configuration's load bound, including widths below 16. -/
def HierarchyLevelOneGeometryFor (cfg : Config) (keyCapacity : Nat) : Prop :=
  ∀ (N : Nat) (tr : Trace), N ≤ keyCapacity → TracePremises cfg N tr →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape cfg N) (words : Ω → Words),
      TapePremises cfg N μ tape words →
      ∃ cycTape : ∀ c, Ω → CycleTape (cycleUnits cfg tr c).units,
        (∀ c < cfg.levelOneCycles, (cycleUnits cfg tr c).n ≤ cfg.cycleLength c) ∧
        (∀ c < cfg.levelOneCycles, ∀ j, ∀ u ∈ (cycleUnits cfg tr c).units j,
          (u.recs.map Rec.key).Nodup) ∧
        (∀ c < cfg.levelOneCycles, ∀ j,
          (unitKeys ((cycleUnits cfg tr c).units j)).card ≤ cfg.load * cfg.carry1) ∧
        (∀ c < cfg.levelOneCycles, Measurable (cycTape c) ∧
          μ.map (cycTape c) =
            ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape (cycleUnits cfg tr c).units))) ∧
        (∀ c < cfg.levelOneCycles, ∀ j ω k (hk : k ∈ cycleKeys (cycleUnits cfg tr c).units j),
          cycleNative cfg c j (words ω) k = cycTape c ω j ⟨k, hk⟩)

/-- The finite coordinate arithmetic suffices for the general projection.
There is no selected-shape, 512-record, or initialization premise. -/
def HierarchyLevelOneGeometry_statement : Prop :=
  ∀ (cfg : Config) (keyCapacity : Nat),
    (∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels →
      cfg.seed ℓ = cfg.fanout ℓ * cfg.seed (ℓ + 1) ∧ 0 < cfg.fanout ℓ ∧
        cfg.ordinals ℓ / cfg.fanout ℓ ≤ cfg.ordinals (ℓ + 1)) →
    HierarchyLevelOneGeometryFor cfg keyCapacity

end RebuildBound.Spec
