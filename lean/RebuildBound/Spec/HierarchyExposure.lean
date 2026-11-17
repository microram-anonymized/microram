import RebuildBound.Spec.Compose

/-! Empty-start exposure accounting, shared by every geometry and horizon.
This counts reference jobs; it does not supply their probability laws. -/

open scoped ENNReal
namespace RebuildBound.Spec
open Model

/-- Empty initialization removes precisely the initialization exposure.
Ordinary, preparation and finish counts are unchanged. -/
def HierarchyExposure_statement : Prop :=
  ∀ cfg : Config,
    cfg.exposures = ({cfg with initialized := false} : Config).exposures ++
      (if cfg.initialized then [(.initialization, 1)] else [])

/-- Any shared per-class bounds give the same repeated-job budget at either
start. Addition avoids any finiteness premise needed by subtraction. -/
def HierarchyExposureBudget_statement : Prop :=
  ∀ (cfg : Config) (B : JobClass → ℝ≥0∞),
    cfg.exposureSum B = ({cfg with initialized := false} : Config).exposureSum B +
      (if cfg.initialized then B .initialization else 0) ∧
    ({cfg with initialized := false} : Config).exposureSum B ≤ cfg.exposureSum B

end RebuildBound.Spec
