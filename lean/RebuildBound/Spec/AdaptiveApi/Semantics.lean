import RebuildBound.Spec.Adaptive.Semantics
import RebuildBound.Spec.ApiCorrectness.Semantics

/-! The generic deterministic bridge from adaptive settings to the realized fixed run. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive

/-- The actual run issued by an admissible adaptive client satisfies the
fixed-run setting, including all structural and unshadowed premises. -/
def AdaptiveRealizedSetting_statement : Prop :=
  ∀ (geo : HierarchyGeometry) (U : Finset LogicalKey) (g : OnlineGeom) (m : Nat)
    (a : AdaptiveRun m) (S : Schedule) (n : Nat),
    AdaptiveSetting geo U g a S n →
    ∀ (words : Words) (dummy : Nat → Nat → Nat),
      UniverseBatchSetting geo U g (realized geo.cfg geo.shapes g S a words dummy) S n m

end RebuildBound.Spec
