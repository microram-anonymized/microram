import RebuildBound.Spec.Configuration31
import RebuildBound.Spec.KeyRelabelStructure.Semantics
import RebuildBound.Spec.KeyUniverse

/-! Pattern independence and real-probe freshness for a fixed key universe.
Only the numeric key bound is replaced by membership in that universe. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.OnlineBatch

def GenericOnlinePattern31_statement : Prop :=
  ∀ h, 1 ≤ h → UniverseOnlinePatternFor (geometry31.chunk h)

def GenericOnlineFresh31_statement : Prop :=
  ∀ h, 1 ≤ h → UniverseOnlineFreshFor (geometry31.chunk h)

def GenericBatchPattern31_statement : Prop :=
  ∀ h, 1 ≤ h → UniverseBatchPatternFor (geometry31.chunk h)

def GenericBatchFresh31_statement : Prop :=
  ∀ h, 1 ≤ h → UniverseBatchFreshFor (geometry31.chunk h)

end RebuildBound.Spec
