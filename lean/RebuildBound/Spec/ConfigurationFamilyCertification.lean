import RebuildBound.Spec.ConfigurationFamilyBound
import RebuildBound.Spec.AdaptiveStepsAssembly
import RebuildBound.Spec.KeyRelabel.Semantics

/-! Family capacity and observation claims for the serialized ideal model.
The public geometry, schedule, fixed key universe, joint ideal tapes and
observation agreement remain explicit in the underlying interfaces. -/
open scoped ENNReal
namespace RebuildBound.Spec
open ConfigurationFamily

/-- Shared causal capacity bound: at most h * 2^-64 for h positive windows. -/
def ConfigurationFamilyCausal_statement : Prop :=
  ∀ initialized m, m ∈ members →
    CausalWindowsFor (m.geometry initialized) (ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

/-- Fixed and adaptive executions use the same checked exposure budget. -/
def ConfigurationFamilyWindows_statement : Prop :=
  ∀ initialized m, m ∈ members →
    HierarchyWindowsFor (m.geometry initialized) (ENNReal.ofReal (1 / (2 : ℝ) ^ 64)) ∧
      AdaptiveWindowsFor (m.geometry initialized) (ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

/-- Distance from the public simulator, for scalar, batch and adaptive runs,
is at most h * 2^-64. Each execution uses one fixed run-wide key universe. -/
def ConfigurationFamilyOblivious_statement : Prop :=
  ∀ initialized m, m ∈ members →
    UniverseOnlineObliviousFor (m.geometry initialized) (ENNReal.ofReal (1 / (2 : ℝ) ^ 64)) ∧
      UniverseBatchObliviousFor (m.geometry initialized) (ENNReal.ofReal (1 / (2 : ℝ) ^ 64)) ∧
      AdaptiveObliviousFor (m.geometry initialized) (ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

end RebuildBound.Spec
