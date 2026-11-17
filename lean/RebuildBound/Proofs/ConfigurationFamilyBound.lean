import RebuildBound.Proofs.ConfigurationFamilyBound.Transfer
import RebuildBound.Proofs.ConfigurationFamilyNumerics

/-! Certified planner-family capacity and privacy. One structural/probability
proof and shared exact-shape arithmetic certificates cover every listed
geometry from both starts. Native planner and execution refinement remain
separate from these ideal-model statements. -/
namespace RebuildBound
open Spec

theorem ConfigurationFamilyCausal : ConfigurationFamilyCausal_statement :=
  ConfigurationFamilyBoundProof.causal ConfigurationFamilyNumerics

theorem ConfigurationFamilyWindows : ConfigurationFamilyWindows_statement :=
  ConfigurationFamilyBoundProof.windows ConfigurationFamilyCausal

theorem ConfigurationFamilyOblivious : ConfigurationFamilyOblivious_statement :=
  ConfigurationFamilyBoundProof.oblivious ConfigurationFamilyWindows

end RebuildBound
