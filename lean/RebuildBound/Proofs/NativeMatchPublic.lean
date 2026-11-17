import RebuildBound.Spec.NativeMatch.Public
import RebuildBound.Proofs.NativeMatchLinearCoded
import RebuildBound.Proofs.NativeMatchPublicFit
import RebuildBound.Proofs.NativeMatchRing

namespace RebuildBound
open Spec NativeMatchProduction NativeMatchPublicFit NativeMatchPhysical
open Model Model.Hierarchy

theorem NativeMatchPublicChecks : Spec.NativeMatchPublicChecks_statement := by
  intro member initialized h ctx hm hv hc
  simp only [NativeMatchPublic.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hf : FamilyTimeFit ctx := by
    intro level hlo hhi
    have hmem : level - 1 ∈ List.range ctx.geo.cfg.levels := List.mem_range.mpr (by omega)
    have ht := List.all_eq_true.mp hc.1.1 (level - 1) hmem
    have hl : level - 1 + 1 = level := by omega
    simpa only [hl, decide_eq_true_eq] using ht
  have hr : publicReady ctx.unit ctx.snapshots ctx.client.shape ctx.accesses = true := hc.2
  exact ⟨NativeMatchPublicFieldsFit member initialized h ctx hm hv hf,
    NativeMatchPublicCounterFit member initialized h ctx hc.1.2, by simpa [hr] using NativeMatchRingCost ctx⟩

theorem NativeMatchPublicFailure : Spec.NativeMatchPublicFailure_statement := by
  intro member initialized hm h hh ctx hv model width hmodel hw hc policy
  obtain ⟨hf, hd, hr⟩ := NativeMatchPublicChecks member initialized h ctx hm hv hc
  simpa only [NativeMatchLinearCoded.bestError, hr, add_zero, NativeMatchPublic.error] using
    NativeMatchBestCodedFailure member initialized hm h hh ctx hv model width hmodel hw hf hd policy

theorem NativeMatchPublicObservation : Spec.NativeMatchPublicObservation_statement := by
  intro member initialized hm h hh ctx hv model width hmodel hw hc policy event hevent
  obtain ⟨hf, hd, hr⟩ := NativeMatchPublicChecks member initialized h ctx hm hv hc
  simpa only [NativeMatchLinearCoded.bestError, hr, add_zero, NativeMatchPublic.error] using
    NativeMatchBestCodedObservation member initialized hm h hh ctx hv model width hmodel hw hf hd policy event hevent
end RebuildBound
