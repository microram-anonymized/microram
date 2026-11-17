import RebuildBound.Spec.AdaptiveApi
import RebuildBound.Proofs.Adaptive.Semantics
import RebuildBound.Proofs.ApiCorrectness

/-! Deterministic transfer of API correctness to realized adaptive runs. -/

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Model.Adaptive

theorem AdaptiveRealizedSetting : AdaptiveRealizedSetting_statement := by
  intro geo U g m a S n hs words dummy
  have h0 := hs.2 (fun _ _ => 0)
  have hr := AdaptiveProof.adaptiveReplay geo.cfg geo.shapes g S m a n hs.1
    h0.2.2.2.1.geom.1 h0.2.2.2.1.geom.2 h0.2.2.2.2 words dummy
  rw [hr.1]
  exact hs.2 _

theorem AdaptiveApiCorrectness31 : AdaptiveApiCorrectness31_statement := by
  intro h hh U g m a S n hs c words dummy requests
  dsimp only
  intro hi
  have h0 := hs.2 (fun _ _ => 0)
  have hr := AdaptiveProof.adaptiveReplay (geometry31.chunk h).cfg
    (geometry31.chunk h).shapes g S m a n hs.1
    h0.2.2.2.1.geom.1 h0.2.2.2.1.geom.2 h0.2.2.2.2 words dummy
  have hlen : (OnlineBatch.slots (realized (geometry31.chunk h).cfg
      (geometry31.chunk h).shapes g S a words dummy)).length = slotCount a.shape := by
    rw [hr.1]
    exact (ReplayShape m a n _).2.2.1
  apply BatchApiCorrectness31 h hh U g _ S m ?_ c words dummy requests hi
  have hsetting := AdaptiveRealizedSetting _ U g m a S n hs words dummy
  simpa only [hlen, hs.1] using hsetting

end RebuildBound
