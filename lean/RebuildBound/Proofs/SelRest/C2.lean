import RebuildBound.Proofs.SelRest.Sound

namespace RebuildBound.SelRest

theorem chunk2_ok : chunkOk 2 := by
  unfold chunkOk
  have h : (chunk 2).all (fun x => selCheck scaleP x.1 x.2.2) = true := by
    unfold chunk scaleP
    decide +kernel
  intro x hx
  exact List.all_eq_true.mp h x hx

end RebuildBound.SelRest
