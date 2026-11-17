import RebuildBound.Spec.NativeApi
import RebuildBound.Proofs.AdaptiveApi
import RebuildBound.Proofs.NativeAdapter

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Model.Adaptive Model.NativeAdapter

namespace NativeApiProof

/-- The local interface equations discharge post-record implementation. -/
theorem implements {c : Api.Codec} {cfg : Config} {sh : Shapes} {g : OnlineGeom}
    {run : OnlineBatch.BatchRun} {S : Schedule} {words : Words}
    {dummy : Nat → Nat → Nat} {requests : List Api.Request}
    {selected : Nat → Option Rec} {returned : Nat → NativeApi.Response}
    (H : NativeApi.Local c cfg sh g run S words dummy requests selected returned) :
    Api.Implements c cfg sh g run S words dummy requests := by
  refine ⟨H.length, ?_⟩
  intro t q s hq hs
  obtain ⟨hk, hp, hsel, hpost, _⟩ := H.slot t q s hq hs
  exact ⟨hk, hp, by simpa only [hsel] using hpost⟩

/-- Transfer logical correctness to the separately supplied native responses. -/
theorem correct {c : Api.Codec} {cfg : Config} {sh : Shapes} {g : OnlineGeom}
    {run : OnlineBatch.BatchRun} {S : Schedule} {words : Words}
    {dummy : Nat → Nat → Nat} {requests : List Api.Request}
    {selected : Nat → Option Rec} {returned : Nat → NativeApi.Response}
    (H : NativeApi.Local c cfg sh g run S words dummy requests selected returned)
    (HC : ApiCorrect c cfg sh g run S words dummy requests) :
    NativeApi.Correct c run requests returned := by
  refine ⟨HC.1, ?_⟩
  intro t q s hq hs
  obtain ⟨_, _, hsel, _, hresp⟩ := H.slot t q s hq hs
  obtain ⟨hbatch, hscalar, _⟩ := HC.2 t q s hq hs
  rw [hresp, hsel]
  unfold NativeApi.response
  split
  · exact congrArg NativeApi.Response.batch hbatch
  · exact congrArg NativeApi.Response.scalar hscalar

end NativeApiProof

theorem NativeApiCorrectness31 : NativeApiCorrectness31_statement := by
  intro h hh U g run S m hs c words dummy requests selected returned hlocal
  exact NativeApiProof.correct hlocal
    (BatchApiCorrectness31 h hh U g run S m hs c words dummy requests
      (NativeApiProof.implements hlocal))

theorem NativeAdapterApiCorrectness31 : NativeAdapterApiCorrectness31_statement := by
  intro h hh U g m Public View State p encode metadata S n hs M words dummy R hagree
    c requests selected returned hlocal
  have hops := (NativeAdapterAgreement _ _ g S m Public View State p encode metadata M
    words dummy R hagree).1
  have hrun : NativeApi.machineRun M p =
      realized (geometry31.chunk h).cfg (geometry31.chunk h).shapes g S
        (p.folded encode metadata) words dummy := by
    change (⟨(M.prefix p p.shape).1, p.init, p.unsh⟩ : OnlineBatch.BatchRun) =
      ⟨(interact (geometry31.chunk h).cfg (geometry31.chunk h).shapes g S
        (p.folded encode metadata) words dummy).1, p.init, p.unsh⟩
    exact congrArg (fun ops => OnlineBatch.BatchRun.mk ops p.init p.unsh) hops
  have hi := NativeApiProof.implements hlocal
  rw [hrun] at hi
  have hc := AdaptiveApiCorrectness31 h hh U g m (p.folded encode metadata) S n hs
    c words dummy requests hi
  rw [← hrun] at hc
  exact NativeApiProof.correct hlocal hc

end RebuildBound
