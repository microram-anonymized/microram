import RebuildBound.Spec.NativeAdapter
import RebuildBound.Proofs.Adaptive
import RebuildBound.Proofs.AdaptiveFlagAdmissible

/-! A prefix induction, followed by the existing adaptive probability theorem. -/
namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Model.Adaptive Model.NativeAdapter

namespace NativeAdapterProof

/-- Agreement holds after every public operation prefix, including empty
chunks. The operation index is independent of the number of emitted rows. -/
theorem prefixes (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} {Public View State : Type} (p : Program View) (encode : Encoding m Public View)
    (metadata : Public) (M : Machine State View) (words : Words) (dummy : Nat → Nat → Nat)
    (R : List Kind → State → Prop)
    (H : NativeLocalAgreement cfg sh g S p encode metadata M words dummy R)
    (pre : List Kind) (hp : pre <+: p.shape) :
    R pre (M.prefix p pre).2 ∧
      M.observe (M.prefix p pre).2 =
        encode metadata (referencePrefix cfg sh g S p encode metadata words dummy pre).2 ∧
      (M.prefix p pre).1 = (referencePrefix cfg sh g S p encode metadata words dummy pre).1 := by
  induction pre using List.reverseRecOn with
  | nil => exact ⟨H.1, H.2.1, rfl⟩
  | append_singleton pre k ih =>
    have hp0 : pre <+: p.shape := (List.prefix_append pre [k]).trans hp
    obtain ⟨hr, ho, hops⟩ := ih hp0
    obtain ⟨hr', ho'⟩ := H.2.2 pre k (M.prefix p pre).2 hp hr ho
    have hn : M.prefix p (pre ++ [k]) = M.issue p (M.prefix p pre) k := by
      simp [Machine.prefix, List.foldl_append]
    refine ⟨by simpa [hn, Machine.issue] using hr', ?_, ?_⟩
    · simpa [hn, Machine.issue] using ho'
    · rw [hn]
      simp only [Machine.issue, referencePrefix, List.foldl_append, List.foldl_cons,
        List.foldl_nil, Adaptive.issue, Program.folded]
      change (M.prefix p pre).1 ++ [k.op (p.next (M.observe (M.prefix p pre).2))] =
        (referencePrefix cfg sh g S p encode metadata words dummy pre).1 ++
          [k.op (p.next (encode metadata
            (referencePrefix cfg sh g S p encode metadata words dummy pre).2))]
      rw [ho, hops]

end NativeAdapterProof

/-- Local transition simulation determines the entire adaptive execution. -/
theorem NativeAdapterAgreement : NativeAdapterAgreement_statement := by
  intro cfg sh g S m Public View State p encode metadata M words dummy R H
  obtain ⟨_, ho, hops⟩ := NativeAdapterProof.prefixes cfg sh g S p encode metadata M words dummy R H
    p.shape (List.prefix_refl _)
  refine ⟨hops, ?_⟩
  change M.observation p = encode metadata
    (rowsOf (transcript cfg sh g S (p.folded encode metadata) (slotCount p.shape) words dummy)
      (slotCount p.shape))
  have hrows := AdaptiveReplayProof.rowsOf_transcript cfg sh g S (p.folded encode metadata)
    (slotCount p.shape) rfl words dummy
    (interact cfg sh g S (p.folded encode metadata) words dummy).2 (List.prefix_refl _)
  rw [AdaptiveReplayProof.interact_rows_length] at hrows
  change (interact cfg sh g S (p.folded encode metadata) words dummy).2 =
    rowsOf (transcript cfg sh g S (p.folded encode metadata) (slotCount p.shape) words dummy)
      (slotCount p.shape) at hrows
  rw [← hrows]
  exact ho

/-- The local simulation takes the place of a whole-run observation-agreement
premise in the adaptive bound. -/
theorem NativeAdapterOblivious31 : NativeAdapterOblivious31_statement := by
  intro h hh U g m Public View State _ p encode metadata S n hset Ω _ μ _ tape dtape words ht
    M hM henc hlocal A hA
  apply AdaptiveOblivious31 h hh U g m (p.folded encode metadata) S n hset μ tape dtape words ht
    (fun ω => (M ω).observation p) (transcriptEncoding encode metadata) hM henc ?_ A hA
  intro ω hs
  obtain ⟨R, hR⟩ := hlocal ω hs
  have hc := (NativeAdapterAgreement _ _ g S m Public View State p encode metadata (M ω)
    (words ω) (dummyOf (dtape ω)) R hR).2
  have hn : n = slotCount p.shape := hset.1
  subst n
  exact hc

/-- The common public encoding transports the adaptive two-client comparison. -/
theorem NativeAdapterTwoClients31 : NativeAdapterTwoClients31_statement := by
  intro h hh U U' g m Public View State State' _ p p' encode metadata S n hshape hset hset'
    Ω Ω' _ _ μ μ' _ _ tape dtape words tape' dtape' words' ht ht' M M' hM hM' henc
    hlocal hlocal' A hA
  apply AdaptiveTwoClients31 h hh U U' g m (p.folded encode metadata) (p'.folded encode metadata)
    S n hshape hset hset' μ μ' tape dtape words tape' dtape' words' ht ht'
    (fun ω => (M ω).observation p) (fun ω => (M' ω).observation p')
    (transcriptEncoding encode metadata) hM hM' henc ?_ ?_ A hA
  · intro ω hs
    obtain ⟨R, hR⟩ := hlocal ω hs
    have hc := (NativeAdapterAgreement _ _ g S m Public View State p encode metadata (M ω)
      (words ω) (dummyOf (dtape ω)) R hR).2
    have hn : n = slotCount p.shape := hset.1
    subst n
    exact hc
  · intro ω hs
    obtain ⟨R, hR⟩ := hlocal' ω hs
    have hc := (NativeAdapterAgreement _ _ g S m Public View State' p' encode metadata (M' ω)
      (words' ω) (dummyOf (dtape' ω)) R hR).2
    have hn : n = slotCount p'.shape := hset'.1
    subst n
    exact hc

end RebuildBound
