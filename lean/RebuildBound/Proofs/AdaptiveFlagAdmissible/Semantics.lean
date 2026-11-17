import RebuildBound.Spec.AdaptiveSteps

/-! Admissibility from the flag rule, requester trace and replay shape.
This deterministic step uses no numerical capacity bound. -/

namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Model.Adaptive

theorem AdaptiveFlagAdmissibleStep : AdaptiveFlagAdmissibleStep_statement := by
  intro hFS hRT hRS h hh U g m a S hU hcard hg hE hhor hnodup hinit hkeys hS hflag
  refine ⟨rfl, fun t => ?_⟩
  obtain ⟨_, _, hlen, hinit', _, hrec⟩ := hRS m a (slotCount a.shape) t
  have hslotkeys : ∀ s ∈ OnlineBatch.slots (replay a t), s.record.key ∈ U := by
    intro s hs
    obtain ⟨rows, i, hr⟩ := hrec s hs
    rw [hr]; exact hkeys rows i
  have htrace := hRT (geometry31.chunk h).cfg U g (replay a t) hg hE hslotkeys
    (by rw [hinit']; exact hnodup) (by rw [hinit']; exact hinit)
  refine ⟨hU, hcard, hlen.ge, ⟨⟨hg, hE⟩, by rw [hlen]; exact hhor, hslotkeys, htrace, ?_⟩, hS⟩
  exact hFS h hh U g (replay a t) S m (fun _ _ _ => 0) hU hcard hg hE (by rw [hlen]; exact hhor)
    htrace (by rw [hlen]; exact hS) (hflag t)

end RebuildBound
