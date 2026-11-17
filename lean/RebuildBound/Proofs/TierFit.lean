import RebuildBound.Spec.Hierarchy

/-!
# TierFit: a publication's tier fits its capacity

The last drain entry of each model records the occupancy of the final tier
(before the field projection, and for the top finish before the tombstone
filter, neither of which raises it). A job that publishes has no failing
trace entry, so that entry is within the drain's capacity.
-/

namespace RebuildBound.TierFitProof

open RebuildBound.Model

/-- Projecting the slots does not change the occupancy. -/
theorem occupied_map_map {α β : Type} (f : α → β) (B : List (Option α)) :
    occupied (B.map fun s => s.map f) = occupied B := by
  unfold occupied
  rw [List.countP_map]
  congr 1
  funext s
  cases s <;> rfl

/-- Filtering the slots does not raise the occupancy. -/
theorem occupied_map_filter_le {α : Type} (p : α → Bool) (B : List (Option α)) :
    occupied (B.map fun s => s.filter p) ≤ occupied B := by
  unfold occupied
  rw [List.countP_map]
  apply List.countP_mono_left
  intro s _ h
  cases s with
  | none => simp [Option.filter] at h
  | some a => rfl

theorem recs_length (B : Bucket) : (Bucket.recs B).length = occupied B := by
  unfold Bucket.recs occupied
  exact List.length_filterMap_eq_countP

/-- No entry of a trace without a first failure exceeds its capacity. -/
theorem le_of_find_none {τ : Type} (p : τ × Nat → Bool) (trace : List (τ × Nat))
    (h : (trace.find? p).map Prod.fst = none) (x : τ × Nat) (hx : x ∈ trace) : p x = false := by
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  simpa using h x hx

end RebuildBound.TierFitProof

open RebuildBound.Model RebuildBound.TierFitProof

theorem RebuildBound.SepTierFit : RebuildBound.Spec.SepTierFit_statement := by
  intro g w inp out h
  unfold sJob sJobWith at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i hf
    injection h with h
    subst h
    unfold sFirstFailure at hf
    have key := le_of_find_none _ _ hf
    simp only [sReferenceWith, sDrain, sDrainStep] at key ⊢
    rw [recs_length, occupied_map_map]
    have := key _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)))
    simpa [SepGeom.capOf] using this

theorem RebuildBound.TopTierFit : RebuildBound.Spec.TopTierFit_statement := by
  intro g unsh w inp out h
  unfold topJob at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i hf
    injection h with h
    subst h
    unfold firstFailure at hf
    have key := le_of_find_none _ _ hf
    simp only [topReference, drain, drainStep] at key ⊢
    rw [recs_length]
    refine le_trans (occupied_map_filter_le _ _) ?_
    rw [occupied_map_map]
    have := key _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)))
    simpa [Caps.capOf, TopGeom.caps, exceeds] using this

theorem RebuildBound.TPTierFit : RebuildBound.Spec.TPTierFit_statement := by
  intro g unsh w inp out h
  unfold tpJob tpJobWith at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i hf
    injection h with h
    subst h
    unfold tpFirstFailure at hf
    have key := le_of_find_none _ _ hf
    simp only [tpReferenceWith, tpDrain] at key ⊢
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at key ⊢
    simp only [tpDrainStep] at key ⊢
    rw [recs_length]
    have := key _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)))
    exact Nat.le_of_not_lt (of_decide_eq_false this)
