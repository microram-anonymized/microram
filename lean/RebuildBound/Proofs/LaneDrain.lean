import Mathlib.Data.List.Basic

/-! Generic lane filtering and observed append-fold laws. These logical helpers
assume the supplied update laws; they claim no native implementation correspondence. -/
namespace RebuildBound.LaneDrain

theorem filterMap_map_filter {α : Type*} (p : α → Bool) (B : List (Option α)) :
    (B.map fun s => s.filter p).filterMap id = (B.filterMap id).filter p := by
  simp only [List.filterMap_map, List.filter_filterMap, Function.comp_def, id]


/-- A fold that preserves records up to permutation. -/
theorem fold_records {σ α : Type*} (records : σ → List α)
    (step : σ → List α → σ)
    (law : ∀ s L, (records (step s L)).Perm (records s ++ L)) :
    ∀ (chunks : List (List α)) (s : σ),
      (records (chunks.foldl step s)).Perm (records s ++ chunks.flatten)
  | [], s => by simp
  | L :: chunks, s => by
    rw [List.foldl_cons]
    refine (fold_records records step law chunks _).trans ?_
    rw [List.flatten_cons, ← List.append_assoc]
    exact (law s L).append_right _

/-- Trace equality follows from equal chunk lengths and observed state.
The update law remains an explicit premise. -/
theorem fold_trace {σ α β τ : Type*} (measure : σ → Nat) (trace : σ → τ)
    (step₁ : σ → List α → σ) (step₂ : σ → List β → σ)
    (law : ∀ s₁ s₂ L₁ L₂, L₁.length = L₂.length → measure s₁ = measure s₂ →
      trace s₁ = trace s₂ →
      measure (step₁ s₁ L₁) = measure (step₂ s₂ L₂) ∧
      trace (step₁ s₁ L₁) = trace (step₂ s₂ L₂)) :
    ∀ (chunks₁ : List (List α)) (chunks₂ : List (List β)) (s₁ s₂ : σ),
      chunks₁.map List.length = chunks₂.map List.length → measure s₁ = measure s₂ →
      trace s₁ = trace s₂ → trace (chunks₁.foldl step₁ s₁) = trace (chunks₂.foldl step₂ s₂)
  | [], [], _, _, _, _, ht => ht
  | [], _ :: _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | L₁ :: chunks₁, L₂ :: chunks₂, s₁, s₂, hl, hm, ht => by
    simp only [List.map_cons, List.cons.injEq] at hl
    obtain ⟨hm', ht'⟩ := law s₁ s₂ L₁ L₂ hl.1 hm ht
    exact fold_trace measure trace step₁ step₂ law chunks₁ chunks₂ _ _ hl.2 hm' ht'

end RebuildBound.LaneDrain
