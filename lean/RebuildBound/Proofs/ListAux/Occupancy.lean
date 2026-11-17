import RebuildBound.Proofs.ListAux.Bucket

/-!
# D4b, the coordinated drain

The first drain appends A's leftovers and B's tier leftovers to a tier with no
free lane, so its trace quantities are prefix sums of their lengths. The last
append follows the leftover dedup. Both are bounded by counting distinct keys
shut out of full homes.
-/

namespace RebuildBound.D4b

open RebuildBound.Model

theorem occupied_append {α : Type} (A B : List (Option α)) :
    occupied (A ++ B) = occupied A + occupied B := List.countP_append

theorem occupied_map_some {α : Type} (L : List α) : occupied (L.map some) = L.length := by
  unfold occupied; rw [List.countP_map]; simp

theorem free_map_some {α : Type} (L : List α) : (L.map some).countP (·.isNone) = 0 := by
  rw [List.countP_map]; simp

theorem occupied_appendFill {α : Type} (B : List (Option α)) (L : List α) :
    occupied (appendFill B L) = occupied B + L.length := by
  unfold appendFill
  rw [occupied_append, occupied_map_some]
  unfold occupied
  rw [fill_some, fill_snd, List.length_drop]
  have := Nat.min_le_left L.length (B.countP (·.isNone))
  omega

theorem appendFill_full {α : Type} (T : List (Option α)) (h : T.countP (·.isNone) = 0)
    (L : List α) : appendFill T L = T ++ L.map some := by
  unfold appendFill; rw [fill_of_full T L h]

theorem drainStep_snd (acc : List (Option (Rec × Bool)) × List (Test × Nat)) (L : List (Rec × Bool)) :
    (drainStep acc L).2 = acc.2 ++ [(.drain, occupied acc.1 + L.length)] := by
  unfold drainStep; simp only; rw [occupied_appendFill]

theorem drain_fold : ∀ (Ls : List (List (Rec × Bool))) (T : List (Option (Rec × Bool)))
    (tr : List (Test × Nat)), T.countP (·.isNone) = 0 →
    (Ls.foldl drainStep (T, tr)).1 = T ++ Ls.flatten.map some ∧
    ∀ e ∈ (Ls.foldl drainStep (T, tr)).2,
      e ∈ tr ∨ (e.1 = .drain ∧ e.2 ≤ occupied T + Ls.flatten.length)
  | [], T, tr, _ => ⟨by simp, fun e he => Or.inl he⟩
  | L :: Ls, T, tr, h => by
    simp only [List.foldl_cons]
    have hd : drainStep (T, tr) L =
        (T ++ L.map some, tr ++ [(.drain, occupied T + L.length)]) := by
      unfold drainStep; simp only; rw [appendFill_full T h, occupied_append, occupied_map_some]
    rw [hd]
    have h' : (T ++ L.map some).countP (·.isNone) = 0 := by
      rw [List.countP_append, h, free_map_some]
    obtain ⟨ih1, ih2⟩ := drain_fold Ls _ (tr ++ [(.drain, occupied T + L.length)]) h'
    refine ⟨by rw [ih1]; simp, ?_⟩
    intro e he
    rcases ih2 e he with he | he
    · rcases List.mem_append.1 he with he | he
      · exact Or.inl he
      · right
        rw [List.mem_singleton] at he
        subst he
        simp
    · right
      refine ⟨he.1, ?_⟩
      rw [occupied_append, occupied_map_some] at he
      simp only [List.flatten_cons, List.length_append]
      omega

/-- The first drain's lists. -/
def firstL (st : FinState) : List (List (Rec × Bool)) :=
  (st.leaves.map fun L => L.map fun r => (r, true)) ++ [st.bcopy.map fun r => (r, false)]

/-- The leftover dedup's lane test. -/
def dq (st : FinState) : Rec × Bool → Bool :=
  fun p => !(p.2 && (st.ins.map Rec.key).contains p.1.key)

theorem drain_snd_eq (st : FinState) : ∃ p : Rec → Bool,
    (drain st).2 = ((firstL st).foldl drainStep ([], [])).2 ++
      [(.drain, occupied (((firstL st).foldl drainStep ([], [])).1.map fun s => s.filter (dq st)) +
        (st.ins.filter p).length)] := by
  refine ⟨fun r => !(((((((firstL st).foldl drainStep ([], [])).1.map fun s => s.filter (dq st)).filterMap
    id).filter fun p => !p.2).map fun p => p.1.key).contains r.key), ?_⟩
  have : (drain st).2 = (drainStep ((((firstL st).foldl drainStep ([], [])).1.map fun s => s.filter (dq st)),
      ((firstL st).foldl drainStep ([], [])).2) ((st.ins.filter fun r => !(((((((firstL st).foldl
      drainStep ([], [])).1.map fun s => s.filter (dq st)).filterMap id).filter fun p => !p.2).map
      fun p => p.1.key).contains r.key)).map fun r => (r, false))).2 := rfl
  rw [this, drainStep_snd, List.length_map]

theorem occupied_map_filter {α : Type} (q : α → Bool) (L : List α) :
    occupied ((L.map some).map fun s => s.filter q) = L.countP q := by
  simp only [occupied, List.countP_map, Function.comp_def]
  congr 1
  funext a
  by_cases h : q a <;> simp [Option.filter, h]

theorem firstL_flatten (st : FinState) : (firstL st).flatten =
    st.leaves.flatten.map (fun r => (r, true)) ++ st.bcopy.map fun r => (r, false) := by
  unfold firstL
  rw [List.flatten_append]
  simp [List.map_flatten]

/-- Every drain-trace quantity is at most `E`, given the two counting bounds. -/
theorem drain_bound (st : FinState) (E : Nat)
    (hA : st.leaves.flatten.length + st.bcopy.length ≤ E)
    (hB : ∀ p : Rec → Bool, (st.leaves.flatten.filter fun r => !(st.ins.map Rec.key).contains r.key).length +
      st.bcopy.length + (st.ins.filter p).length ≤ E) :
    ∀ e ∈ (drain st).2, e.1 = .drain ∧ e.2 ≤ E := by
  obtain ⟨p, hp⟩ := drain_snd_eq st
  obtain ⟨h1, h2⟩ := drain_fold (firstL st) [] [] rfl
  intro e he
  rw [hp] at he
  rcases List.mem_append.1 he with he | he
  · rcases h2 e he with he | he
    · simp at he
    · refine ⟨he.1, ?_⟩
      have := he.2
      rw [firstL_flatten] at this
      simp only [List.length_append, List.length_map] at this
      simp only [occupied, List.countP_nil] at this
      omega
  · rw [List.mem_singleton] at he
    subst he
    refine ⟨rfl, ?_⟩
    show occupied _ + _ ≤ E
    rw [h1, List.nil_append, occupied_map_filter, firstL_flatten, List.countP_append,
      List.countP_map, List.countP_map]
    have e1 : ((st.leaves.flatten).countP ((dq st) ∘ fun r => (r, true))) =
        (st.leaves.flatten.filter fun r => !(st.ins.map Rec.key).contains r.key).length := by
      rw [List.countP_eq_length_filter]; rfl
    have e2 : (st.bcopy.countP ((dq st) ∘ fun r => (r, false))) = st.bcopy.length := by
      rw [List.countP_eq_length]; intro a _; simp [dq]
    rw [e1, e2]
    exact hB p

end RebuildBound.D4b
