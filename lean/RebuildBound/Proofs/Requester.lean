import RebuildBound.Spec.Requester
import Mathlib.Tactic.SplitIfs

/-! Unit discipline of the online stash: uniqueness and shape are invariants of
`step`, lifted to `run` by fold induction. For a batch, the current unit's
records never share a key with a lane still to be inserted. -/
namespace RebuildBound
open Spec Model Model.Requester

namespace RequesterAux

theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β)
    (hf : ∀ s x, P s → P (f s x)) : ∀ (xs : List α) (s : β), P s → P (xs.foldl f s)
  | [], _, h => h
  | x :: xs, s, h => foldl_inv P f hf xs _ (hf s x h)

theorem recs_clearKey (k : LogicalKey) (u : Bucket) :
    (clearKey k u).recs = u.recs.filter (·.key != k) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    cases a with
    | none => simp_all [clearKey, Bucket.recs]
    | some v =>
      by_cases h : v.key = k <;> simp_all [clearKey, Bucket.recs, Option.filter]

theorem recs_append_single (u : Bucket) (l : Option Rec) :
    (u ++ [l]).recs = u.recs ++ l.toList := by
  cases l <;> simp [Bucket.recs, List.filterMap_append]

theorem keys_clearKey_nodup (k : LogicalKey) (u : Bucket) (h : (u.recs.map Rec.key).Nodup) :
    ((clearKey k u).recs.map Rec.key).Nodup := by
  rw [recs_clearKey]
  exact h.sublist ((List.filter_sublist).map _)

theorem foldl_clear_sub (L : List Rec) :
    ∀ u : Bucket, ((L.foldl (fun u r => clearKey r.key u) u).recs).Sublist u.recs := by
  induction L with
  | nil => intro u; exact List.Sublist.refl _
  | cons a t ih =>
    intro u
    exact (ih _).trans (by rw [recs_clearKey]; exact List.filter_sublist)

theorem foldl_clear_ne (L : List Rec) :
    ∀ u : Bucket, ∀ r ∈ (L.foldl (fun u r => clearKey r.key u) u).recs,
      ∀ y ∈ L, r.key ≠ y.key := by
  induction L with
  | nil => intro u r _ y hy; simp at hy
  | cons a t ih =>
    intro u r hr y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · have := (foldl_clear_sub t _).subset hr
      rw [recs_clearKey] at this
      have := (List.mem_filter.1 this).2
      simpa using this
    · exact ih _ r hr y hy

theorem insert_cur (e : Nat) (st : State) (l : Option Rec) :
    ∀ r ∈ (Requester.insert e st l).current.recs, r ∈ st.current.recs ∨ l = some r := by
  intro r hr
  unfold Requester.insert at hr
  split_ifs at hr
  · simp [Bucket.recs] at hr
  · simp only [recs_append_single] at hr
    rcases List.mem_append.1 hr with h | h
    · exact Or.inl h
    · cases l <;> simp_all

theorem insert_unique (e : Nat) (st : State) (l : Option Rec) (h : Unique st)
    (hl : ∀ r, l = some r → r.key ∉ st.current.recs.map Rec.key) :
    Unique (Requester.insert e st l) := by
  obtain ⟨h1, h2⟩ := h
  have key : ((st.current ++ [l]).recs.map Rec.key).Nodup := by
    rw [recs_append_single]
    cases l with
    | none => simpa using h2
    | some r =>
      simp only [List.map_append, Option.toList_some, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨h2, by simp, ?_⟩
      intro a ha b hb
      simp at hb; subst hb
      exact fun hk => hl r rfl (List.mem_map.2 ⟨_, List.mem_map.1 ha |>.choose_spec.1, by rw [(List.mem_map.1 ha).choose_spec.2, hk]⟩)
  unfold Requester.insert
  split_ifs
  · refine ⟨?_, by simp [Bucket.recs]⟩
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact h1 u hu
    · rw [List.mem_singleton.1 hu]; exact key
  · exact ⟨h1, key⟩

theorem insert_shape (e : Nat) (he : 0 < e) (st : State) (l : Option Rec)
    (h1 : ∀ u ∈ st.frozen, u.length = e) (h2 : st.current.length < e) :
    (∀ u ∈ (Requester.insert e st l).frozen, u.length = e) ∧ (Requester.insert e st l).current.length < e := by
  unfold Requester.insert
  split_ifs with h
  · refine ⟨?_, by simpa using he⟩
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact h1 u hu
    · rw [List.mem_singleton.1 hu]; simp at h ⊢; omega
  · exact ⟨h1, by simp at h ⊢; omega⟩

theorem foldl_batch (e : Nat) (lanes : List Rec) :
    ∀ (L pre : List Rec) (s : State), lanes = pre ++ L → Unique s →
      (∀ r ∈ s.current.recs, ∀ y ∈ L, r.key ≠ y.key) →
      Unique ((L.zipIdx pre.length).foldl
        (fun s ri => insert e s (if superseded lanes ri.2 ri.1 then none else some ri.1)) s) := by
  intro L
  induction L with
  | nil => intro pre s _ h _; simpa using h
  | cons a L ih =>
    intro pre s hl hu hne
    simp only [List.zipIdx_cons, List.foldl_cons]
    have hdrop : lanes.drop (pre.length + 1) = L := by
      subst hl; simp [List.drop_append]
    have hs : superseded lanes pre.length a = L.any (·.key == a.key) := by
      simp [superseded, hdrop]
    have key := fun (r : Rec) (hr : r ∈ s.current.recs) => hne r hr a (List.mem_cons_self ..)
    have hne' := fun r hr y hy => hne r hr y (List.mem_cons_of_mem _ hy)
    have := ih (pre ++ [a])
      (Requester.insert e s (if superseded lanes pre.length a then none else some a))
      (by simp [hl]) ?_ ?_
    · simpa using this
    · refine insert_unique e s _ hu ?_
      intro r hr
      split_ifs at hr
      have hr' : a = r := by simpa using hr
      subst hr'
      intro hm
      obtain ⟨r', hr', hk⟩ := List.mem_map.1 hm
      exact key r' hr' hk
    · intro r hr y hy
      rcases insert_cur e s _ r hr with h | h
      · exact hne' r h y hy
      · split_ifs at h with hsup
        have h' : a = r := by simpa using h
        subst h'
        rw [hs] at hsup
        simp at hsup
        exact fun hk => hsup y hy hk.symm

end RequesterAux
open RequesterAux

theorem RequesterUnique : Spec.RequesterUnique_statement := by
  intro e st ops
  unfold run
  refine foldl_inv _ _ ?_ ops st
  intro s op hs
  cases op with
  | access r real =>
    simp only [step]
    refine insert_unique _ _ _ ⟨hs.1, keys_clearKey_nodup _ _ hs.2⟩ ?_
    intro r' hr' hm
    split_ifs at hr'
    · obtain rfl : r = r' := by simpa using hr'
      obtain ⟨x, hx, hk⟩ := List.mem_map.1 hm
      rw [recs_clearKey] at hx
      simpa [hk] using (List.mem_filter.1 hx).2
  | batch lanes =>
    simp only [step]
    have := foldl_batch e lanes lanes [] ⟨s.frozen, lanes.foldl (fun u r => clearKey r.key u) s.current⟩
      (by simp) ⟨hs.1, ?_⟩ (foldl_clear_ne lanes _)
    · simpa using this
    · exact hs.2.sublist ((foldl_clear_sub lanes _).map _)

theorem RequesterShape : Spec.RequesterShape_statement := by
  intro e st ops he h1 h2
  unfold run
  have := foldl_inv (fun s : State => (∀ u ∈ s.frozen, u.length = e) ∧ s.current.length < e)
    (step e) ?_ ops st ⟨h1, h2⟩
  · exact this
  intro s op hs
  cases op with
  | access r real =>
    simp only [step]
    exact insert_shape e he _ _ hs.1 (by simpa [clearKey] using hs.2)
  | batch lanes =>
    simp only [step]
    refine foldl_inv (fun s : State => (∀ u ∈ s.frozen, u.length = e) ∧ s.current.length < e) _ ?_ _ _ ?_
    · intro s' x hs'
      exact insert_shape e he _ _ hs'.1 hs'.2
    · refine ⟨hs.1, ?_⟩
      have : ∀ (L : List Rec) (u : Bucket), (L.foldl (fun u r => clearKey r.key u) u).length = u.length := by
        intro L; induction L with
        | nil => intro u; rfl
        | cons a t ih => intro u; rw [List.foldl_cons, ih]; simp [clearKey]
      simpa [this] using hs.2

end RebuildBound
