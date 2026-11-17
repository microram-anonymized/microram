import RebuildBound.Proofs.S12.Basic

/-!
# S12: generic list lemmas

`flatMap` over `List.range`, folds of `List.set` at distinct indices, and
key filters.
-/

namespace RebuildBound.S12

open RebuildBound.Model RebuildBound.D23

/-! ### `flatMap` over `List.range` -/

theorem flatMap_eq_range {α β : Type} (f : α → List β) (d : α) :
    ∀ X : List α, X.flatMap f = (List.range X.length).flatMap (fun i => f (X.getD i d))
  | [] => rfl
  | a :: X => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_cons,
      List.flatMap_map, flatMap_eq_range f d X]
    rfl

theorem range_flatMap_append (f g : Nat → List Rec) : ∀ R : Nat,
    List.Perm ((List.range R).flatMap f ++ (List.range R).flatMap g)
      ((List.range R).flatMap (fun i => f i ++ g i)) :=
  fun R => List.flatMap_append_perm (List.range R) f g

theorem range_flatMap_ite (F : List Rec) {c : Nat} : ∀ R : Nat,
    (List.range R).flatMap (fun a => if a = c then F else []) = if c < R then F else []
  | 0 => by simp
  | R + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, range_flatMap_ite F R]
    by_cases hc : c = R
    · subst hc; simp
    · by_cases hlt : c < R
      · simp [hlt, show c < R + 1 by omega, Ne.symm hc]
      · simp [hlt, show ¬ c < R + 1 by omega, Ne.symm hc]

theorem range_flatMap_single (f : Nat → List Rec) {c : Nat} : ∀ R : Nat, c < R →
    List.Perm ((List.range R).flatMap f)
      (f c ++ (List.range R).flatMap (fun i => if i = c then [] else f i)) := by
  intro R h
  have hp := range_flatMap_append (fun i => if i = c then f c else [])
    (fun i => if i = c then [] else f i) R
  rw [range_flatMap_ite, ite_eq_left h] at hp
  convert hp.symm using 1
  apply List.flatMap_congr
  intro i _
  by_cases hi : i = c <;> simp [hi]

/-! ### Folds of `List.set` -/

/-- Set the entries `zs` (index, value), in order. -/
def setAll {α : Type} (m : List α) (zs : List (Nat × α)) : List α :=
  zs.foldl (fun m q => m.set q.1 q.2) m

theorem setAll_cons {α : Type} (m : List α) (q : Nat × α) (zs : List (Nat × α)) :
    setAll m (q :: zs) = setAll (m.set q.1 q.2) zs := rfl

theorem setAll_length {α : Type} : ∀ (m : List α) (zs : List (Nat × α)),
    (setAll m zs).length = m.length
  | _, [] => rfl
  | m, q :: zs => by rw [setAll_cons, setAll_length, List.length_set]

theorem setAll_getD_not {α : Type} (d : α) : ∀ (m : List α) (zs : List (Nat × α)) (v : Nat),
    v ∉ zs.map Prod.fst → (setAll m zs).getD v d = m.getD v d
  | _, [], _, _ => rfl
  | m, q :: zs, v, h => by
    rw [setAll_cons, setAll_getD_not d _ zs v (fun h' => h (List.mem_cons_of_mem _ h'))]
    exact D6.getD_set_ne _ _ _ (fun e => h (e ▸ List.mem_cons_self ..))

theorem setAll_getD_mem {α : Type} (d : α) : ∀ (m : List α) (zs : List (Nat × α)) (q : Nat × α),
    (zs.map Prod.fst).Nodup → q ∈ zs → q.1 < m.length → (setAll m zs).getD q.1 d = q.2
  | _, [], _, _, h, _ => absurd h List.not_mem_nil
  | m, q' :: zs, q, hnd, hq, hlt => by
    rw [setAll_cons]
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hq with rfl | hq
    · rw [setAll_getD_not d _ zs _ hnd.1, getD_set_self _ _ _ _ hlt]
    · exact setAll_getD_mem d _ zs q hnd.2 hq (by rw [List.length_set]; exact hlt)

theorem setAll_mem {α : Type} (P : α → Prop) : ∀ (m : List α) (zs : List (Nat × α)),
    (∀ B ∈ m, P B) → (∀ q ∈ zs, P q.2) → ∀ B ∈ setAll m zs, P B
  | _, [], hm, _ => hm
  | m, q :: zs, hm, hz => by
    rw [setAll_cons]
    apply setAll_mem P _ zs _ (fun q' h => hz q' (List.mem_cons_of_mem _ h))
    intro B hB
    rcases List.mem_or_eq_of_mem_set hB with hB | rfl
    · exact hm B hB
    · exact hz q (List.mem_cons_self ..)

theorem setAll_perm : ∀ (m : List Bucket) (zs : List (Nat × Bucket)),
    (zs.map Prod.fst).Nodup → (∀ q ∈ zs, q.1 < m.length) →
    List.Perm ((setAll m zs).flatMap Bucket.recs ++
        (zs.map fun q => m.getD q.1 []).flatMap Bucket.recs)
      (m.flatMap Bucket.recs ++ (zs.map Prod.snd).flatMap Bucket.recs)
  | m, [], _, _ => by simp [setAll]
  | m, q :: zs, hnd, hlt => by
    rw [setAll_cons]
    rw [List.map_cons, List.nodup_cons] at hnd
    have ih := setAll_perm (m.set q.1 q.2) zs hnd.2 (fun q' h => by
      rw [List.length_set]; exact hlt q' (List.mem_cons_of_mem _ h))
    have e : (zs.map fun q' => (m.set q.1 q.2).getD q'.1 []) = zs.map fun q' => m.getD q'.1 [] := by
      apply List.map_congr_left
      intro q' hq'
      apply D6.getD_set_ne
      intro e; exact hnd.1 (e ▸ List.mem_map_of_mem hq')
    rw [e] at ih
    have hs := perm_flatMap_set Bucket.recs m q.1 q.2 [] (hlt q (List.mem_cons_self ..))
    rw [List.perm_iff_count]; intro x
    have c1 := ih.count_eq x
    have c2 := hs.count_eq x
    simp only [List.map_cons, List.flatMap_cons, List.count_append] at c1 c2 ⊢
    omega

/-! ### Key filters -/

theorem filter_not_keys_nil (L : List Rec) : L.filter (fun x => !([] : List Model.LogicalKey).contains x.key) = L := by
  rw [List.filter_eq_self]; intro x _; simp

theorem filter_not_keys_append (L X Y : List Rec) :
    (L.filter fun x => !(X.map Rec.key).contains x.key).filter
        (fun x => !(Y.map Rec.key).contains x.key) =
      L.filter fun x => !((X ++ Y).map Rec.key).contains x.key := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  rw [keys_contains_append]
  cases (X.map Rec.key).contains x.key <;> cases (Y.map Rec.key).contains x.key <;> rfl

theorem keys_contains_iff (L : List Rec) (k : Model.LogicalKey) : (L.map Rec.key).contains k = true ↔ k ∈ L.map Rec.key := by
  simp

end RebuildBound.S12
