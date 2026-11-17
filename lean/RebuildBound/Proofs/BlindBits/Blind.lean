import RebuildBound.Proofs.BlindBits.Route

/-!
# BlindBits: key sets and word restrictions (from G2.Blind)

`keysOf`, `wOf` and their counting facts. Moved from the binary d = 2
chain (`G2.Blind`); namespace `RebuildBound.G2` kept.
-/

namespace RebuildBound.G2
open RebuildBound.Model RebuildBound.Spec
section Keys
variable {KA : Finset Model.LogicalKey}
/-- The keys of a list of records, as a subset of `KA`. -/
def keysOf (KA : Finset Model.LogicalKey) (l : List Rec) : Finset {x // x ∈ KA} :=
  Finset.univ.filter (fun x => x.val ∈ l.map Rec.key)

theorem mem_keysOf {l : List Rec} {x : {x // x ∈ KA}} :
    x ∈ keysOf KA l ↔ x.val ∈ l.map Rec.key := by
  simp [keysOf]

theorem card_filter_keysOf (l : List Rec) (hnd : (l.map Rec.key).Nodup)
    (hK : ∀ r ∈ l, r.key ∈ KA) (P : {x // x ∈ KA} → Prop) [DecidablePred P] (q : Rec → Bool)
    (hPq : ∀ r (hr : r ∈ l), P ⟨r.key, hK r hr⟩ ↔ q r = true) :
    ((keysOf KA l).filter P).card = l.countP q := by
  induction l with
  | nil => simp [keysOf]
  | cons r l ih =>
    have hr : r.key ∈ KA := hK r List.mem_cons_self
    have hnd' : r.key ∉ l.map Rec.key ∧ (l.map Rec.key).Nodup :=
      List.nodup_cons.1 (by rw [List.map_cons] at hnd; exact hnd)
    have hins : keysOf KA (r :: l) = insert ⟨r.key, hr⟩ (keysOf KA l) := by
      ext x; simp [keysOf, Subtype.ext_iff]
    have hnotin : (⟨r.key, hr⟩ : {x // x ∈ KA}) ∉ keysOf KA l := by
      rw [mem_keysOf]; exact hnd'.1
    have ih' := ih hnd'.2 (fun r' h => hK r' (List.mem_cons_of_mem _ h))
      (fun r' h => hPq r' (List.mem_cons_of_mem _ h))
    rw [hins, Finset.filter_insert, List.countP_cons]
    by_cases hp : P ⟨r.key, hr⟩
    · have hq := (hPq r List.mem_cons_self).1 hp
      simp only [hp, hq, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (fun h => hnotin (Finset.mem_filter.1 h).1), ih']
    · have hq : ¬ q r = true := fun h => hp ((hPq r List.mem_cons_self).2 h)
      simp only [hp, hq, ↓reduceIte]
      rw [ih']; rfl

theorem perm_of_add {l1 l2 l3 : List Rec} (h : (l1 : Multiset Rec) = l2 + l3) :
    l1.Perm (l2 ++ l3) := by
  rw [Multiset.coe_add] at h; exact Multiset.coe_eq_coe.1 h

theorem nodup_of_add {l1 l2 l3 : List Rec} (h : (l1 : Multiset Rec) = l2 + l3)
    (hnd : (l1.map Rec.key).Nodup) : ((l2 ++ l3).map Rec.key).Nodup :=
  ((perm_of_add h).map Rec.key).nodup_iff.1 hnd

theorem mem_of_add {l1 l2 l3 : List Rec} (h : (l1 : Multiset Rec) = l2 + l3) {r : Rec} :
    r ∈ l1 ↔ r ∈ l2 ∨ r ∈ l3 := by
  rw [(perm_of_add h).mem_iff, List.mem_append]

theorem keysOf_sdiff {l1 l2 l3 : List Rec} (h : (l1 : Multiset Rec) = l2 + l3)
    (hnd : ((l2 ++ l3).map Rec.key).Nodup) :
    keysOf KA l1 \ keysOf KA l2 = keysOf KA l3 := by
  have hp := ((perm_of_add h).map Rec.key)
  rw [List.map_append] at hp hnd
  have hdisj := (List.nodup_append.1 hnd).2.2
  ext x
  simp only [Finset.mem_sdiff, mem_keysOf, hp.mem_iff, List.mem_append]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd h1 h2
    · exact h1
  · intro h1
    exact ⟨Or.inr h1, fun h2 => hdisj _ h2 _ h1 rfl⟩

theorem keysOf_subset {l1 l2 l3 : List Rec} (h : (l1 : Multiset Rec) = l2 + l3) :
    keysOf KA l2 ⊆ keysOf KA l1 := by
  intro x hx
  rw [mem_keysOf] at hx ⊢
  rw [((perm_of_add h).map Rec.key).mem_iff, List.map_append]
  exact List.mem_append_left _ hx

theorem keysOf_disjoint {l2 l3 : List Rec} (hnd : ((l2 ++ l3).map Rec.key).Nodup) :
    Disjoint (keysOf KA l2) (keysOf KA l3) := by
  rw [List.map_append] at hnd
  have hdisj := (List.nodup_append.1 hnd).2.2
  rw [Finset.disjoint_left]
  intro x h2 h3
  rw [mem_keysOf] at h2 h3
  exact hdisj _ h2 _ h3 rfl

theorem keysOf_card_le (l : List Rec) : (keysOf KA l).card ≤ l.length := by
  calc (keysOf KA l).card ≤ (l.map Rec.key).toFinset.card := by
        apply Finset.card_le_card_of_injOn Subtype.val
        · intro x hx
          simp only [Finset.mem_coe, List.mem_toFinset]
          exact mem_keysOf.1 hx
        · intro x _ y _ h; exact Subtype.ext h
    _ ≤ (l.map Rec.key).length := List.toFinset_card_le _
    _ = l.length := List.length_map _

end Keys
section Words
variable (KA : Finset Model.LogicalKey) (b : ℕ)
/-- The word function of a word assignment on `KA` (zero off `KA`). -/
noncomputable def wOf (h : {x // x ∈ KA} → Bits b) : Model.LogicalKey → ℕ :=
  fun x => if hx : x ∈ KA then (bitsEquiv b (h ⟨x, hx⟩) : ℕ) else 0

variable {KA b}
theorem wOf_mem (h : {x // x ∈ KA} → Bits b) (x : {x // x ∈ KA}) :
    wOf KA b h x.val = bitsEquiv b (h x) := by
  simp [wOf, x.prop]

theorem natToBits_wOf (h : {x // x ∈ KA} → Bits b) (x : {x // x ∈ KA}) :
    natToBits b (wOf KA b h x.val) = h x := by
  rw [wOf_mem, natToBits_bitsEquiv]

theorem testBit_wOf (h : {x // x ∈ KA} → Bits b) (x : {x // x ∈ KA}) (i : Fin b) :
    (wOf KA b h x.val).testBit i = h x i := by
  rw [wOf_mem, testBit_bitsEquiv]

end Words
end RebuildBound.G2
