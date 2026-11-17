import RebuildBound.Spec.Hierarchy
import RebuildBound.Proofs.DirectPrefix

/-!
# HierarchyInvariant: generic lemmas

Digit and home arithmetic, the forwarded family of a carry, the winners of
two record lists (as lists, key sets and record sets), cardinality from
distinct keys below `N`, and exact conservation across B's tier pages.
-/

namespace RebuildBound.HierarchyInvariantProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Spec

/-! ### Homes -/

theorem val2_one : val2 1 = 0 := by decide

theorem digitHome_one (K t : Nat) : digitHome K 1 t = t % 2 ^ K := by
  simp [digitHome, val2_one, Nat.mod_one]

/-- At a power-of-two digit `b = 2^(val2 b)` the home is the low bits. -/
theorem digitHome_pow (K b t : Nat) (hb : 2 ^ val2 b = b) :
    digitHome K b t = t % (2 ^ K * b) := by
  have h1 : b / 2 ^ val2 b = 1 := by
    rw [hb]; exact Nat.div_self (by rw [← hb]; exact Nat.two_pow_pos _)
  unfold digitHome
  simp only [h1, Nat.mod_one, Nat.mul_zero, Nat.add_zero]
  rw [Nat.pow_add, hb]

theorem homeOf_eq (g : SepGeom) (he : val2 g.d = g.e) (t : Nat) :
    g.homeOf t = digitHome g.K g.d t := by
  have hr : g.d / 2 ^ g.e = g.r := by
    unfold SepGeom.d; exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)
  unfold SepGeom.homeOf SepGeom.cls digitHome
  rw [he]
  dsimp only
  rw [hr]
  rfl

theorem pow_inj {K K' : Nat} (h : 2 ^ K = 2 ^ K') : K = K' :=
  Nat.pow_right_injective (le_refl 2) h

/-! ### Digits -/

theorem digit_pos (b o : Nat) : 1 ≤ Config.digitOf b o := by
  unfold Config.digitOf; omega

theorem digit_le {b : Nat} (hb : 0 < b) (o : Nat) : Config.digitOf b o ≤ b := by
  unfold Config.digitOf
  have := Nat.mod_lt (o - 1) hb
  omega

theorem digit_mul {b v : Nat} (hb : 0 < b) (hv : 0 < v) : Config.digitOf b (v * b) = b := by
  unfold Config.digitOf
  obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
  have e : (u + 1) * b - 1 = (b - 1) + b * u := by
    rw [Nat.succ_mul, Nat.mul_comm]; omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

theorem digit_pred {b v : Nat} (hb : 0 < b) (hd : 2 ≤ Config.digitOf b v) :
    Config.digitOf b (v - 1) = Config.digitOf b v - 1 := by
  unfold Config.digitOf at *
  have hm : 1 ≤ (v - 1) % b := by omega
  have hv : 1 ≤ v - 1 := by
    rcases Nat.eq_zero_or_pos (v - 1) with h | h
    · rw [h, Nat.zero_mod] at hm; omega
    · exact h
  have e := Nat.mod_add_div (v - 1) b
  have e2 : v - 1 - 1 = ((v - 1) % b - 1) + b * ((v - 1) / b) := by omega
  rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by have := Nat.mod_lt (v - 1) hb; omega)]
  omega

theorem digit_succ_dvd {b s : Nat} (hs : b ∣ s) : Config.digitOf b (s + 1) = 1 := by
  unfold Config.digitOf
  simp [Nat.mod_eq_zero_of_dvd hs]

theorem pred_gt {b s v : Nat} (hs : b ∣ s) (hv : s < v) (hd : 2 ≤ Config.digitOf b v) :
    s < v - 1 := by
  rcases Nat.lt_or_ge s (v - 1) with h | h
  · exact h
  · have : v = s + 1 := by omega
    rw [this, digit_succ_dvd hs] at hd
    omega

/-! ### Families -/

theorem familyOfAux_stable (cfg : Config) :
    ∀ (n m ℓ v : Nat), cfg.levels ≤ ℓ + n → cfg.levels ≤ ℓ + m →
      familyOfAux cfg n ℓ v = familyOfAux cfg m ℓ v
  | 0, 0, _, _, _, _ => rfl
  | 0, m + 1, ℓ, v, h, _ => by
    simp only [familyOfAux]
    rw [if_neg (by omega)]
  | n + 1, 0, ℓ, v, _, h => by
    simp only [familyOfAux]
    rw [if_neg (by omega)]
  | n + 1, m + 1, ℓ, v, h, h' => by
    simp only [familyOfAux]
    split_ifs
    · exact familyOfAux_stable cfg n m (ℓ + 1) _ (by omega) (by omega)
    · rfl

/-- The carry consumed by `(ℓ, v)` is routed under the family of `(ℓ, v)`. -/
theorem jobWord_carry (cfg : Config) (words : Words) {ℓ : Nat} (v : Nat) (h2 : 2 ≤ ℓ)
    (hL : ℓ ≤ cfg.levels) (hb : 0 < cfg.fanout (ℓ - 1)) :
    jobWord cfg words (ℓ - 1) (v * cfg.fanout (ℓ - 1)) = jobWord cfg words ℓ v := by
  have e : familyOf cfg (ℓ - 1) (v * cfg.fanout (ℓ - 1)) = familyOf cfg ℓ v := by
    unfold familyOf
    obtain ⟨L, hL'⟩ : ∃ L, cfg.levels = L + 1 := ⟨cfg.levels - 1, by omega⟩
    rw [hL']
    simp only [familyOfAux]
    rw [if_pos ⟨by omega, Nat.mul_mod_left _ _⟩, Nat.mul_div_cancel _ hb,
      show ℓ - 1 + 1 = ℓ by omega]
    exact familyOfAux_stable cfg L (L + 1) ℓ v (by omega) (by omega)
  unfold jobWord
  rw [e]

/-! ### Winners of two record lists -/

/-- B, then A's records whose key B lacks. -/
def win (A B : List Rec) : List Rec := B ++ A.filter fun x => !(B.map Rec.key).contains x.key

/-- The record set of `win`. -/
def winSet (A B : Finset Rec) : Finset Rec := B ∪ A.filter fun x => x.key ∉ B.image Rec.key

theorem mem_win {A B : List Rec} {x : Rec} (h : x ∈ win A B) : x ∈ A ∨ x ∈ B := by
  rcases List.mem_append.1 h with h | h
  · exact Or.inr h
  · exact Or.inl (List.mem_of_mem_filter h)

theorem win_nodup {A B : List Rec} (hA : (A.map Rec.key).Nodup) (hB : (B.map Rec.key).Nodup) :
    ((win A B).map Rec.key).Nodup := by
  unfold win
  rw [List.map_append, List.nodup_append]
  refine ⟨hB, hA.sublist (List.filter_sublist.map _), ?_⟩
  intro a ha b hb e
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
  have h2 : y.key ∉ B.map Rec.key := by simpa using (List.mem_filter.1 hy).2
  subst e
  exact h2 ha

theorem win_toFinset (A B : List Rec) : (win A B).toFinset = winSet A.toFinset B.toFinset := by
  ext x
  simp only [win, winSet, List.toFinset_append, List.toFinset_filter, Finset.mem_union,
    Finset.mem_filter, List.mem_toFinset, Finset.mem_image]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h1, ?_⟩
      rintro ⟨y, hy, e⟩
      have h3 : x.key ∉ B.map Rec.key := by simpa using h2
      exact h3 (List.mem_map.2 ⟨y, hy, e⟩)
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h1, ?_⟩
      have h3 : x.key ∉ B.map Rec.key := fun hm => h2 (by
        obtain ⟨y, hy, e⟩ := List.mem_map.1 hm; exact ⟨y, hy, e⟩)
      simpa using h3

theorem win_keys (A B : List Rec) :
    ((win A B).map Rec.key).toFinset ⊆ (A.map Rec.key).toFinset ∪ (B.map Rec.key).toFinset := by
  intro k hk
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_union] at hk ⊢
  obtain ⟨x, hx, rfl⟩ := hk
  rcases mem_win hx with h | h
  · exact Or.inl ⟨x, h, rfl⟩
  · exact Or.inr ⟨x, h, rfl⟩

theorem win_card (A B : List Rec) :
    ((win A B).map Rec.key).toFinset.card ≤
      (A.map Rec.key).toFinset.card + (B.map Rec.key).toFinset.card :=
  (Finset.card_le_card (win_keys A B)).trans (Finset.card_union_le _ _)

theorem sWinners_eq (inp : SInputs) : inp.winners = win inp.aAll inp.bAll := rfl

theorem tWinners_eq (inp : TopInputs) : inp.winners = win inp.aAll inp.bAll := rfl

theorem dWinners_eq (inp : DirectJob.Inputs) :
    inp.winners = win inp.aRecords (DirectPrefix.winners inp.bRecords) := rfl

/-! ### Cardinalities -/

theorem card_le_of_keys {N : Nat} (S : Finset Rec)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, x.key = y.key → x = y) (hN : ∀ x ∈ S, x.key.toNat < N) :
    S.card ≤ N := by
  calc S.card = (S.image Rec.key).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (KeyIndex.range N).card := Finset.card_le_card (by
        intro k hk
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hk
        exact KeyIndex.mem_range.2 (hN x hx))
    _ = N := KeyIndex.range_card N

theorem keys_card_le {N : Nat} (l : List Rec) (hN : ∀ x ∈ l, x.key.toNat < N) :
    (l.map Rec.key).toFinset.card ≤ N := by
  calc (l.map Rec.key).toFinset.card ≤ (KeyIndex.range N).card := Finset.card_le_card (by
        intro k hk
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hk)
        exact KeyIndex.mem_range.2 (hN x hx))
    _ = N := KeyIndex.range_card N

theorem inj_of_nodup {l : List Rec} (h : (l.map Rec.key).Nodup) :
    ∀ x ∈ l.toFinset, ∀ y ∈ l.toFinset, x.key = y.key → x = y := by
  intro x hx y hy e
  exact List.inj_on_of_nodup_map h (List.mem_toFinset.1 hx) (List.mem_toFinset.1 hy) e

theorem toFinset_card_le {N : Nat} (l : List Rec) (h : (l.map Rec.key).Nodup)
    (hN : ∀ x ∈ l, x.key.toNat < N) : l.toFinset.card ≤ N :=
  card_le_of_keys _ (inj_of_nodup h) (fun x hx => hN x (List.mem_toFinset.1 hx))

theorem length_le_of_nodup {N : Nat} (l : List Rec) (h : (l.map Rec.key).Nodup)
    (hN : ∀ x ∈ l, x.key.toNat < N) : l.length ≤ N := by
  have := keys_card_le l hN
  rw [List.toFinset_card_of_nodup h, List.length_map] at this
  exact this

/-! ### Pages and prefix winners -/

theorem pagesOf_one (C : Nat) (tier : List (Option Rec)) : pagesOf C 1 tier = [Bucket.recs tier] := by
  simp [pagesOf]

/-- Splitting off the first page leaves the same paging rule on the suffix. -/
theorem pagesOf_succ_succ (C n : Nat) (tier : List (Option Rec)) :
    pagesOf C (n + 2) tier =
      Bucket.recs (tier.take C) :: pagesOf C (n + 1) (tier.drop C) := by
  unfold pagesOf
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  congr 1
  simp only [List.map_inj_left, List.mem_range, Function.comp_apply,
    List.drop_drop]
  intro p hp
  have hmul : C * (p + 1) = C + C * p := by ring
  rw [hmul]
  have he : p + 1 + 1 = n + 2 ↔ p + 1 = n + 1 := by omega
  simp only [he]

/-- Positive page counts preserve every tier record, including overflow in
    the reference continuation's last page. -/
theorem pagesOf_flatten (C n : Nat) (tier : List (Option Rec)) (hn : 0 < n) :
    (pagesOf C n tier).flatten = Bucket.recs tier := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  induction n generalizing tier with
  | zero => simp [pagesOf_one]
  | succ n ih =>
    rw [show (n + 1).succ = n + 2 by omega, pagesOf_succ_succ,
      List.flatten_cons, ih _ (by omega)]
    simpa only [Bucket.recs, List.filterMap_append] using
      congrArg (fun t => t.filterMap id) (List.take_append_drop C tier)

theorem prefix_sublist : ∀ rs : List Rec, (DirectPrefix.winners rs).Sublist rs
  | [] => List.Sublist.slnil
  | r :: rs => by
    simp only [DirectPrefix.winners]
    split_ifs
    · exact (prefix_sublist rs).cons r
    · exact (prefix_sublist rs).cons_cons r

theorem records_empty : DirectJob.emptyOutput.records = [] := rfl

theorem recs_map_some (l : List Rec) : Bucket.recs (l.map some) = l := by
  simp [Bucket.recs, List.filterMap_map]

end RebuildBound.HierarchyInvariantProof
