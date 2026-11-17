import RebuildBound.Proofs.D1
import RebuildBound.Proofs.D5
import RebuildBound.Proofs.ListAux.Bucket

/-!
# D4b, generic lemmas

Lists, `fill`, and the counting lemma: distinct keys absent from full homes
number at most `homeExcess`.
-/

namespace RebuildBound.D4b

open RebuildBound.Model

/-! ### Lists -/

/-- Keys of two lists of records, disjoint by home. -/
theorem nodup_keys_append_of_home {g : Geom} {w : Model.LogicalKey → Nat} {L₁ L₂ : List Rec}
    (h₁ : (L₁.map Rec.key).Nodup) (h₂ : (L₂.map Rec.key).Nodup)
    (h : ∀ x ∈ L₁, ∀ y ∈ L₂, home g w x ≠ home g w y) :
    ((L₁ ++ L₂).map Rec.key).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨h₁, h₂, ?_⟩
  intro a ha b hb e
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
  exact h x hx y hy (by simp [home, e])

/-! ### `fill` -/

theorem fill_free {α : Type} : ∀ (B : List (Option α)) (L : List α),
    (fill B L).1.countP (·.isNone) = B.countP (·.isNone) - min L.length (B.countP (·.isNone))
  | [], L => by simp [fill]
  | some r :: B, L => by simp [fill, fill_free B L]
  | none :: B, [] => by simp [fill]
  | none :: B, a :: L => by
    simp only [fill, List.countP_cons, fill_free B L, List.length_cons]
    simp [Nat.add_min_add_right]

theorem recs_eq_filterMap (B : Bucket) : B.recs = B.filterMap id := rfl

theorem recs_length_eq (B : Bucket) : B.recs.length = B.countP (·.isSome) :=
  (D1Lemmas.countP_isSome B).symm

/-- The overflow of `fill` is nonempty only when every lane ends occupied. -/
theorem fill_full_of_snd {B : Bucket} {L : List Rec} {r : Rec} (h : r ∈ (fill B L).2) :
    (Bucket.recs (fill B L).1).length = B.length := by
  rw [fill_snd] at h
  have hl : min L.length (B.countP (·.isNone)) < L.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    simp at h
  have h1 := (fill_recs_perm B L).length_eq
  have h2 := D1Lemmas.countP_isNone_add B
  simp only [List.length_append, List.length_take] at h1
  omega

/-! ### Keys -/

/-! ### The winners and the counting lemma -/

/-- The keys of the complete union A ∪ B, once each. -/
def WK (inp : Inputs) : List Model.LogicalKey := inp.winners.map Rec.key

theorem mem_WK_of_b {inp : Inputs} {r : Rec} (h : r ∈ inp.bAll) : r.key ∈ WK inp := by
  unfold WK Inputs.winners
  exact List.mem_map.2 ⟨r, List.mem_append_left _ h, rfl⟩

theorem mem_WK_of_a {inp : Inputs} {r : Rec} (h : r ∈ inp.aAll) : r.key ∈ WK inp := by
  by_cases hb : (inp.bAll.map Rec.key).contains r.key = true
  · have : r.key ∈ inp.bAll.map Rec.key := by simpa using hb
    obtain ⟨s, hs, e⟩ := List.mem_map.1 this
    rw [← e]; exact mem_WK_of_b hs
  · unfold WK Inputs.winners
    refine List.mem_map.2 ⟨r, List.mem_append_right _ (List.mem_filter.2 ⟨h, ?_⟩), rfl⟩
    simpa using hb

theorem WK_nodup {g : Geom} {TA TB : Nat} {wOld w : Model.LogicalKey → Nat} {inp : Inputs}
    (hI : InputValid g TA TB wOld w inp) : (WK inp).Nodup := by
  unfold WK Inputs.winners
  rw [List.map_append, List.nodup_append]
  refine ⟨hI.bNodup, ?_, ?_⟩
  · exact hI.aNodup.sublist (List.filter_sublist.map _)
  · intro a ha b hb e
    subst e
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hb
    have := (List.mem_filter.1 hr).2
    simp [ha] at this

theorem homeCount_eq (g : Geom) (w : Model.LogicalKey → Nat) (inp : Inputs) (v : Nat) :
    homeCount g w inp.winners v = ((WK inp).filter fun x => w x % g.homes == v).length := by
  unfold homeCount WK
  rw [← List.countP_eq_length_filter, List.countP_map]
  rfl

/-- **Counting.** Distinct union keys, each absent from its home's `C` distinct
union keys, number at most `homeExcess`. -/
theorem count_bound {g : Geom} {w : Model.LogicalKey → Nat} {inp : Inputs} (M : Nat → List Model.LogicalKey)
    (hM : ∀ v < g.homes, (M v).Nodup ∧ ∀ x ∈ M v, x ∈ WK inp ∧ w x % g.homes = v)
    (L : List Model.LogicalKey) (hL : L.Nodup)
    (hx : ∀ x ∈ L, x ∈ WK inp ∧ x ∉ M (w x % g.homes) ∧ g.C ≤ (M (w x % g.homes)).length) :
    L.length ≤ homeExcess g w inp := by
  have hpos : 0 < g.homes := Nat.two_pow_pos _
  have hsum := sum_countP_eq (fun x => w x % g.homes) L g.homes
  have hall : (L.countP fun x => decide (w x % g.homes < g.homes)) = L.length :=
    List.countP_eq_length.2 fun x _ => by simp [Nat.mod_lt _ hpos]
  rw [hall] at hsum
  rw [← hsum]
  unfold homeExcess
  apply List.sum_le_sum
  intro v hv
  have hv' : v < g.homes := List.mem_range.1 hv
  rw [homeCount_eq, List.countP_eq_length_filter]
  by_cases he : (L.filter fun x => w x % g.homes == v) = []
  · rw [he]; simp
  · obtain ⟨x, hxm⟩ := List.exists_mem_of_ne_nil _ he
    have hxv : w x % g.homes = v := by simpa using (List.mem_filter.1 hxm).2
    have hC := (hx x (List.mem_filter.1 hxm).1).2.2
    rw [hxv] at hC
    have hnd : ((L.filter fun x => w x % g.homes == v) ++ M v).Nodup := by
      rw [List.nodup_append]
      refine ⟨hL.filter _, (hM v hv').1, ?_⟩
      intro a ha b hb e
      subst e
      have hav : w a % g.homes = v := by simpa using (List.mem_filter.1 ha).2
      have := (hx a (List.mem_filter.1 ha).1).2.1
      rw [hav] at this
      exact this hb
    have hsub : ((L.filter fun x => w x % g.homes == v) ++ M v) ⊆
        ((WK inp).filter fun x => w x % g.homes == v) := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · have hav : w a % g.homes = v := by simpa using (List.mem_filter.1 ha).2
        exact List.mem_filter.2 ⟨(hx a (List.mem_filter.1 ha).1).1, by simpa using hav⟩
      · obtain ⟨h1, h2⟩ := (hM v hv').2 a ha
        exact List.mem_filter.2 ⟨h1, by simpa using h2⟩
    have := (hnd.subperm hsub).length_le
    simp only [List.length_append] at this
    omega

/-! ### Buckets at home -/

variable (g : Geom) (w : Model.LogicalKey → Nat) (inp : Inputs)

/-- A main bucket in good standing at home `v`: `C` lanes, records at home `v`
with union keys, distinct keys. -/
structure HomeOK (v : Nat) (B : Bucket) : Prop where
  len : B.length = g.C
  home : ∀ r ∈ B.recs, home g w r = v
  wk : ∀ r ∈ B.recs, r.key ∈ WK inp
  nd : B.keys.Nodup

/-- Key `x` is shut out of a full bucket. -/
def Blocks (x : Model.LogicalKey) (B : Bucket) : Prop := B.recs.length = g.C ∧ x ∉ B.keys

variable {g w inp}

/-- The counting lemma for a main table. -/
theorem count_main (main : List Bucket) (hok : ∀ v < g.homes, HomeOK g w inp v (main.getD v []))
    (L : List Rec) (hnd : (L.map Rec.key).Nodup)
    (hL : ∀ r ∈ L, r.key ∈ WK inp ∧ Blocks g r.key (main.getD (home g w r) [])) :
    L.length ≤ homeExcess g w inp := by
  have h := count_bound (g := g) (w := w) (inp := inp) (fun v => (main.getD v []).keys) ?_ (L.map Rec.key) hnd ?_
  · simpa using h
  · intro v hv
    refine ⟨(hok v hv).nd, ?_⟩
    intro x hx
    obtain ⟨r, hr, rfl⟩ := mem_keys.1 hx
    exact ⟨(hok v hv).wk r hr, (hok v hv).home r hr⟩
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    obtain ⟨h1, h2, h3⟩ := hL r hr
    refine ⟨h1, h3, ?_⟩
    show g.C ≤ (main.getD (home g w r) []).keys.length
    rw [keys_eq, List.length_map, h2]

end RebuildBound.D4b
