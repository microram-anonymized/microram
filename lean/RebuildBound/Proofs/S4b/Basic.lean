import RebuildBound.Proofs.ListAux.Bucket
import RebuildBound.Proofs.ListAux.Occupancy
import RebuildBound.Spec.SepT

/-!
# S4b, generic lemmas for the separated-sources model

The general-digit counterpart of `D4b/Basic`: homes are `sHome` of the merge
family, `N` of them. `HomeOK` (a main bucket in good standing), `Blocks` (a key
shut out of a full bucket), and the counting lemma: distinct union keys shut
out of full homes number at most `sHomeExcess`.
-/

namespace RebuildBound.S4b

open RebuildBound.Model
open RebuildBound.D4b

/-- The keys of the complete union A ∪ B, once each. -/
def WK (inp : SInputs) : List Model.LogicalKey := inp.winners.map Rec.key

theorem homeOf_lt {g : SepGeom} (hg : g.Valid) (t : Nat) : g.homeOf t < g.N := by
  unfold SepGeom.homeOf SepGeom.cls SepGeom.N
  have hr : 0 < g.r := hg.1
  have h1 : t % 2 ^ g.k < 2 ^ g.k := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h2 : t / 2 ^ g.k % g.r < g.r := Nat.mod_lt _ hr
  have h3 : 2 ^ g.k * (t / 2 ^ g.k % g.r + 1) ≤ 2 ^ g.k * g.r :=
    Nat.mul_le_mul_left _ h2
  rw [Nat.mul_comm g.r]
  rw [Nat.mul_add, Nat.mul_one] at h3
  omega

theorem sHome_lt {g : SepGeom} (hg : g.Valid) (w : Model.LogicalKey → Nat) (r : Rec) : sHome g w r < g.N :=
  homeOf_lt hg _

theorem mem_WK_of_b {inp : SInputs} {r : Rec} (h : r ∈ inp.bAll) : r.key ∈ WK inp := by
  unfold WK SInputs.winners
  exact List.mem_map.2 ⟨r, List.mem_append_left _ h, rfl⟩

theorem mem_WK_of_a {inp : SInputs} {r : Rec} (h : r ∈ inp.aAll) : r.key ∈ WK inp := by
  by_cases hb : (inp.bAll.map Rec.key).contains r.key = true
  · have : r.key ∈ inp.bAll.map Rec.key := by simpa using hb
    obtain ⟨s, hs, e⟩ := List.mem_map.1 this
    rw [← e]; exact mem_WK_of_b hs
  · unfold WK SInputs.winners
    refine List.mem_map.2 ⟨r, List.mem_append_right _ (List.mem_filter.2 ⟨h, ?_⟩), rfl⟩
    simpa using hb

theorem WK_nodup {g : SepGeom} {wOld w : Model.LogicalKey → Nat} {inp : SInputs}
    (hI : SInputShape g wOld w inp) : (WK inp).Nodup := by
  unfold WK SInputs.winners
  rw [List.map_append, List.nodup_append]
  refine ⟨hI.bNodup, ?_, ?_⟩
  · exact hI.aNodup.sublist (List.filter_sublist.map _)
  · intro a ha b hb e
    subst e
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hb
    have := (List.mem_filter.1 hr).2
    simp [ha] at this

theorem homeCount_eq (g : SepGeom) (w : Model.LogicalKey → Nat) (inp : SInputs) (v : Nat) :
    sHomeCount g w inp.winners v =
      ((WK inp).filter fun x => g.homeOf (w x) == v).length := by
  unfold sHomeCount WK
  rw [← List.countP_eq_length_filter, List.countP_map]
  rfl

/-- **Counting.** Distinct union keys, each absent from its home's `C` distinct
union keys, number at most `sHomeExcess`. -/
theorem count_bound {g : SepGeom} (hg : g.Valid) {w : Model.LogicalKey → Nat} {inp : SInputs}
    (M : Nat → List Model.LogicalKey)
    (hM : ∀ v < g.N, (M v).Nodup ∧ ∀ x ∈ M v, x ∈ WK inp ∧ g.homeOf (w x) = v)
    (L : List Model.LogicalKey) (hL : L.Nodup)
    (hx : ∀ x ∈ L, x ∈ WK inp ∧ x ∉ M (g.homeOf (w x)) ∧ g.C ≤ (M (g.homeOf (w x))).length) :
    L.length ≤ sHomeExcess g w inp := by
  have hsum := sum_countP_eq (fun x => g.homeOf (w x)) L g.N
  have hall : (L.countP fun x => decide (g.homeOf (w x) < g.N)) = L.length :=
    List.countP_eq_length.2 fun x _ => by simpa using homeOf_lt hg (w x)
  rw [hall] at hsum
  rw [← hsum]
  unfold sHomeExcess sExcess
  apply List.sum_le_sum
  intro v hv
  have hv' : v < g.N := List.mem_range.1 hv
  rw [homeCount_eq, List.countP_eq_length_filter]
  by_cases he : (L.filter fun x => g.homeOf (w x) == v) = []
  · rw [he]; simp
  · obtain ⟨x, hxm⟩ := List.exists_mem_of_ne_nil _ he
    have hxv : g.homeOf (w x) = v := by simpa using (List.mem_filter.1 hxm).2
    have hC := (hx x (List.mem_filter.1 hxm).1).2.2
    rw [hxv] at hC
    have hnd : ((L.filter fun x => g.homeOf (w x) == v) ++ M v).Nodup := by
      rw [List.nodup_append]
      refine ⟨hL.filter _, (hM v hv').1, ?_⟩
      intro a ha b hb e
      subst e
      have hav : g.homeOf (w a) = v := by simpa using (List.mem_filter.1 ha).2
      have := (hx a (List.mem_filter.1 ha).1).2.1
      rw [hav] at this
      exact this hb
    have hsub : ((L.filter fun x => g.homeOf (w x) == v) ++ M v) ⊆
        ((WK inp).filter fun x => g.homeOf (w x) == v) := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · have hav : g.homeOf (w a) = v := by simpa using (List.mem_filter.1 ha).2
        exact List.mem_filter.2 ⟨(hx a (List.mem_filter.1 ha).1).1, by simpa using hav⟩
      · obtain ⟨h1, h2⟩ := (hM v hv').2 a ha
        exact List.mem_filter.2 ⟨h1, by simpa using h2⟩
    have := (hnd.subperm hsub).length_le
    simp only [List.length_append] at this
    omega

/-! ### Buckets at home -/

/-- A main bucket in good standing at home `v`: `C` lanes, records at home `v`
with union keys, distinct keys. -/
structure HomeOK (g : SepGeom) (w : Model.LogicalKey → Nat) (inp : SInputs) (v : Nat) (B : Bucket) :
    Prop where
  len : B.length = g.C
  home : ∀ r ∈ B.recs, sHome g w r = v
  wk : ∀ r ∈ B.recs, r.key ∈ WK inp
  nd : B.keys.Nodup

/-- Key `x` is shut out of a full bucket. -/
def Blocks (g : SepGeom) (x : Model.LogicalKey) (B : Bucket) : Prop := B.recs.length = g.C ∧ x ∉ B.keys

/-- The counting lemma for a main table. -/
theorem count_main {g : SepGeom} (hg : g.Valid) {w : Model.LogicalKey → Nat} {inp : SInputs}
    (main : List Bucket) (hok : ∀ v < g.N, HomeOK g w inp v (main.getD v []))
    (L : List Rec) (hnd : (L.map Rec.key).Nodup)
    (hL : ∀ r ∈ L, r.key ∈ WK inp ∧ Blocks g r.key (main.getD (sHome g w r) [])) :
    L.length ≤ sHomeExcess g w inp := by
  have h := count_bound hg (w := w) (inp := inp) (fun v => (main.getD v []).keys) ?_
    (L.map Rec.key) hnd ?_
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
    show g.C ≤ (main.getD (sHome g w r) []).keys.length
    rw [keys_eq, List.length_map, h2]

/-- What the rest of the job needs from A's route. -/
structure RouteOut (g : SepGeom) (w : Model.LogicalKey → Nat) (inp : SInputs) (s : SRoute) : Prop where
  len : s.main.length = g.N
  ok : ∀ v < g.N, HomeOK g w inp v (s.main.getD v [])
  poolNd : ((sPool s inp.aTier inp.bTier).map Rec.key).Nodup
  poolIn : ∀ r ∈ sPool s inp.aTier inp.bTier, r ∈ inp.aAll
  poolNotB : ∀ r ∈ sPool s inp.aTier inp.bTier, r.key ∉ inp.bTier.flatten.map Rec.key
  tr : ∀ e ∈ s.trace, (∃ j c, e.1 = STest.stash j c) ∨ e.1 = STest.radix

end RebuildBound.S4b
