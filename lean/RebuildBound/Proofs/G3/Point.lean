import RebuildBound.Proofs.G3.Law
import RebuildBound.Proofs.StageAvg

/-!
# G3: counts of the fixed key sets

`topCount` over a list with distinct keys is the number of its keys with the given home;
the keys of A and of the live set are fixed by the law.
-/

open scoped ENNReal NNReal

namespace RebuildBound.G3Proof

open RebuildBound.Model RebuildBound.Spec

/-- The home-count vector of a key set. -/
def cntK (m : ℕ) (K : Finset Model.LogicalKey) (w : Model.LogicalKey → ℕ) : Fin (2 ^ m) → ℕ :=
  fun v => (K.filter fun x => w x % 2 ^ m = v.val).card

theorem topCount_eq (g : TopGeom) (w : Model.LogicalKey → ℕ) (l : List Rec) (hnd : (l.map Rec.key).Nodup)
    (v : ℕ) :
    topCount g w l v =
      ((l.map Rec.key).toFinset.filter fun x => w x % 2 ^ (g.k + g.e) = v).card := by
  induction l with
  | nil => simp [topCount]
  | cons r l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    have ih := ih hnd.2
    unfold topCount at ih ⊢
    rw [List.countP_cons, ih, List.map_cons, List.toFinset_cons, Finset.filter_insert]
    have hT : g.T = 2 ^ (g.k + g.e) := rfl
    simp only [topHome, hT, beq_iff_eq]
    split_ifs with h1
    · rw [Finset.card_insert_of_notMem]
      intro hmem
      exact hnd.1 (by simpa using (Finset.mem_filter.mp hmem).1)
    · simp

/-- Winners are distinct by key, with key set `A ∪ B`. -/
theorem winners_keys (inp : TopInputs) (ha : (inp.aAll.map Rec.key).Nodup)
    (hb : (inp.bAll.map Rec.key).Nodup) :
    (inp.winners.map Rec.key).Nodup := by
  unfold TopInputs.winners
  rw [List.map_append, List.nodup_append]
  refine ⟨hb, ((List.filter_sublist).map _).nodup ha, ?_⟩
  intro a ha' b hb' hab
  subst hab
  simp only [List.mem_map, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hb'
  obtain ⟨r, ⟨_, hc⟩, rfl⟩ := hb'
  exact hc (List.mem_map.mp ha')

theorem live_keys (inp : TopInputs) (ha : (inp.aAll.map Rec.key).Nodup)
    (hb : (inp.bAll.map Rec.key).Nodup) : (inp.live.map Rec.key).Nodup := by
  unfold TopInputs.live
  exact ((List.filter_sublist).map _).nodup (winners_keys inp ha hb)

theorem live_toFinset (inp : TopInputs) (RA RB : Finset Rec) (ha : inp.aAll.toFinset = RA)
    (hb : inp.bAll.toFinset = RB) : inp.live.toFinset = liveSet RA RB := by
  subst ha hb
  ext r
  simp only [TopInputs.live, TopInputs.winners, liveSet, List.mem_toFinset, List.mem_filter,
    List.mem_append, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
    Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, List.mem_map]

theorem map_key_toFinset (l : List Rec) : (l.map Rec.key).toFinset = l.toFinset.image Rec.key := by
  ext x; simp

end RebuildBound.G3Proof
