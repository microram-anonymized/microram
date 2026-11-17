import RebuildBound.Proofs.BlindBits.Bits
import RebuildBound.Proofs.ListAux.Pairs
import RebuildBound.Proofs.ListAux.Bucket

/-!
# BlindBits: flattened main lists (from G2.Route)

`flat` (the records of a list of buckets) and its `set`/`getD`/`countP`
facts. Moved from the binary d = 2 chain (`G2.Route`); namespace
`RebuildBound.G2` kept.
-/

namespace RebuildBound.G2
open RebuildBound.Model RebuildBound.Spec
/-- All records of a list of buckets, bucket by bucket. -/
def flat (l : List Bucket) : List Rec := l.flatMap Bucket.recs

theorem flat_cons (B : Bucket) (l : List Bucket) : flat (B :: l) = B.recs ++ flat l := by
  simp [flat]

theorem flat_set : ∀ (l : List Bucket) (i : ℕ), i < l.length → ∀ x : Bucket,
    ((flat (l.set i x) : List Rec) : Multiset Rec) + ((l.getD i []).recs : Multiset Rec) =
      (flat l : Multiset Rec) + (x.recs : Multiset Rec)
  | [], i, h, _ => by simp at h
  | B :: l, 0, _, x => by
    simp only [List.set_cons_zero, flat_cons, List.getD_cons_zero, ← Multiset.coe_add]
    abel
  | B :: l, i + 1, h, x => by
    simp only [List.set_cons_succ, flat_cons, List.getD_cons_succ, ← Multiset.coe_add]
    have := flat_set l i (by simpa using h) x
    rw [add_assoc, this, add_assoc]

theorem getD_mem {l : List Bucket} {i : ℕ} (h : i < l.length) : l.getD i [] ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

theorem mem_flat {l : List Bucket} {r : Rec} : r ∈ flat l ↔ ∃ B ∈ l, r ∈ B.recs := by
  simp [flat]

theorem mem_flat_of_getD {l : List Bucket} {u : ℕ} {r : Rec} (h : r ∈ (l.getD u []).recs) :
    r ∈ flat l := by
  rcases D5.recs_getD_sub l u with h' | h'
  · rw [h'] at h; simp at h
  · exact mem_flat.2 ⟨_, h', h⟩

theorem flat_countP (l : List Bucket) (q : Rec → Bool) :
    (flat l).countP q = ∑ u ∈ Finset.range l.length, (l.getD u []).recs.countP q := by
  induction l with
  | nil => simp [flat]
  | cons B l ih =>
    rw [flat_cons, List.countP_append, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

end RebuildBound.G2
