import RebuildBound.Proofs.D8.Basic

/-!
# D8: one home's resolution, merge and offers

The model's `topDest` acts on the share of one home `v` of the finish state
(main bucket, leaf candidates of home `v`, B-tier candidates of home `v`) by
`hstep`: the clear, the resolution (`hres`), the merge of B's live
records, and the two offers (`hoff`). This file proves the conservation,
provenance and counting facts of that step for lists with distinct keys.
-/

namespace RebuildBound.D8

open RebuildBound.Model RebuildBound.D23

/-- The share of one home in a finish state. -/
structure HQ where
  m : Bucket
  P : List Rec
  T : List Rec

/-- The resolution at one destination: (d) C's tombstones; (a)+(c) on the leaf
candidates; (b)+(c) on the B-tier candidates. `dk` are the keys of B's
direction records. -/
def hres (dk : List Model.LogicalKey) (h : HQ) : HQ :=
  ⟨(dropTombs h.m).clear fun key => (h.T.map Rec.key).contains key,
   h.P.filter fun r => !(dk.contains r.key || r.tomb),
   h.T.filter fun r => !r.tomb⟩

/-- The offers: the leaf candidates, then the B-tier candidates. -/
def hoff (h : HQ) : HQ :=
  ⟨(fill (fill h.m h.P).1 h.T).1,
   h.P.filter fun r => !((h.P.take (h.P.length - (fill h.m h.P).2.length)).map Rec.key).contains r.key,
   h.T.filter fun r => !((h.T.take (h.T.length -
     (fill (fill h.m h.P).1 h.T).2.length)).map Rec.key).contains r.key⟩

/-- One home's visit, after the clear: the resolution, the merge of `S` (B's
live direction records) and the offers. Returns the new share and the
direction's sheds. -/
def hvisit (dk : List Model.LogicalKey) (S : List Rec) (h : HQ) : HQ × List Rec :=
  let h1 := hres dk h
  let f := fill h1.m S
  (hoff ⟨f.1, h1.P, h1.T⟩, f.2)

/-- One home's whole visit: the clear against B's keys, then `hvisit`. -/
def hstep (clr : Model.LogicalKey → Bool) (dk : List Model.LogicalKey) (S : List Rec) (h : HQ) : HQ × List Rec :=
  hvisit dk S ⟨h.m.clear clr, h.P, h.T⟩

/-! ### The offers -/

theorem filter_notin_take (P : List Rec) (n : Nat) (hn : (P.map Rec.key).Nodup) :
    P.filter (fun r => !((P.take n).map Rec.key).contains r.key) = P.drop n := by
  have hsplit : P.filter (fun r => !((P.take n).map Rec.key).contains r.key) =
      (P.take n ++ P.drop n).filter (fun r => !((P.take n).map Rec.key).contains r.key) := by
    rw [List.take_append_drop]
  rw [hsplit]
  have hn' : ((P.take n ++ P.drop n).map Rec.key).Nodup := by
    rw [List.take_append_drop]; exact hn
  rw [List.filter_append, filter_keys_nil, List.nil_append, filter_keys_self]
  · exact keys_disjoint_of_nodup hn'
  · intro r hr; exact List.mem_map_of_mem hr

theorem placed_eq (M : Bucket) (L : List Rec) :
    L.length - (fill M L).2.length = min (nfree M) L.length := by
  rw [fill_snd, List.length_drop]
  have := Nat.min_le_right (nfree M) L.length
  omega

section off
variable (M1 : Bucket) (P T : List Rec)

/-- The leaf candidates placed. -/
def nP : Nat := min (nfree M1) P.length
/-- The B-tier candidates placed. -/
def nT : Nat := min (nfree (fill M1 P).1) T.length

theorem hoff_m : (hoff ⟨M1, P, T⟩).m = (fill (fill M1 P).1 T).1 := rfl

theorem hoff_P (hP : (P.map Rec.key).Nodup) : (hoff ⟨M1, P, T⟩).P = P.drop (nP M1 P) := by
  show P.filter (fun r => !((P.take (P.length - (fill M1 P).2.length)).map Rec.key).contains r.key) = _
  rw [placed_eq]; exact filter_notin_take P _ hP

theorem hoff_T (hT : (T.map Rec.key).Nodup) : (hoff ⟨M1, P, T⟩).T = T.drop (nT M1 P T) := by
  show T.filter (fun r => !((T.take (T.length -
     (fill (fill M1 P).1 T).2.length)).map Rec.key).contains r.key) = _
  rw [placed_eq]; exact filter_notin_take T _ hT

theorem hoff_m_length : (hoff ⟨M1, P, T⟩).m.length = M1.length := by
  rw [hoff_m, D1Lemmas.fill_length, D1Lemmas.fill_length]

theorem hoff_m_recs : List.Perm (hoff ⟨M1, P, T⟩).m.recs
    (M1.recs ++ P.take (nP M1 P) ++ T.take (nT M1 P T)) := by
  rw [hoff_m]
  have h2 := fill_recs (fill M1 P).1 T
  have h1 := fill_recs M1 P
  have : List.Perm ((fill (fill M1 P).1 T).1.filterMap id)
      (M1.recs ++ P.take (nP M1 P) ++ T.take (nT M1 P T)) :=
    h2.trans (h1.append_right _)
  exact this

theorem hoff_nfree : nfree (hoff ⟨M1, P, T⟩).m = nfree M1 - P.length - T.length := by
  rw [hoff_m, fill_nfree, fill_nfree]

end off

/-! ### The merge and the chain -/

theorem merge_chain (M : Bucket) (S P T : List Rec)
    (hn : ((M.recs ++ S ++ P ++ T).map Rec.key).Nodup) :
    let f := fill M S
    let h := hoff ⟨f.1, P, T⟩
    List.Perm (h.m.recs ++ f.2 ++ h.P ++ h.T) (M.recs ++ S ++ P ++ T) ∧
      h.m.length = M.length ∧
      h.m.recs.length = min M.length (M.recs.length + S.length + P.length + T.length) ∧
      (f.2 ≠ [] ∨ h.P ≠ [] ∨ h.T ≠ [] → nfree h.m = 0) := by
  intro f h
  have hP : (P.map Rec.key).Nodup :=
    nodup_keys_sublist ((List.sublist_append_right (M.recs ++ S) P).trans
      (List.sublist_append_left _ T)) hn
  have hT : (T.map Rec.key).Nodup := nodup_keys_sublist (List.sublist_append_right _ T) hn
  have hhP : h.P = P.drop (nP f.1 P) := hoff_P f.1 P T hP
  have hhT : h.T = T.drop (nT f.1 P T) := hoff_T f.1 P T hT
  have hf2 : f.2 = S.drop (min (nfree M) S.length) := fill_snd M S
  have hf1 : List.Perm (Bucket.recs f.1) (M.recs ++ S.take (min (nfree M) S.length)) := fill_recs M S
  have hhm : List.Perm h.m.recs ((Bucket.recs f.1) ++ P.take (nP f.1 P) ++ T.take (nT f.1 P T)) :=
    hoff_m_recs f.1 P T
  have hnf1 : nfree f.1 = nfree M - S.length := fill_nfree M S
  have hmlen : h.m.length = M.length := by
    rw [hoff_m_length, D1Lemmas.fill_length]
  have hrl := recs_length_add_nfree M
  have hrl' : (Bucket.recs M).length + nfree M = M.length := hrl
  have hflen : (Bucket.recs f.1).length = M.recs.length + min (nfree M) S.length := by
    rw [hf1.length_eq, List.length_append, List.length_take]
    omega
  have hnfh : nfree h.m = nfree M - S.length - P.length - T.length := by
    show nfree (hoff ⟨f.1, P, T⟩).m = _
    rw [hoff_nfree, hnf1]
  refine ⟨?_, hmlen, ?_, ?_⟩
  · rw [List.perm_iff_count]
    intro x
    have c1 := hhm.count_eq x
    have c2 := hf1.count_eq x
    have cS : List.count x S = List.count x (S.take (min (nfree M) S.length)) +
        List.count x (S.drop (min (nfree M) S.length)) := by
      rw [← List.count_append, List.take_append_drop]
    have cP : List.count x P = List.count x (P.take (nP f.1 P)) + List.count x (P.drop (nP f.1 P)) := by
      rw [← List.count_append, List.take_append_drop]
    have cT : List.count x T = List.count x (T.take (nT f.1 P T)) +
        List.count x (T.drop (nT f.1 P T)) := by
      rw [← List.count_append, List.take_append_drop]
    rw [hhP, hhT, hf2]
    simp only [List.count_append] at c1 c2 ⊢
    omega
  · have hl := hhm.length_eq
    simp only [List.length_append, List.length_take] at hl
    rw [hl, hflen]
    unfold nP nT
    rw [hnf1, fill_nfree]
    have := Nat.min_le_right (nfree M) S.length
    omega
  · intro hne
    rw [hnfh]
    rw [hhP, hhT, hf2] at hne
    unfold nP nT at hne
    rw [hnf1, fill_nfree] at hne
    simp only [ne_eq, List.drop_eq_nil_iff, not_le] at hne
    omega

end RebuildBound.D8
