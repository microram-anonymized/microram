import RebuildBound.Spec.Model.TopCanonical
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.ENNReal.Inv

/-!
# CanonTop: the canonical top law meets `TopLaw` at every population size

`RebuildBound.TopCanonical : TopCanonical_statement`. Follows `Proofs/Canon.lean`:
general facts about `placeRecs C n hm rs` (`0 < n`): `n` buckets of `C` lanes,
buckets then tier are a permutation of `rs`, bucket `i` holds only records
with `hm r % n = i`, and a tier record's bucket is full.
-/

namespace RebuildBound.CanonTopLemmas

open RebuildBound.Model
open scoped ENNReal NNReal

instance : LawfulBEq Rec where
  rfl {a} := by
    cases a with
    | mk key val tomb =>
      change ((key == key) && ((val == val) && (tomb == tomb))) = true
      simp
  eq_of_beq {a b} h := by
    cases a with
    | mk ak av atomb =>
      cases b with
      | mk bk bv bt =>
        change ((ak == bk) && ((av == bv) && (atomb == bt))) = true at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        rfl


theorem bucket_recs (l : List Rec) (n : Nat) :
    Bucket.recs (l.map some ++ List.replicate n none) = l := by
  simp [Bucket.recs, List.filterMap_append, List.filterMap_map]

theorem flatMap_filter_perm (n : Nat) (hn : 0 < n) (hm : Rec → Nat) (rs : List Rec) :
    ((List.range n).flatMap fun i => rs.filter fun x => hm x % n == i).Perm rs := by
  rw [List.perm_iff_count]
  intro a
  rw [List.count_flatMap]
  have hc : ∀ i, (List.count a ∘ fun i => rs.filter fun x => hm x % n == i) i =
      if i = hm a % n then List.count a rs else 0 := by
    intro i
    simp only [Function.comp_apply]
    split_ifs with h
    · exact List.count_filter (by simp [h])
    · refine List.count_eq_zero_of_not_mem fun hmem => h ?_
      have := (List.mem_filter.1 hmem).2
      simp at this
      exact this.symm
  rw [List.map_congr_left (fun i _ => hc i), ← List.sum_toFinset _ List.nodup_range,
    Finset.sum_ite_eq']
  simp [Nat.mod_lt _ hn]

section
variable (C n : Nat) (hm : Rec → Nat) (rs : List Rec)

def here (i : Nat) : List Rec := rs.filter fun r => hm r % n == i

theorem fst_eq : (placeRecs C n hm rs).1 = (List.range n).map fun i =>
    ((here n hm rs i).take C).map some ++
      List.replicate (C - ((here n hm rs i).take C).length) none := rfl

theorem snd_eq : (placeRecs C n hm rs).2 =
    (List.range n).flatMap fun i => (here n hm rs i).drop C := rfl

theorem length_fst : (placeRecs C n hm rs).1.length = n := by
  simp [fst_eq]

theorem lanes : ∀ B ∈ (placeRecs C n hm rs).1, B.length = C := by
  intro B hB
  rw [fst_eq] at hB
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hB
  simp only [List.length_append, List.length_map, List.length_replicate]
  have := List.length_take_le C (here n hm rs i)
  omega

theorem recs_getD {i : Nat} (hi : i < n) :
    ((placeRecs C n hm rs).1.getD i []).recs = (here n hm rs i).take C := by
  rw [fst_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  exact bucket_recs _ _

theorem home {i : Nat} (hi : i < n) :
    ∀ r ∈ ((placeRecs C n hm rs).1.getD i []).recs, hm r % n = i := by
  intro r hr
  rw [recs_getD C n hm rs hi] at hr
  have := (List.mem_filter.1 (List.mem_of_mem_take hr)).2
  simpa using this

theorem tierFull :
    ∀ r ∈ (placeRecs C n hm rs).2,
      ((placeRecs C n hm rs).1.getD (hm r % n) []).recs.length = C := by
  intro x hx0
  rw [snd_eq] at hx0
  obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.1 hx0
  have hxh : x ∈ here n hm rs i := List.mem_of_mem_drop hxi
  have hhome : hm x % n = i := by simpa [here] using (List.mem_filter.1 hxh).2
  have hlen : C < (here n hm rs i).length := by
    have := List.length_pos_of_mem hxi
    rw [List.length_drop] at this
    omega
  rw [hhome, recs_getD C n hm rs (List.mem_range.1 hi), List.length_take]
  omega

theorem all_perm (hn : 0 < n) :
    ((placeRecs C n hm rs).1.flatMap Bucket.recs ++ (placeRecs C n hm rs).2).Perm rs := by
  have h1 : (placeRecs C n hm rs).1.flatMap Bucket.recs =
      (List.range n).flatMap fun i => (here n hm rs i).take C := by
    rw [fst_eq, List.flatMap_map]
    simp only [bucket_recs]
  rw [h1, snd_eq]
  refine (List.flatMap_append_perm _ _ _).trans ?_
  simp only [List.take_append_drop]
  exact flatMap_filter_perm n hn hm rs

end

theorem nodup_keys (RA : Finset Rec) (h : (RA.image Rec.key).card = RA.card) :
    (RA.toList.map Rec.key).Nodup := by
  have h1 : (RA.toList.map Rec.key).toFinset = RA.image Rec.key := by
    ext x; simp
  have h2 : (RA.toList.map Rec.key).toFinset.card = (RA.toList.map Rec.key).length := by
    rw [h1, h]; simp
  exact Multiset.coe_nodup.1 ((Multiset.toFinset_card_eq_card_iff_nodup
    (m := ((RA.toList.map Rec.key : List Model.LogicalKey) : Multiset Model.LogicalKey))).1 h2)

theorem pa_perm_aux (g : TopGeom) (RA RB : Finset Rec) (W : Nat)
    (h : (canonicalTopLaw g RA RB W).Key → Fin (2 ^ W)) :
    (((canonicalTopLaw g RA RB W).inputs () ((canonicalTopLaw g RA RB W).wordFn h)).aAll).Perm
      RA.toList :=
  all_perm g.C g.T _ _ (Nat.two_pow_pos _)

theorem pb_perm_aux (g : TopGeom) (RA RB : Finset Rec) (W : Nat)
    (h : (canonicalTopLaw g RA RB W).Key → Fin (2 ^ W)) :
    (((canonicalTopLaw g RA RB W).inputs () ((canonicalTopLaw g RA RB W).wordFn h)).bAll).Perm
      RB.toList :=
  all_perm g.C g.U _ _ (Nat.two_pow_pos _)

end RebuildBound.CanonTopLemmas

open RebuildBound.Model RebuildBound.CanonTopLemmas in
open scoped ENNReal NNReal in
theorem RebuildBound.TopCanonical : RebuildBound.Model.TopCanonical_statement := by
  intro g unsh RA RB W lam hA hB hunsh hW hAl hWl
  have hT : 0 < g.T := Nat.two_pow_pos _
  have hU : 0 < g.U := Nat.two_pow_pos _
  have hAn := nodup_keys RA hA
  have hBn := nodup_keys RB hB
  refine ⟨?_, ?_, ?_, ?_, hW, hAl, hWl⟩
  · show ∑ _x : Unit, (1 : ℝ≥0∞) = 1
    simp
  · intro _ h
    set w := (canonicalTopLaw g RA RB W).wordFn h with hw
    have pa := all_perm g.C g.T (fun r => w r.key) RA.toList hT
    have pb := all_perm g.C g.U (fun r => w r.key) RB.toList hU
    refine
      { cLen := length_fst _ _ _ _
        cLanes := lanes _ _ _ _
        bLen := length_fst _ _ _ _
        bLanes := lanes _ _ _ _
        aNodup := (pa.map Rec.key).nodup_iff.2 hAn
        bNodup := (pb.map Rec.key).nodup_iff.2 hBn
        cHome := fun v hv => home g.C g.T _ _ hv
        bHome := fun i hi => home g.C g.U _ _ hi
        carryFull := fun r hr => tierFull g.C g.T _ _ r hr
        tierUnsh := ?_ }
    intro r hr he c hc hck
    have hrB : r ∈ RB := by
      have := pb.subset (List.mem_append_right _ hr)
      simpa using this
    have hcA : c ∈ RA := by
      have := pa.subset (List.mem_append_left _ hc)
      simpa using this
    exact hunsh r hrB he c hcA hck
  · intro hist h
    cases hist
    ext x
    show _ ↔ x ∈ RA
    have := (pa_perm_aux g RA RB W h).mem_iff (a := x)
    simpa using this
  · intro hist h
    cases hist
    ext x
    show _ ↔ x ∈ RB
    have := (pb_perm_aux g RA RB W h).mem_iff (a := x)
    simpa using this
