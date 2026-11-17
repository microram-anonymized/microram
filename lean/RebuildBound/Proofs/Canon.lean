import RebuildBound.Spec.Model.Canonical
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.ENNReal.Inv

/-!
# Canon: the canonical law meets `InputLaw` at every population size

`RebuildBound.Canonical : Canonical_statement`. The work is a general lemma
about the canonical reference producer `placeBy C U hm v ks` (namespace
`RebuildBound.CanonLemmas`):

1. it has `U` buckets of exactly `C` lanes;
2. its records (bucket order, then the tier) are a permutation of
   `ks.map (⟨·, v, false⟩)`: the buckets hold `take C` and the tier `drop C`
   of each home's filter, and the filters by home partition `ks`;
3. bucket `i` holds only records of home `i`;
4. a tier record's home bucket is full.

Applied to A (old homes `canonOld KA o`) and B (merge-family words) it gives
`InputShape` on every outcome, and the key sets. The density of the old-home
vector is exactly the uniform one, because `canonOld KA o` reads `o` on `KA`.

At the end, `big_population`: a population too large for any tier (`C = 64`,
`|KB| = 129`) still has a law meeting `InputLaw`.

No probability API is needed: the history space is finite and the law is
uniform, so the proof works with finite `ℝ≥0∞` sums directly.
-/

namespace RebuildBound.CanonLemmas

open RebuildBound.Model
open scoped ENNReal NNReal

/-- The record the canonical producer writes for key `x`, with value `v`. -/
abbrev mk (v : Nat) (x : Model.LogicalKey) : Rec := ⟨x, v, false⟩

/-- The records of a bucket made of records followed by free lanes. -/
theorem bucket_recs (v : Nat) (l : List Model.LogicalKey) (n : Nat) :
    Bucket.recs (l.map (fun x => some (mk v x)) ++ List.replicate n none) = l.map (mk v) := by
  simp [Bucket.recs, List.filterMap_append, List.filterMap_map]

/-- The partition of a list by residues: the filters by home `i < U` together
are a permutation of the list. -/
theorem flatMap_filter_perm (U : Nat) (hU : 0 < U) (hm : Model.LogicalKey → Nat) (ks : List Model.LogicalKey) :
    ((List.range U).flatMap fun i => ks.filter fun x => hm x % U == i).Perm ks := by
  rw [List.perm_iff_count]
  intro a
  rw [List.count_flatMap]
  have hc : ∀ i, (List.count a ∘ fun i => ks.filter fun x => hm x % U == i) i =
      if i = hm a % U then List.count a ks else 0 := by
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
  simp [Nat.mod_lt _ hU]

section
variable (C U : Nat) (hm : Model.LogicalKey → Nat) (v : Nat) (ks : List Model.LogicalKey)

/-- The keys of home `i`, in the order of `ks`. -/
def here (i : Nat) : List Model.LogicalKey := ks.filter fun x => hm x % U == i

theorem placeBy_fst : (placeBy C U hm v ks).1 = (List.range U).map fun i =>
    ((here U hm ks i).take C).map (fun x => some (mk v x)) ++
      List.replicate (C - ((here U hm ks i).take C).length) none := rfl

theorem placeBy_snd : (placeBy C U hm v ks).2 =
    ((List.range U).flatMap fun i => (here U hm ks i).drop C).map (mk v) := rfl

/-- (1) `U` buckets. -/
theorem length_fst : (placeBy C U hm v ks).1.length = U := by
  simp [placeBy_fst]

/-- (1) Each bucket has `C` lanes. -/
theorem lanes : ∀ B ∈ (placeBy C U hm v ks).1, B.length = C := by
  intro B hB
  rw [placeBy_fst] at hB
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hB
  simp only [List.length_append, List.length_map, List.length_replicate]
  have := List.length_take_le C (here U hm ks i)
  omega

/-- Bucket `i < U`'s records: the first `C` keys of home `i`. -/
theorem recs_getD {i : Nat} (hi : i < U) :
    ((placeBy C U hm v ks).1.getD i []).recs = ((here U hm ks i).take C).map (mk v) := by
  rw [placeBy_fst, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  exact bucket_recs v _ _

/-- (3) Bucket `i` holds only records of home `i`. -/
theorem home {i : Nat} (hi : i < U) :
    ∀ r ∈ ((placeBy C U hm v ks).1.getD i []).recs, hm r.key % U = i := by
  intro r hr
  rw [recs_getD C U hm v ks hi] at hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
  have := (List.mem_filter.1 (List.mem_of_mem_take hx)).2
  simpa using this

/-- (4) A tier record's home bucket is full. -/
theorem tierFull :
    ∀ r ∈ (placeBy C U hm v ks).2, ((placeBy C U hm v ks).1.getD (hm r.key % U) []).recs.length = C := by
  intro r hr
  rw [placeBy_snd] at hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
  obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.1 hx
  have hxh : x ∈ here U hm ks i := List.mem_of_mem_drop hxi
  have hhome : hm x % U = i := by simpa [here] using (List.mem_filter.1 hxh).2
  have hlen : C < (here U hm ks i).length := by
    have := List.length_pos_of_mem hxi
    rw [List.length_drop] at this
    omega
  show ((placeBy C U hm v ks).1.getD (hm x % U) []).recs.length = C
  rw [hhome, recs_getD C U hm v ks (List.mem_range.1 hi), List.length_map, List.length_take]
  omega

/-- (2) The records, buckets then tier, are a permutation of `ks`'s records. -/
theorem all_perm (hU : 0 < U) :
    ((placeBy C U hm v ks).1.flatMap Bucket.recs ++ (placeBy C U hm v ks).2).Perm
      (ks.map (mk v)) := by
  have h1 : (placeBy C U hm v ks).1.flatMap Bucket.recs =
      ((List.range U).flatMap fun i => (here U hm ks i).take C).map (mk v) := by
    rw [placeBy_fst, List.flatMap_map, List.map_flatMap]
    simp only [bucket_recs]
  rw [h1, placeBy_snd, ← List.map_append]
  refine List.Perm.map _ ?_
  refine (List.flatMap_append_perm _ _ _).trans ?_
  simp only [List.take_append_drop]
  exact flatMap_filter_perm U hU hm ks

/-- (2) The keys, buckets then tier, are a permutation of `ks`. -/
theorem keys_perm (hU : 0 < U) :
    (((placeBy C U hm v ks).1.flatMap Bucket.recs ++ (placeBy C U hm v ks).2).map Rec.key).Perm
      ks := by
  have h := (all_perm C U hm v ks hU).map Rec.key
  have e : (ks.map (mk v)).map Rec.key = ks := by simp [List.map_map, Function.comp_def]
  rw [e] at h
  exact h

end

/-- Two canonical producers meet the structural input contract. -/
theorem shape (g : Geom) (wOld w : Model.LogicalKey → Nat) (vA vB : Nat) (ksA ksB : List Model.LogicalKey)
    (hA : ksA.Nodup) (hB : ksB.Nodup) :
    InputShape g wOld w ⟨(placeBy g.C g.U wOld vA ksA).1, (placeBy g.C g.U wOld vA ksA).2,
      (placeBy g.C g.U w vB ksB).1, (placeBy g.C g.U w vB ksB).2⟩ := by
  have hU : 0 < g.U := Nat.two_pow_pos _
  exact
    { aLen := length_fst _ _ _ _ _
      aLanes := lanes _ _ _ _ _
      bLen := length_fst _ _ _ _ _
      bLanes := lanes _ _ _ _ _
      aNodup := (keys_perm g.C g.U wOld vA ksA hU).nodup_iff.2 hA
      bNodup := (keys_perm g.C g.U w vB ksB hU).nodup_iff.2 hB
      aHome := fun _ hi => home g.C g.U wOld vA ksA hi
      bHome := fun _ hi => home g.C g.U w vB ksB hi
      aTierFull := tierFull g.C g.U wOld vA ksA
      bTierFull := tierFull g.C g.U w vB ksB }

/-- `canonOld KA o` reads `o` on `KA`, so the old-home vector determines `o`. -/
theorem canonOld_iff (g : Geom) (KA : Finset Model.LogicalKey) (o o' : KA → Fin g.U) :
    (∀ x : KA, canonOld KA o' x % g.U = o x) ↔ o' = o := by
  have hc : ∀ (o : KA → Fin g.U) (x : KA), canonOld KA o x = o x := by
    intro o x
    simp [canonOld, x.2]
  constructor
  · intro h
    funext x
    apply Fin.ext
    have := h x
    rwa [hc, Nat.mod_eq_of_lt (o' x).2] at this
  · rintro rfl x
    rw [hc, Nat.mod_eq_of_lt (o' x).2]

end RebuildBound.CanonLemmas

open RebuildBound.Model RebuildBound.CanonLemmas in
open scoped ENNReal NNReal in
/-- **Canon.** The canonical law meets `InputLaw` with `D = 1` at every
population size within `λ U`. -/
theorem RebuildBound.Canonical : RebuildBound.Model.Canonical_statement := by
  intro g KA KB W lam hW hA hB
  have hU : 0 < g.U := Nat.two_pow_pos _
  have hUpow : ((g.U : ℝ≥0∞) ^ KA.card) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hU.ne')
  have hUtop : ((g.U : ℝ≥0∞) ^ KA.card) ≠ ∞ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  refine ⟨?_, ?_, ?_, ?_, hW, hA, hB, ?_⟩
  · -- weight_sum
    show ∑ _o : KA → Fin g.U, ((g.U : ℝ≥0∞) ^ KA.card)⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
    exact ENNReal.mul_inv_cancel hUpow hUtop
  · -- shape
    intro o h
    exact shape g _ _ 0 1 _ _ (Finset.sort_nodup _ _) (Finset.sort_nodup _ _)
  · -- aKeys
    intro o
    exact (List.toFinset_eq_of_perm _ _
      (keys_perm g.C g.U (canonOld KA o) 0 (KA.sort (· ≤ ·)) hU)).trans (Finset.sort_toFinset _ _)
  · -- bKeys
    intro o h
    exact (List.toFinset_eq_of_perm _ _
      (keys_perm g.C g.U (JobLaw.wordFn (canonicalLaw g KA KB W) h) 1 (KB.sort (· ≤ ·)) hU)).trans
      (Finset.sort_toFinset _ _)
  · -- density
    intro o
    refine (Finset.sum_eq_single_of_mem o ?_ ?_).trans_le ?_
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (canonOld_iff g KA o o).2 rfl⟩
    · exact fun b hb hne => absurd ((canonOld_iff g KA o b).1 (Finset.mem_filter.1 hb).2) hne
    show ((g.U : ℝ≥0∞) ^ KA.card)⁻¹ ≤ ((1 : ℝ≥0) : ℝ≥0∞) / (g.U : ℝ≥0∞) ^ KA.card
    simp

namespace RebuildBound.CanonLemmas

open RebuildBound.Model

/-- The geometry of the large-population check: `C = 64`, `k = 1` (`U = 2`). -/
def gBig : RebuildBound.Model.Geom := { C := 64, k := 1, lo := 0, poolSlots := 0 }

/-- **A large population has a law.** With `C = 64`, `U = 2` and
`λ = 65`, a job whose B population has `129` keys (more than `C` plus any
tier capacity below `65`; `129 ≤ λ U = 130`) has a law meeting `InputLaw`:
the canonical one, with `A` empty and `W = 2`. Not registered. -/
theorem big_population :
    gBig.C = 64 ∧ gBig.U = 2 ∧
      ∃ L : JobLaw gBig, L.KB.card = 129 ∧ InputLaw L 65 1 := by
  have hinj : Function.Injective LogicalKey.ofNat := fun a b h => by
    simpa only [LogicalKey.toNat_ofNat] using congrArg LogicalKey.toNat h
  have hcard : ((Finset.range 129).image LogicalKey.ofNat).card = 129 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  refine ⟨rfl, rfl, canonicalLaw gBig ∅ ((Finset.range 129).image LogicalKey.ofNat) 2,
    hcard, RebuildBound.Canonical gBig ∅ ((Finset.range 129).image LogicalKey.ofNat)
      2 65 (by decide) (by simp) ?_⟩
  rw [hcard]
  norm_num [gBig, Geom.U]


end RebuildBound.CanonLemmas
