import RebuildBound.Spec.Model.TopPrep
import RebuildBound.Proofs.ListAux.Route
import RebuildBound.Proofs.ListAux.Fill
import RebuildBound.Proofs.ListAux.Pairs
import RebuildBound.Proofs.Exchange

/-!
# RouteCore: one merge-split step on `(main, stash)`

The pair steps of the three routes (`Model.pairStep`, `sPairStep`,
`tpPairStep`) are, on `(main, stash)`, definitionally one function
`coreStep rule C w j i` (`pairStep_ms`, `sPairStep_ms`, `tpPairStep_ms`, all
`rfl`); only the trace label differs. Proved once here:

* `coreMain_spec`, `coreMain_inv`: lengths and lanes kept; the new main records
  plus the shed are the old main records, so every invariant of the main
  records is kept (no hypothesis on the stashes);
* `coreMain_getD_mem`: where a record of the new main comes from;
* `coreStep_spec`: on `Shape C n m`, the shape is kept, main plus stashes is
  conserved and the other stashes are untouched;
* `coreStep_comm`: steps on disjoint pairs commute (main equal, stashes equal
  up to order);
* `fold_eq_of_split`: a stage reads only bit `j` of its records;
* `coreFold_spec`: the disjoint pairs of one bit, processed in order;
  `fold_proj` transports a fold of a model step to the core fold.
-/

namespace RebuildBound.RouteCore

open RebuildBound.Model RebuildBound.D23 RebuildBound.Exchange

/-! ### The core step -/

/-- The split of the pair `(i, i + 2^j)` by bit `j`. -/
def split (rule : CapRule) (C : Nat) (w : Model.LogicalKey → Nat) (j i : Nat) (main : List Bucket) :
    Bucket × Bucket × List Rec :=
  rule.split C (dirBit w j) (main.getD i []) (main.getD (i + 2 ^ j) [])

/-- The stash of bit `j` after the step (its length is the trace value). -/
def sj (rule : CapRule) (C : Nat) (w : Model.LogicalKey → Nat) (j i : Nat) (main : List Bucket)
    (stash : List (List Rec)) : List Rec :=
  stash.getD j [] ++ (split rule C w j i main).2.2

/-- The merge-split of the pair `(i, i + 2^j)` on `(main, stash)`. -/
def coreStep (rule : CapRule) (C : Nat) (w : Model.LogicalKey → Nat) (j i : Nat)
    (ms : List Bucket × List (List Rec)) : List Bucket × List (List Rec) :=
  ((ms.1.set i (split rule C w j i ms.1).1).set (i + 2 ^ j) (split rule C w j i ms.1).2.1,
   ms.2.set j (sj rule C w j i ms.1 ms.2))

theorem pairStep_ms (rule : CapRule) (g : Geom) (w : Model.LogicalKey → Nat) (j i : Nat) (st : RouteState) :
    ((pairStep rule g w j i st).main, (pairStep rule g w j i st).stash) =
      coreStep rule g.C w j i (st.main, st.stash) := rfl

theorem sPairStep_ms (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) (j i : Nat) (st : SRoute) :
    ((sPairStep rule g w j i st).main, (sPairStep rule g w j i st).stash) =
      coreStep rule g.C w j i (st.main, st.stash) := rfl

theorem tpPairStep_ms (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) (j i : Nat) (st : TPRoute) :
    ((tpPairStep rule g w j i st).main, (tpPairStep rule g w j i st).stash) =
      coreStep rule g.C w j i (st.main, st.stash) := rfl

theorem sFold_radix (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) (t : Nat) :
    ∀ (I : List Nat) (s : SRoute), (I.foldl (fun s i => sPairStep rule g w t i s) s).radix = s.radix
  | [], _ => rfl
  | i :: I, s => by simp only [List.foldl_cons]; rw [sFold_radix rule g w t I]; rfl

/-- A fold commutes with a projection that maps each step to a core step. -/
theorem fold_proj {σ τ α : Type} (proj : σ → τ) (step : α → σ → σ) (core : α → τ → τ)
    (h : ∀ a s, proj (step a s) = core a (proj s)) :
    ∀ (L : List α) (s : σ), proj (L.foldl (fun s a => step a s) s) =
      L.foldl (fun t a => core a t) (proj s)
  | [], _ => rfl
  | a :: L, s => by simp only [List.foldl_cons]; rw [fold_proj proj step core h L, h]

/-! ### One step -/

/-- `n` buckets of `C` lanes and `m` stashes. -/
structure Shape (C n m : Nat) (ms : List Bucket × List (List Rec)) : Prop where
  len : ms.1.length = n
  lanes : ∀ B ∈ ms.1, B.length = C
  slen : ms.2.length = m

section Step
variable {rule : CapRule} {C n m : Nat} {w : Model.LogicalKey → Nat} {j i : Nat}

/-- Main part: lengths and lanes kept; the new main records plus the shed are
the old main records. No hypothesis on the stashes. -/
theorem coreMain_spec (hv : rule.Valid) {main : List Bucket} (hlen : main.length = n)
    (hl : ∀ B ∈ main, B.length = C) (hi : i + 2 ^ j < n) (stash : List (List Rec)) :
    (coreStep rule C w j i (main, stash)).1.length = n ∧
    (∀ B ∈ (coreStep rule C w j i (main, stash)).1, B.length = C) ∧
    List.Perm ((coreStep rule C w j i (main, stash)).1.flatMap Bucket.recs ++
      (split rule C w j i main).2.2) (main.flatMap Bucket.recs) := by
  have hp2 := Nat.two_pow_pos j
  have hne : i ≠ i + 2 ^ j := by omega
  have hF := hl _ (getD_mem main i [] (by omega))
  have hS := hl _ (getD_mem main (i + 2 ^ j) [] (by omega))
  have hp := hv.perm C (dirBit w j) _ _ hF hS
  have hln := hv.lanes C (dirBit w j) _ _ hF hS
  have A1 := perm_flatMap_set Bucket.recs (main.set i (split rule C w j i main).1) (i + 2 ^ j)
    (split rule C w j i main).2.1 [] (by rw [List.length_set]; omega)
  rw [D6.getD_set_ne _ _ _ hne] at A1
  have A2 := perm_flatMap_set Bucket.recs main i (split rule C w j i main).1 [] (by omega)
  refine ⟨by simp [coreStep, hlen], ?_, ?_⟩
  · intro B hB
    rcases List.mem_or_eq_of_mem_set hB with hB | hB
    · rcases List.mem_or_eq_of_mem_set hB with hB | hB
      · exact hl B hB
      · rw [hB]; exact hln.1
    · rw [hB]; exact hln.2
  · rw [List.perm_iff_count]; intro x
    have c1 := A1.count_eq x; have c2 := A2.count_eq x; have c4 := hp.count_eq x
    simp only [coreStep, split, List.count_append] at c1 c2 c4 ⊢
    omega

/-- Main part, for an invariant of the main records: lengths and lanes kept,
and a property of every main record still holds. -/
theorem coreMain_inv (hv : rule.Valid) {main : List Bucket} (hlen : main.length = n)
    (hl : ∀ B ∈ main, B.length = C) (hi : i + 2 ^ j < n) (stash : List (List Rec))
    {P : Rec → Prop} (hP : ∀ B ∈ main, ∀ r ∈ B.recs, P r) :
    (coreStep rule C w j i (main, stash)).1.length = n ∧
    (∀ B ∈ (coreStep rule C w j i (main, stash)).1, B.length = C) ∧
    ∀ B ∈ (coreStep rule C w j i (main, stash)).1, ∀ r ∈ B.recs, P r := by
  obtain ⟨h1, h2, hM⟩ := coreMain_spec (w := w) hv hlen hl hi stash
  refine ⟨h1, h2, fun B hB r hr => ?_⟩
  obtain ⟨B', hB', hr'⟩ := List.mem_flatMap.1
    (hM.subset (List.mem_append_left _ (List.mem_flatMap.2 ⟨B, hB, hr⟩)))
  exact hP B' hB' r hr'

/-- Where a record of the new main comes from: an untouched bucket keeps its
records; the pair's two buckets hold records of the old pair, split by bit `j`. -/
theorem coreMain_getD_mem (hv : rule.Valid) {main : List Bucket} (hl : ∀ B ∈ main, B.length = C)
    (hi : i + 2 ^ j < main.length) (stash : List (List Rec)) {v : Nat} {r : Rec}
    (hr : r ∈ ((coreStep rule C w j i (main, stash)).1.getD v []).recs) :
    (v ≠ i ∧ v ≠ i + 2 ^ j ∧ r ∈ (main.getD v []).recs) ∨
    ((v = i ∧ dirBit w j r = false ∨ v = i + 2 ^ j ∧ dirBit w j r = true) ∧
      (r ∈ (main.getD i []).recs ∨ r ∈ (main.getD (i + 2 ^ j) []).recs)) := by
  have hp2 := Nat.two_pow_pos j
  have hF := hl _ (getD_mem main i [] (by omega))
  have hS := hl _ (getD_mem main (i + 2 ^ j) [] (by omega))
  have hsrc : ∀ B, B = (split rule C w j i main).1 ∨ B = (split rule C w j i main).2.1 →
      r ∈ B.recs → r ∈ (main.getD i []).recs ∨ r ∈ (main.getD (i + 2 ^ j) []).recs :=
    fun B hB hr => List.mem_append.1 ((hv.perm C (dirBit w j) _ _ hF hS).subset
      (List.mem_append_left _ (List.mem_append.2 (by
        rcases hB with rfl | rfl; exacts [.inl hr, .inr hr]))))
  simp only [coreStep] at hr
  by_cases h1 : v = i + 2 ^ j
  · subst h1
    rw [getD_set_self _ _ _ _ (by simp; omega)] at hr
    exact Or.inr ⟨Or.inr ⟨rfl, hv.dir_second C _ _ _ hF hS r hr⟩, hsrc _ (Or.inr rfl) hr⟩
  · rw [D6.getD_set_ne _ _ _ (Ne.symm h1)] at hr
    by_cases h2 : v = i
    · subst h2
      rw [getD_set_self _ _ _ _ (by omega)] at hr
      exact Or.inr ⟨Or.inl ⟨rfl, hv.dir_first C _ _ _ hF hS r hr⟩, hsrc _ (Or.inl rfl) hr⟩
    · rw [D6.getD_set_ne _ _ _ (Ne.symm h2)] at hr
      exact Or.inl ⟨h2, h1, hr⟩

/-- Whole step: shape kept, main plus stashes conserved, other stashes untouched. -/
theorem coreStep_spec (hv : rule.Valid) {ms : List Bucket × List (List Rec)} (h : Shape C n m ms)
    (hj : j < m) (hi : i + 2 ^ j < n) :
    Shape C n m (coreStep rule C w j i ms) ∧
    List.Perm ((coreStep rule C w j i ms).1.flatMap Bucket.recs ++
        (coreStep rule C w j i ms).2.flatten) (ms.1.flatMap Bucket.recs ++ ms.2.flatten) ∧
    (∀ j', j' ≠ j → (coreStep rule C w j i ms).2.getD j' [] = ms.2.getD j' []) := by
  obtain ⟨main, stash⟩ := ms
  obtain ⟨hlen, hl, hsl⟩ := h
  obtain ⟨h1, h2, hM⟩ := coreMain_spec (w := w) hv hlen hl hi stash
  have A3 := flatten_set_perm stash j (sj rule C w j i main stash) (by simp at hsl; omega)
  refine ⟨⟨h1, h2, by simp [coreStep, hsl]⟩, ?_,
    fun j' hj' => D6.getD_set_ne _ _ _ (Ne.symm hj')⟩
  rw [List.perm_iff_count]; intro x
  have c1 := hM.count_eq x; have c3 := A3.count_eq x
  simp only [coreStep, sj, List.count_append] at c1 c3 ⊢
  omega

end Step

/-! ### Disjoint pairs commute -/

section Comm
variable {rule : CapRule} {C : Nat} {w : Model.LogicalKey → Nat}

/-- A step leaves the buckets outside its pair alone. -/
theorem core_getD_ne {t i u : Nat} (ms : List Bucket × List (List Rec)) (h1 : u ≠ i)
    (h2 : u ≠ i + 2 ^ t) : (coreStep rule C w t i ms).1.getD u [] = ms.1.getD u [] := by
  simp only [coreStep]; rw [D6.getD_set_ne _ _ _ (Ne.symm h2), D6.getD_set_ne _ _ _ (Ne.symm h1)]

theorem coreStash_getD (j i j' : Nat) (ms : List Bucket × List (List Rec)) :
    (coreStep rule C w j i ms).2.getD j' [] =
      if j = j' ∧ j < ms.2.length then ms.2.getD j' [] ++ (split rule C w j i ms.1).2.2
      else ms.2.getD j' [] := by
  simp only [coreStep, sj, D6.getD_set_eq]
  split_ifs with h <;> simp_all

theorem split_coreStep {ja ia jb ib : Nat} (ms : List Bucket × List (List Rec))
    (hab : ¬Conflict (ja, ia) (jb, ib)) :
    split rule C w ja ia (coreStep rule C w jb ib ms).1 = split rule C w ja ia ms.1 := by
  unfold Conflict at hab
  simp only at hab
  unfold split
  rw [core_getD_ne _ (by omega) (by omega), core_getD_ne _ (by omega) (by omega)]

/-- Steps on disjoint pairs commute: the same main, stashes equal up to order. -/
theorem coreStep_comm (a b : Nat × Nat) (hab : ¬Conflict a b) (ms : List Bucket × List (List Rec)) :
    (coreStep rule C w a.1 a.2 (coreStep rule C w b.1 b.2 ms)).1 =
      (coreStep rule C w b.1 b.2 (coreStep rule C w a.1 a.2 ms)).1 ∧
    (coreStep rule C w a.1 a.2 (coreStep rule C w b.1 b.2 ms)).2.length =
      (coreStep rule C w b.1 b.2 (coreStep rule C w a.1 a.2 ms)).2.length ∧
    ∀ j', ((coreStep rule C w a.1 a.2 (coreStep rule C w b.1 b.2 ms)).2.getD j' []).Perm
      ((coreStep rule C w b.1 b.2 (coreStep rule C w a.1 a.2 ms)).2.getD j' []) := by
  obtain ⟨ja, ia⟩ := a
  obtain ⟨jb, ib⟩ := b
  have hba : ¬Conflict (jb, ib) (ja, ia) := fun h => hab h.symm
  have e1 := split_coreStep (rule := rule) (C := C) (w := w) ms hab
  have e2 := split_coreStep (rule := rule) (C := C) (w := w) ms hba
  refine ⟨?_, by simp [coreStep], fun j' => ?_⟩
  · simp only [coreStep] at e1 e2 ⊢
    rw [e1, e2]
    unfold Conflict at hab
    simp only at hab
    generalize split rule C w ja ia ms.1 = sa
    generalize split rule C w jb ib ms.1 = sb
    rw [List.set_comm _ _ (show ib + 2 ^ jb ≠ ia by omega),
      List.set_comm _ _ (show ib + 2 ^ jb ≠ ia + 2 ^ ja by omega),
      List.set_comm _ _ (show ib ≠ ia by omega),
      List.set_comm _ _ (show ib ≠ ia + 2 ^ ja by omega)]
  · simp only [coreStash_getD, e1, e2]
    simp only [coreStep, List.length_set]
    split_ifs <;>
      first | exact List.Perm.refl _ | exact D6.perm_append_swap _ _ _

end Comm

/-! ### Blindness: a stage reads only bit `j` of its records -/

/-- A fold of steps on disjoint pairs of bit `j`, each a function of its split,
reading buckets that agree with `M0`, is the same for two words that agree on
bit `j` of `M0`'s records. -/
theorem fold_eq_of_split {σ : Type} {rule : CapRule} (hv : rule.Valid) {C : Nat}
    {w w' : Model.LogicalKey → Nat} {j : Nat} (main : σ → List Bucket) (f f' : Nat → σ → σ)
    (hf : ∀ i s, split rule C w j i (main s) = split rule C w' j i (main s) → f i s = f' i s)
    (hm : ∀ i s u, u ≠ i → u ≠ i + 2 ^ j → (main (f i s)).getD u [] = (main s).getD u [])
    (M0 : List Bucket)
    (hbits : ∀ B ∈ M0, ∀ r ∈ B.recs, (w r.key).testBit j = (w' r.key).testBit j) :
    ∀ (I : List Nat), I.Nodup → (∀ i ∈ I, i.testBit j = false) → ∀ s : σ,
    (∀ i ∈ I, (main s).getD i [] = M0.getD i [] ∧
      (main s).getD (i + 2 ^ j) [] = M0.getD (i + 2 ^ j) []) →
    I.foldl (fun s i => f i s) s = I.foldl (fun s i => f' i s) s
  | [], _, _, _, _ => rfl
  | i :: I, hnd, hbit, s, hs => by
    simp only [List.foldl_cons]
    have hi := hs i List.mem_cons_self
    have hrec : ∀ u, ∀ r ∈ (M0.getD u []).recs, (w r.key).testBit j = (w' r.key).testBit j := by
      intro u r hr
      rcases D5.recs_getD_sub M0 u with h | h
      · rw [h] at hr; simp at hr
      · exact hbits _ h r hr
    rw [← hf i s (hv.local_dir _ _ _ _ _ fun r hr => by
      rw [hi.1, hi.2] at hr
      exact (List.mem_append.1 hr).elim (hrec _ r) (hrec _ r))]
    refine fold_eq_of_split hv main f f' hf hm M0 hbits I (List.nodup_cons.1 hnd).2
      (fun i' hi' => hbit i' (List.mem_cons_of_mem _ hi')) _ fun i' hi' => ?_
    have hne : i' ≠ i := fun h => (List.nodup_cons.1 hnd).1 (h ▸ hi')
    have b1 := hbit i List.mem_cons_self
    have b2 := hbit i' (List.mem_cons_of_mem _ hi')
    have p1 := D5.testBit_add_pow b1
    have p2 := D5.testBit_add_pow b2
    have n1 : i' ≠ i + 2 ^ j := fun h => by rw [h] at b2; simp [p1] at b2
    have n2 : i' + 2 ^ j ≠ i := fun h => by rw [h] at p2; simp [b1] at p2
    have n3 : i' + 2 ^ j ≠ i + 2 ^ j := fun h => hne (by omega)
    rw [hm _ _ _ hne n1, hm _ _ _ n2 n3]
    exact hs i' (List.mem_cons_of_mem _ hi')

/-! ### The pairs of one bit, folded -/

section Fold
variable {rule : CapRule} {C n : Nat} {w : Model.LogicalKey → Nat} {t : Nat}

/-- The pairs `I` of bit `t`, processed in order on `(main, stash)`. -/
theorem coreFold_spec (hv : rule.Valid) :
    ∀ (I : List Nat) (main : List Bucket) (stash : List (List Rec)), main.length = n →
    (∀ B ∈ main, B.length = C) → I.Nodup → (∀ i ∈ I, i + 2 ^ t < n ∧ i.testBit t = false) →
    t < stash.length →
    (I.foldl (fun ms i => coreStep rule C w t i ms) (main, stash)).1.length = n ∧
    (∀ B ∈ (I.foldl (fun ms i => coreStep rule C w t i ms) (main, stash)).1, B.length = C) ∧
    (∀ u, (∀ i ∈ I, u ≠ i ∧ u ≠ i + 2 ^ t) →
      (I.foldl (fun ms i => coreStep rule C w t i ms) (main, stash)).1.getD u [] =
        main.getD u []) ∧
    (∀ i ∈ I, (I.foldl (fun ms i => coreStep rule C w t i ms) (main, stash)).1.getD i [] =
        (split rule C w t i main).1 ∧
      (I.foldl (fun ms i => coreStep rule C w t i ms) (main, stash)).1.getD (i + 2 ^ t) [] =
        (split rule C w t i main).2.1) ∧
    ∃ X : List Rec, (I.foldl (fun ms i => coreStep rule C w t i ms) (main, stash)).2 =
        stash.set t (stash.getD t [] ++ X) ∧
      ((main.flatMap Bucket.recs : List Rec) : Multiset Rec) =
        ((I.foldl (fun ms i => coreStep rule C w t i ms) (main, stash)).1.flatMap Bucket.recs :
          Multiset Rec) + (X : Multiset Rec)
  | [], main, stash, hlen, hl, _, _, hst => by
    refine ⟨hlen, hl, fun _ _ => rfl, fun _ h => by simp at h, [], ?_, by simp⟩
    simp only [List.foldl_nil, List.append_nil]
    rw [List.getD_eq_getElem _ _ hst, List.set_getElem_self]
  | i :: I, main, stash, hlen, hl, hnd, hI, hst => by
    simp only [List.foldl_cons]
    have hi := hI i List.mem_cons_self
    obtain ⟨hl1, hl2, hM⟩ := coreMain_spec (w := w) hv hlen hl hi.1 stash
    obtain ⟨ih0, ihl, ih1, ih2, X, ih3, ih4⟩ := coreFold_spec hv I
      (coreStep rule C w t i (main, stash)).1 (coreStep rule C w t i (main, stash)).2 hl1 hl2
      (List.nodup_cons.1 hnd).2 (fun i' h => hI i' (List.mem_cons_of_mem _ h))
      (by simpa [coreStep] using hst)
    simp only [Prod.mk.eta] at ih0 ihl ih1 ih2 ih3 ih4
    have hpos := Nat.two_pow_pos t
    have hfresh : ∀ i' ∈ I, (i ≠ i' ∧ i ≠ i' + 2 ^ t) ∧
        (i + 2 ^ t ≠ i' ∧ i + 2 ^ t ≠ i' + 2 ^ t) := by
      intro i' hi'
      have hne : i ≠ i' := fun h => (List.nodup_cons.1 hnd).1 (h ▸ hi')
      have b1 := hi.2
      have b2 := (hI i' (List.mem_cons_of_mem _ hi')).2
      have p1 := D5.testBit_add_pow b1
      have p2 := D5.testBit_add_pow b2
      refine ⟨⟨hne, fun h => ?_⟩, ⟨fun h => ?_, fun h => hne (by omega)⟩⟩
      · rw [h] at b1; simp [p2] at b1
      · rw [← h] at b2; simp [p1] at b2
    have hsp : ∀ i' ∈ I, split rule C w t i' (coreStep rule C w t i (main, stash)).1 =
        split rule C w t i' main := by
      intro i' hi'
      obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hfresh i' hi'
      unfold split
      rw [core_getD_ne _ (Ne.symm a1) (Ne.symm a3), core_getD_ne _ (Ne.symm a2) (Ne.symm a4)]
    refine ⟨ih0, ihl, ?_, ?_, (split rule C w t i main).2.2 ++ X, ?_, ?_⟩
    · intro u hu
      have h0 := hu i List.mem_cons_self
      rw [ih1 u (fun i' hi' => hu i' (List.mem_cons_of_mem _ hi')), core_getD_ne _ h0.1 h0.2]
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · rw [ih1 j (fun i' hi' => (hfresh i' hi').1),
          ih1 (j + 2 ^ t) (fun i' hi' => (hfresh i' hi').2)]
        simp only [coreStep]
        refine ⟨?_, ?_⟩
        · rw [D6.getD_set_ne _ _ _ (by omega), getD_set_self _ _ _ _ (by omega)]
        · rw [getD_set_self _ _ _ _ (by simp; omega)]
      · rw [← hsp j hj]; exact ih2 j hj
    · rw [ih3]; simp only [coreStep, sj]
      rw [getD_set_self _ _ _ _ hst, List.set_set, List.append_assoc]
    · rw [← Multiset.coe_eq_coe.2 hM]
      simp only [← Multiset.coe_add]
      rw [ih4]; abel

end Fold

end RebuildBound.RouteCore
