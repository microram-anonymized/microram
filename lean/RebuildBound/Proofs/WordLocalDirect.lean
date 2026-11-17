import RebuildBound.Spec.WordLocality
import RebuildBound.Proofs.D1
import RebuildBound.Proofs.S05
import RebuildBound.Proofs.S12
import RebuildBound.Proofs.DirectJobB

/-!
# Word locality of the direct job

`runJob` reads the previous family's word only inside `Inputs.Valid`, at the
A-main records, and the current word only at records of A and B. The proof
carries a predicate `P` (the two words agree at the record's key) through
every phase: each step is congruent when every record in its state satisfies
`P`, and each step only moves records, so its result satisfies `P` again.

* A preparation: `RG P` on the route state (main, stage stashes, radix stash).
* B production: the producer's indices lie in the winner list
  (`DirectJobBIndices`), so every home read is at a B record; the published
  table holds B winners (`DirectJobBSuccess`).
* Distribution: filters of the pool, which holds A records.
* Finish: `FG P` on the finish state (main, insertion stash, leaves, B copy),
  through `sInsertBucket`'s clear, fill and fused offers.
-/

namespace RebuildBound.WordLocalDirectProof

open Model Model.DirectJob

/-! ### Generic folds -/

theorem steps_congr {σ α : Type} (step step' : Nat → σ → α → σ × CheckEvent)
    (Inv : σ → Prop)
    (h : ∀ o st op, Inv st → step o st op = step' o st op ∧ Inv (step o st op).1) :
    ∀ (ops : List α) (o : Nat) (st : σ), Inv st →
      stepsBounded step o st ops = stepsBounded step' o st ops ∧
      ∀ a, stepsBounded step o st ops = .ok a → Inv a
  | [], o, st, hst => ⟨rfl, fun a ha => by
      simp only [stepsBounded, Except.ok.injEq] at ha; exact ha ▸ hst⟩
  | op :: ops, o, st, hst => by
    obtain ⟨he, hi⟩ := h o st op hst
    obtain ⟨ihe, ihi⟩ := steps_congr step step' Inv h ops (o + 1) _ hi
    refine ⟨?_, ?_⟩
    · simp only [stepsBounded, ← he, ihe]
    · intro a ha
      simp only [stepsBounded] at ha
      split at ha
      · exact ihi a ha
      · simp at ha

theorem foldl_congr_inv {α β : Type} (f f' : β → α → β) (Inv : β → Prop)
    (h : ∀ b a, Inv b → f b a = f' b a ∧ Inv (f b a)) :
    ∀ (l : List α) (b : β), Inv b → l.foldl f b = l.foldl f' b ∧ Inv (l.foldl f b)
  | [], _, hb => ⟨rfl, hb⟩
  | a :: l, b, hb => by
    obtain ⟨he, hi⟩ := h b a hb
    simp only [List.foldl_cons, ← he]
    exact foldl_congr_inv f f' Inv h l _ hi

theorem foldl_inv {α β : Type} (f : β → α → β) (Inv : β → Prop)
    (h : ∀ b a, Inv b → Inv (f b a)) (l : List α) (b : β) (hb : Inv b) :
    Inv (l.foldl f b) :=
  (foldl_congr_inv f f Inv (fun b a hb => ⟨rfl, h b a hb⟩) l b hb).2

/-! ### Good records -/

section Good

variable (P : Rec → Prop)

/-- Every record of a bucket satisfies `P`. -/
def BG (B : Bucket) : Prop := ∀ x ∈ B.recs, P x

/-- Every record of a list satisfies `P`. -/
def LG (L : List Rec) : Prop := ∀ x ∈ L, P x

variable {P}

theorem set_good {γ : Type} {Q : γ → Prop} {m : List γ} (hm : ∀ B ∈ m, Q B) {a : γ}
    (ha : Q a) (i : Nat) : ∀ B ∈ m.set i a, Q B := fun B hB =>
  (List.mem_or_eq_of_mem_set hB).elim (hm B) (fun h => h ▸ ha)

theorem getD_good {γ : Type} {Q : γ → Prop} {m : List γ} (hm : ∀ B ∈ m, Q B) {d : γ}
    (hd : Q d) (i : Nat) : Q (m.getD i d) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : m[i]? with
  | none => exact hd
  | some B => exact hm B (List.mem_of_getElem? h)

theorem nil_good : LG P [] := fun _ h => by simp at h

theorem bnil_good : BG P [] := fun _ h => by simp [Bucket.recs] at h

theorem append_good {L L' : List Rec} (h : LG P L) (h' : LG P L') : LG P (L ++ L') :=
  fun x hx => (List.mem_append.1 hx).elim (h x) (h' x)

theorem filter_good {L : List Rec} (h : LG P L) (q : Rec → Bool) : LG P (L.filter q) :=
  fun x hx => h x (List.mem_filter.1 hx).1

theorem take_good {L : List Rec} (h : LG P L) (n : Nat) : LG P (L.take n) :=
  fun x hx => h x (List.mem_of_mem_take hx)

theorem flatten_good {Ls : List (List Rec)} (h : ∀ L ∈ Ls, LG P L) : LG P Ls.flatten :=
  fun x hx => by
    obtain ⟨L, hL, hx⟩ := List.mem_flatten.1 hx
    exact h L hL x hx

theorem empty_good (C : Nat) : BG P (Bucket.empty C) := fun x hx => by
  simp [Bucket.recs, Bucket.empty] at hx

theorem fill_good {B : Bucket} {L : List Rec} (hB : BG P B) (hL : LG P L) :
    BG P (fill B L).1 ∧ LG P (fill B L).2 := by
  have hp := D1Lemmas.fill_perm B L
  have hm : ∀ x, x ∈ Bucket.recs (fill B L).1 ++ (fill B L).2 → P x := fun x hx =>
    (List.mem_append.1 (hp.mem_iff.1 hx)).elim (hB x) (hL x)
  exact ⟨fun x hx => hm x (List.mem_append_left _ hx),
    fun x hx => hm x (List.mem_append_right _ hx)⟩

theorem clear_good {B : Bucket} (hB : BG P B) (p : Model.LogicalKey → Bool) : BG P (B.clear p) :=
  fun x hx => by
    rw [D1Lemmas.clear_recs] at hx
    exact hB x (List.mem_filter.1 hx).1

theorem mapFilter_good {B : Bucket} (hB : BG P B) (q : Rec → Bool) :
    BG P (B.map fun s => s.filter q) := fun x hx => by
  rw [D1Lemmas.recs_map_filter] at hx
  exact hB x (List.mem_filter.1 hx).1

theorem flatMap_good {Bs : List Bucket} (h : LG P (Bs.flatMap Bucket.recs)) :
    ∀ B ∈ Bs, BG P B := fun B hB x hx => h x (List.mem_flatMap.2 ⟨B, hB, hx⟩)

theorem good_flatMap {Bs : List Bucket} (h : ∀ B ∈ Bs, BG P B) :
    LG P (Bs.flatMap Bucket.recs) := fun x hx => by
  obtain ⟨B, hB, hx⟩ := List.mem_flatMap.1 hx
  exact h B hB x hx

theorem foldSet_good {m : List Bucket} (hm : ∀ B ∈ m, BG P B) :
    ∀ (L : List (Nat × Bucket)), (∀ e ∈ L, BG P e.2) →
      ∀ B ∈ L.foldl (fun m q => m.set q.1 q.2) m, BG P B := by
  intro L hL
  induction L generalizing m with
  | nil => exact hm
  | cons e L ih =>
    simp only [List.foldl_cons]
    exact ih (set_good hm (hL e List.mem_cons_self) e.1)
      (fun e' he' => hL e' (List.mem_cons_of_mem _ he'))

end Good

/-- The two words agree at a record's key. -/
def Agree (w w' : Model.LogicalKey → Nat) (x : Rec) : Prop := w x.key = w' x.key

/-! ### A preparation -/

/-- Every record of a route state satisfies `P`. -/
structure RG (P : Rec → Prop) (st : SRoute) : Prop where
  main : ∀ B ∈ st.main, BG P B
  stash : ∀ L ∈ st.stash, LG P L
  radix : LG P st.radix

theorem split_good {P : Rec → Prop} (C : Nat) (dir : Rec → Bool) {F S : Bucket}
    (hF : BG P F) (hS : BG P S) :
    BG P (engineRule.split C dir F S).1 ∧ BG P (engineRule.split C dir F S).2.1 ∧
      LG P (engineRule.split C dir F S).2.2 := by
  show BG P (engineSplit C dir F S).1 ∧ BG P (engineSplit C dir F S).2.1 ∧
    LG P (engineSplit C dir F S).2.2
  rw [D1Lemmas.engineSplit_eq]
  have hp := D1Lemmas.pick_perm dir S.recs ((D1Lemmas.F0 dir F).countP (·.isNone))
    ((D1Lemmas.F1 dir F).countP (·.isNone))
  have hk : LG P ((D1Lemmas.pk dir F S).1 ++ (D1Lemmas.pk dir F S).2.1 ++
      (D1Lemmas.pk dir F S).2.2) := fun x hx => hS x (hp.mem_iff.1 hx)
  refine ⟨(fill_good (mapFilter_good hF _) (fun x hx => hk x ?_)).1,
    (fill_good (mapFilter_good hF _) (fun x hx => hk x ?_)).1, fun x hx => hk x ?_⟩
  · simp [hx]
  · simp [hx]
  · simp [hx]

theorem pair_ok (g : SepGeom) (w w' : Model.LogicalKey → Nat) (j i : Nat) (st : SRoute)
    (h : RG (Agree w w') st) :
    sPairStep engineRule g w j i st = sPairStep engineRule g w' j i st ∧
      RG (Agree w w') (sPairStep engineRule g w j i st) := by
  have hF := getD_good h.main bnil_good i
  have hS := getD_good h.main bnil_good (i + 2 ^ j)
  have he : engineRule.split g.C (dirBit w j) (st.main.getD i []) (st.main.getD (i + 2 ^ j) []) =
      engineRule.split g.C (dirBit w' j) (st.main.getD i []) (st.main.getD (i + 2 ^ j) []) := by
    apply D1Lemmas.engine_valid.local_dir
    intro x hx
    have : w x.key = w' x.key :=
      (List.mem_append.1 hx).elim (hF x) (hS x)
    simp [dirBit, this]
  obtain ⟨g1, g2, g3⟩ := split_good (dir := dirBit w j) g.C hF hS
  refine ⟨by simp only [sPairStep, he], ?_, ?_, h.radix⟩
  · exact set_good (set_good h.main g1 _) g2 _
  · exact set_good h.stash (append_good (getD_good h.stash nil_good j) g3) _

theorem radix_ok (g : SepGeom) (w w' : Model.LogicalKey → Nat) (p : Nat) (st : SRoute)
    (h : RG (Agree w w') st) :
    radixStep g w p st = radixStep g w' p st ∧ RG (Agree w w') (radixStep g w p st) := by
  refine ⟨S05.radixStep_congr g w w' p st (fun a _ x hx => by
    rw [getD_good h.main bnil_good _ x hx]), ?_⟩
  let X := ((List.range g.r).map fun a => a * g.blk + p).map fun j => st.main.getD j []
  have hX : LG (Agree w w') (X.flatMap Bucket.recs) := good_flatMap (fun B hB => by
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hB
    exact getD_good h.main bnil_good j)
  have hperm := S12.radixSplit_perm (fun x => g.cls (w x.key)) X
  have hs : LG (Agree w w') ((radixSplit (fun x => g.cls (w x.key)) X).1.flatMap Bucket.recs ++
      (radixSplit (fun x => g.cls (w x.key)) X).2) := fun x hx => hX x (hperm.mem_iff.1 hx)
  refine ⟨?_, h.stash, ?_⟩
  · apply foldSet_good h.main
    intro e he
    exact flatMap_good (fun x hx => hs x (List.mem_append_left _ hx)) _ (List.of_mem_zip he).2
  · exact append_good h.radix (fun x hx => hs x (List.mem_append_right _ hx))

theorem aTransition_ok (g : Geometry) (w w' : Model.LogicalKey → Nat) (o : Nat) (st : SRoute) (op : AOp)
    (h : RG (Agree w w') st) :
    aTransition g w o st op = aTransition g w' o st op ∧
      RG (Agree w w') (aTransition g w o st op).1 := by
  cases op with
  | pair bit index =>
    obtain ⟨he, hg⟩ := pair_ok g.aTopology w w' bit index st h
    exact ⟨by simp only [aTransition, he], hg⟩
  | radix index =>
    obtain ⟨he, hg⟩ := radix_ok g.aTopology w w' index st h
    exact ⟨by simp only [aTransition, he], hg⟩

theorem prepareA_ok (g : Geometry) (w w' : Model.LogicalKey → Nat) (aMain : List Bucket)
    (h : LG (Agree w w') (aMain.flatMap Bucket.recs)) :
    prepareA g w aMain = prepareA g w' aMain ∧
      ∀ a, prepareA g w aMain = .ok a → RG (Agree w w') a := by
  have h0 : RG (Agree w w') (aInitial g aMain) := by
    refine ⟨?_, ?_, nil_good⟩
    · intro B hB
      rcases List.mem_append.1 hB with hB | hB
      · rw [(List.eq_of_mem_replicate hB)]; exact empty_good _
      · exact flatMap_good h B hB
    · intro L hL
      rw [List.eq_of_mem_replicate hL]; exact nil_good
  exact steps_congr _ _ _ (aTransition_ok g w w') (aOps g) 0 _ h0

/-! ### B production -/

theorem winners_sub : ∀ (rs : List Rec), ∀ x ∈ DirectPrefix.winners rs, x ∈ rs
  | [], x, h => by simp [DirectPrefix.winners] at h
  | r :: rs, x, h => by
    unfold DirectPrefix.winners at h
    split at h
    · exact List.mem_cons_of_mem _ (winners_sub rs x h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (winners_sub rs x h)

theorem bHomes_congr (g : Geometry) (w w' : Model.LogicalKey → Nat) (inp : DirectJob.Inputs)
    (hu : ∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup)
    (hw : LG (Agree w w') inp.bRecords) :
    bHomes g w inp = bHomes g w' inp := by
  unfold bHomes DirectGroups.groups
  apply List.map_congr_left
  intro v _
  apply List.filter_congr
  intro i hi
  have hlt := DirectJobBIndices inp hu i hi
  have hm : DirectRecords.record inp.bRecords i ∈ inp.bRecords := by
    apply winners_sub
    unfold DirectRecords.record
    rw [getElem!_pos (DirectPrefix.winners inp.bRecords) i hlt]
    exact List.getElem_mem hlt
  simp only [DirectRecords.home, DirectPrefix.cachedHome]
  rw [show w (DirectRecords.record inp.bRecords i).key = w' (DirectRecords.record inp.bRecords i).key
    from hw _ hm]

theorem buildB_congr (g : Geometry) (w w' : Model.LogicalKey → Nat) (inp : DirectJob.Inputs)
    (hu : ∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup)
    (hw : LG (Agree w w') inp.bRecords) :
    buildB g w inp = buildB g w' inp := by
  unfold buildB bRemaining
  rw [bHomes_congr g w w' inp hu hw]

theorem buildB_good (g : Geometry) (w w' : Model.LogicalKey → Nat) (inp : DirectJob.Inputs)
    (hu : ∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup)
    (hw : LG (Agree w w') inp.bRecords) (b : Table) (hb : buildB g w inp = .ok b) :
    LG (Agree w w') (b.main.flatten ++ b.tier) := by
  have hp := (DirectJobBSuccess g w inp b hu hb).1
  exact fun x hx => hw x (winners_sub _ x (hp.mem_iff.1 hx))

theorem bLanes_good {P : Rec → Prop} (b : Table) (h : LG P b.main.flatten) :
    ∀ B ∈ b.bLanes, BG P B := by
  intro B hB x hx
  obtain ⟨rs, hrs, rfl⟩ := List.mem_map.1 hB
  have : Bucket.recs (rs.map some ++ List.replicate (64 - rs.length) none) = rs := by
    simp [Bucket.recs, List.filterMap_append]
  rw [this] at hx
  exact h x (List.mem_flatten.2 ⟨rs, hrs, hx⟩)

/-! ### Distribution -/

theorem distributeA_congr (g : Geometry) (w w' : Model.LogicalKey → Nat) (pool : List Rec)
    (h : LG (Agree w w') pool) :
    distributeA g w pool = distributeA g w' pool := by
  unfold distributeA
  split
  · rfl
  · rename_i i r p _
    have hf : ∀ q : Nat → Bool, pool.filter (fun x => q (g.home (w x.key) / 2 ^ i)) =
        pool.filter (fun x => q (g.home (w' x.key) / 2 ^ i)) := fun q =>
      List.filter_congr (fun x hx => by rw [h x hx])
    dsimp only
    congr 1
    · apply List.map_congr_left
      intro v _
      exact hf (fun t => t == v)
    · apply List.map_congr_left
      intro e _
      rcases e with ⟨⟨d, pre⟩, o⟩
      dsimp only
      rw [hf (fun t => t / 2 ^ (r - d) == pre)]

theorem distributeA_good {P : Rec → Prop} (g : Geometry) (w : Model.LogicalKey → Nat) (pool : List Rec)
    (h : LG P pool) : ∀ L ∈ (distributeA g w pool).leaves, LG P L := by
  unfold distributeA
  split
  · intro L hL
    simp only [List.mem_singleton] at hL
    exact hL ▸ h
  · intro L hL
    obtain ⟨v, _, rfl⟩ := List.mem_map.1 hL
    exact filter_good h _

theorem distributeABounded_ok (g : Geometry) (w w' : Model.LogicalKey → Nat) (pool : List Rec)
    (h : LG (Agree w w') pool) :
    distributeABounded g w pool = distributeABounded g w' pool ∧
      ∀ leaves, distributeABounded g w pool = .ok leaves → ∀ L ∈ leaves, LG (Agree w w') L := by
  refine ⟨by unfold distributeABounded; rw [distributeA_congr g w w' pool h], ?_⟩
  intro leaves hl
  unfold distributeABounded at hl
  dsimp only at hl
  split at hl
  · simp at hl
  · simp only [Except.ok.injEq] at hl
    exact hl ▸ distributeA_good g w pool h

/-! ### Finish -/

/-- Every record of a finish state satisfies `P`. -/
structure FG (P : Rec → Prop) (st : SFin) : Prop where
  main : ∀ B ∈ st.main, BG P B
  ins : LG P st.ins
  leaves : ∀ L ∈ st.leaves, LG P L
  bcopy : ∀ L ∈ st.bcopy, LG P L

theorem offerA_ok (g : SepGeom) (w w' : Model.LogicalKey → Nat) (ci : Nat) (st : SFin)
    (h : FG (Agree w w') st) :
    sOfferA g w ci st = sOfferA g w' ci st ∧ FG (Agree w w') (sOfferA g w ci st) := by
  have hl := getD_good h.leaves nil_good (ci / 2 ^ g.I)
  have hc : (st.leaves.getD (ci / 2 ^ g.I) []).filter (fun x => sHome g w x == ci) =
      (st.leaves.getD (ci / 2 ^ g.I) []).filter (fun x => sHome g w' x == ci) :=
    List.filter_congr (fun x hx => by
      rw [sHome, sHome, show w x.key = w' x.key from hl x hx])
  refine ⟨by simp only [sOfferA, hc], ?_, h.ins, ?_, h.bcopy⟩
  · exact set_good h.main (fill_good (getD_good h.main bnil_good ci)
      (filter_good (filter_good hl _) _)).1 _
  · exact set_good h.leaves (filter_good hl _) _

theorem offerPage_ok (g : SepGeom) (w w' : Model.LogicalKey → Nat) (ci : Nat) (st : SFin) (pg : Nat)
    (h : FG (Agree w w') st) :
    sOfferPage g w ci st pg = sOfferPage g w' ci st pg ∧
      FG (Agree w w') (sOfferPage g w ci st pg) := by
  have hl := getD_good h.bcopy nil_good pg
  have hc : (st.bcopy.getD pg []).filter (fun x => sHome g w x == ci) =
      (st.bcopy.getD pg []).filter (fun x => sHome g w' x == ci) :=
    List.filter_congr (fun x hx => by
      rw [sHome, sHome, show w x.key = w' x.key from hl x hx])
  refine ⟨by simp only [sOfferPage, hc], ?_, h.ins, h.leaves, ?_⟩
  · exact set_good h.main (fill_good (clear_good (getD_good h.main bnil_good ci) _)
      (filter_good hl _)).1 _
  · exact set_good h.bcopy (filter_good hl _) _

theorem offerB_ok (g : SepGeom) (w w' : Model.LogicalKey → Nat) (ci : Nat) (st : SFin)
    (h : FG (Agree w w') st) :
    sOfferB g w ci st = sOfferB g w' ci st ∧ FG (Agree w w') (sOfferB g w ci st) :=
  foldl_congr_inv _ _ _ (fun b pg hb => offerPage_ok g w w' ci b pg hb) _ st h

/-- The fill of one way in `sInsertBucket`, with the insertion-stash test
after the last way. Returns the state and the sheds so far. -/
def insFill (g : SepGeom) (w : Model.LogicalKey → Nat) (Bi : Bucket) (i : Nat) (acc : SFin × List Rec)
    (q : Nat) : SFin × List Rec :=
  let ci := i + q * g.U
  let f := fill (acc.1.main.getD ci []) (Bi.recs.filter fun x => g.wayOf (w x.key) == q)
  let sheds := acc.2 ++ f.2
  let st := { acc.1 with main := acc.1.main.set ci f.1 }
  let st := if q + 1 = g.d then
      let ins := st.ins ++ sheds
      { st with ins := ins, trace := st.trace ++ [(.insertion, ins.length)] }
    else st
  (st, sheds)

def insStep (g : SepGeom) (w : Model.LogicalKey → Nat) (Bi : Bucket) (i : Nat) (acc : SFin × List Rec)
    (q : Nat) : SFin × List Rec :=
  (sOfferB g w (i + q * g.U) (sOfferA g w (i + q * g.U) (insFill g w Bi i acc q).1),
    (insFill g w Bi i acc q).2)

def insClear (g : SepGeom) (Bi : Bucket) (i : Nat) (st : SFin) : SFin :=
  { st with
    main := (List.range g.d).foldl
      (fun m q => m.set (i + q * g.U) ((m.getD (i + q * g.U) []).clear fun key =>
        Bi.keys.contains key))
      st.main }

theorem sInsertBucket_eq (g : SepGeom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat)
    (st : SFin) :
    sInsertBucket g w bMain i st =
      ((List.range g.d).foldl (insStep g w (bMain.getD i []) i)
        (insClear g (bMain.getD i []) i st, [])).1 := rfl

theorem insFill_ok (g : SepGeom) (w w' : Model.LogicalKey → Nat) (Bi : Bucket) (i : Nat)
    (hB : BG (Agree w w') Bi) (acc : SFin × List Rec) (q : Nat)
    (h : FG (Agree w w') acc.1 ∧ LG (Agree w w') acc.2) :
    insFill g w Bi i acc q = insFill g w' Bi i acc q ∧
      (FG (Agree w w') (insFill g w Bi i acc q).1 ∧
        LG (Agree w w') (insFill g w Bi i acc q).2) := by
  have hc : Bi.recs.filter (fun x => g.wayOf (w x.key) == q) =
      Bi.recs.filter (fun x => g.wayOf (w' x.key) == q) :=
    List.filter_congr (fun x hx => by rw [hB x hx])
  obtain ⟨f1, f2⟩ := fill_good (getD_good h.1.main bnil_good (i + q * g.U))
    (filter_good hB (fun x => g.wayOf (w x.key) == q))
  refine ⟨by simp only [insFill, hc], ?_⟩
  have hm := set_good h.1.main f1 (i + q * g.U)
  have hs := append_good h.2 f2
  simp only [insFill]
  split
  · exact ⟨⟨hm, append_good h.1.ins hs, h.1.leaves, h.1.bcopy⟩, hs⟩
  · exact ⟨⟨hm, h.1.ins, h.1.leaves, h.1.bcopy⟩, hs⟩

theorem insStep_ok (g : SepGeom) (w w' : Model.LogicalKey → Nat) (Bi : Bucket) (i : Nat)
    (hB : BG (Agree w w') Bi) (acc : SFin × List Rec) (q : Nat)
    (h : FG (Agree w w') acc.1 ∧ LG (Agree w w') acc.2) :
    insStep g w Bi i acc q = insStep g w' Bi i acc q ∧
      (FG (Agree w w') (insStep g w Bi i acc q).1 ∧
        LG (Agree w w') (insStep g w Bi i acc q).2) := by
  obtain ⟨e0, g0⟩ := insFill_ok g w w' Bi i hB acc q h
  obtain ⟨e1, g1⟩ := offerA_ok g w w' (i + q * g.U) _ g0.1
  obtain ⟨e2, g2⟩ := offerB_ok g w w' (i + q * g.U) _ g1
  refine ⟨?_, g2, g0.2⟩
  unfold insStep
  rw [e2, e1, e0]

theorem insClear_good {P : Rec → Prop} (g : SepGeom) (Bi : Bucket) (i : Nat) (st : SFin)
    (h : FG P st) : FG P (insClear g Bi i st) := by
  refine ⟨?_, h.ins, h.leaves, h.bcopy⟩
  apply foldl_inv _ (fun m : List Bucket => ∀ B ∈ m, BG P B) _ _ _ h.main
  intro m q hm
  exact set_good hm (clear_good (getD_good hm bnil_good _) _) _

theorem insertBucket_ok (g : SepGeom) (w w' : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat)
    (hB : ∀ B ∈ bMain, BG (Agree w w') B) (st : SFin) (h : FG (Agree w w') st) :
    sInsertBucket g w bMain i st = sInsertBucket g w' bMain i st ∧
      FG (Agree w w') (sInsertBucket g w bMain i st) := by
  rw [sInsertBucket_eq, sInsertBucket_eq]
  obtain ⟨e, hg⟩ := foldl_congr_inv _ _ (fun acc : SFin × List Rec =>
      FG (Agree w w') acc.1 ∧ LG (Agree w w') acc.2)
    (insStep_ok g w w' (bMain.getD i []) i (getD_good hB bnil_good i)) (List.range g.d)
    (insClear g (bMain.getD i []) i st, []) ⟨insClear_good g _ i st h, nil_good⟩
  exact ⟨by rw [e], hg.1⟩

theorem finishBounded_congr (g : Geometry) (w w' : Model.LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec))
    (hb : LG (Agree w w') (b.main.flatten ++ b.tier))
    (hm : ∀ B ∈ main, BG (Agree w w') B) (hl : ∀ L ∈ leaves, LG (Agree w w') L) :
    finishBounded g w b main leaves = finishBounded g w' b main leaves := by
  have hbl := bLanes_good b (fun x hx => hb x (List.mem_append_left _ hx))
  have h0 : FG (Agree w w') (finishInitial b main leaves) := by
    refine ⟨hm, nil_good, hl, ?_⟩
    intro L hL
    simp only [finishInitial, List.mem_singleton] at hL
    exact hL ▸ fun x hx => hb x (List.mem_append_right _ hx)
  have hi : insertBounded g w b main leaves = insertBounded g w' b main leaves := by
    unfold insertBounded
    refine (steps_congr _ _ (FG (Agree w w')) ?_ _ 0 _ h0).1
    intro o st src hst
    obtain ⟨e, hg⟩ := insertBucket_ok g.finishTopology w w' b.bLanes src hbl st hst
    exact ⟨by simp only [finishTransition, e], hg⟩
  unfold finishBounded
  rw [hi]

end RebuildBound.WordLocalDirectProof

namespace RebuildBound

open Model Model.DirectJob WordLocalDirectProof

theorem DirectJobWordLocal : Spec.DirectJobWordLocal_statement := by
  intro g oldWord oldWord' word word' inp ho hw
  have hV : inp.Valid g oldWord ↔ inp.Valid g oldWord' := by
    have hlast : (∀ ib ∈ inp.aMain.zipIdx, ∀ x ∈ ib.1.recs,
          digitHome g.K (g.digit - 1) (oldWord x.key) = ib.2) ↔
        (∀ ib ∈ inp.aMain.zipIdx, ∀ x ∈ ib.1.recs,
          digitHome g.K (g.digit - 1) (oldWord' x.key) = ib.2) := by
      have hk : ∀ ib ∈ inp.aMain.zipIdx, ∀ x ∈ ib.1.recs, oldWord x.key = oldWord' x.key :=
        fun ib hib x hx => ho x (List.mem_flatMap.2 ⟨ib.1, List.fst_mem_of_mem_zipIdx hib, hx⟩)
      constructor
      · intro h ib hib x hx; rw [← hk ib hib x hx]; exact h ib hib x hx
      · intro h ib hib x hx; rw [hk ib hib x hx]; exact h ib hib x hx
    unfold Inputs.Valid
    rw [hlast]
  have hA : LG (Agree word word') (inp.aMain.flatMap Bucket.recs) := fun x hx =>
    hw x (List.mem_append_left _ (List.mem_append_left _ hx))
  have hAT : LG (Agree word word') inp.aTier := fun x hx =>
    hw x (List.mem_append_left _ (List.mem_append_right _ hx))
  have hBR : LG (Agree word word') inp.bRecords := fun x hx => hw x (List.mem_append_right _ hx)
  unfold runJob
  by_cases hg : g.Valid
  · rw [ite_eq_right (not_not.2 hg), ite_eq_right (not_not.2 hg)]
    by_cases hv : inp.Valid g oldWord
    · rw [ite_eq_right (not_not.2 hv), ite_eq_right (not_not.2 (hV.1 hv))]
      have hu := hv.2.2.2.2.1
      have hB := buildB_congr g word word' inp hu hBR
      by_cases hd : g.digit = 1
      · rw [ite_eq_left hd, ite_eq_left hd, hB]
      · rw [ite_eq_right hd, ite_eq_right hd]
        obtain ⟨hP, hPg⟩ := prepareA_ok g word word' inp.aMain hA
        rw [← hP, ← hB]
        cases hpa : prepareA g word inp.aMain with
        | error e => rfl
        | ok a =>
          have ha := hPg a hpa
          cases hbb : buildB g word inp with
          | error e => rfl
          | ok b =>
            have hbg := buildB_good g word word' inp hu hBR b hbb
            have hpool : LG (Agree word word') (aOperational a inp.aTier b.tier) :=
              filter_good (append_good (append_good (flatten_good ha.stash) ha.radix) hAT) _
            obtain ⟨hD, hDg⟩ := distributeABounded_ok g word word' _ hpool
            simp only
            rw [← hD]
            cases hdd : distributeABounded g word (aOperational a inp.aTier b.tier) with
            | error e => rfl
            | ok leaves =>
              simp only
              rw [finishBounded_congr g word word' b a.main leaves hbg ha.main (hDg leaves hdd)]
    · rw [ite_eq_left hv, ite_eq_left (fun h => hv (hV.2 h))]
  · rw [ite_eq_left hg, ite_eq_left hg]

end RebuildBound
