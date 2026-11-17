import Mathlib
import RebuildBound.Spec.WordLocality
import RebuildBound.Proofs.S05

/-!
# WordLocalS: the separated job reads its word only at its records' keys

`sJob engineRule g w inp` depends on `w` only at the keys of `inp.aAll ++ inp.bAll`.

Write `P r` for `w r.key = w' r.key`. Every phase is shown, for a state whose
records all satisfy `P`, to (a) compute the same result under `w` and `w'` and
(b) produce a state whose records all satisfy `P` again. For the engine's rule
(b) holds unconditionally: `pick`, `pickClass`, `fill`, `clear` and the filters
only move or drop records. The two facts are threaded together through every
fold (`foldl_wl`). The radix congruence is `S05.radixSplit_congr`.
-/

namespace RebuildBound.WordLocalS

open RebuildBound.Model RebuildBound.Spec

/-! ### Record predicates on the state's containers -/

section Pred

variable (P : Rec → Prop)

/-- Every record of a bucket satisfies `P`. -/
def BP (B : Bucket) : Prop := ∀ r, some r ∈ B → P r

/-- Every record of every bucket satisfies `P`. -/
def MP (M : List Bucket) : Prop := ∀ B ∈ M, BP P B

/-- Every record of a list satisfies `P`. -/
def RP (L : List Rec) : Prop := ∀ r ∈ L, P r

/-- Every record of every list satisfies `P`. -/
def LP (L : List (List Rec)) : Prop := ∀ s ∈ L, RP P s

variable {P}

theorem getD_mem_or {α : Type} (l : List α) (i : Nat) (d : α) :
    l.getD i d ∈ l ∨ l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => right; rfl
  | some a => left; exact List.mem_of_getElem? h

theorem BP_nil : BP P ([] : Bucket) := fun _ h => by simp at h

theorem RP_nil : RP P [] := fun _ h => by simp at h

theorem MP_getD {M : List Bucket} (h : MP P M) (i : Nat) : BP P (M.getD i []) := by
  rcases getD_mem_or M i [] with hm | hm
  · exact h _ hm
  · rw [hm]; exact BP_nil

theorem LP_getD {L : List (List Rec)} (h : LP P L) (i : Nat) : RP P (L.getD i []) := by
  rcases getD_mem_or L i [] with hm | hm
  · exact h _ hm
  · rw [hm]; exact RP_nil

theorem MP_set {M : List Bucket} (h : MP P M) {B : Bucket} (hB : BP P B) (i : Nat) :
    MP P (M.set i B) := by
  intro X hX
  rcases List.mem_or_eq_of_mem_set hX with hX | hX
  · exact h X hX
  · rw [hX]; exact hB

theorem LP_set {L : List (List Rec)} (h : LP P L) {s : List Rec} (hs : RP P s) (i : Nat) :
    LP P (L.set i s) := by
  intro X hX
  rcases List.mem_or_eq_of_mem_set hX with hX | hX
  · exact h X hX
  · rw [hX]; exact hs

theorem RP_append {L L' : List Rec} (h : RP P L) (h' : RP P L') : RP P (L ++ L') := by
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact h r hr
  · exact h' r hr

theorem RP_filter {L : List Rec} (h : RP P L) (q : Rec → Bool) : RP P (L.filter q) :=
  fun r hr => h r (List.mem_of_mem_filter hr)

theorem RP_take {L : List Rec} (h : RP P L) (n : Nat) : RP P (L.take n) :=
  fun r hr => h r (List.mem_of_mem_take hr)

theorem LP_flatten {L : List (List Rec)} (h : LP P L) : RP P L.flatten := by
  intro r hr
  obtain ⟨s, hs, hr⟩ := List.mem_flatten.1 hr
  exact h s hs r hr

theorem BP_recs {B : Bucket} : BP P B ↔ RP P B.recs := by
  simp [BP, RP, Bucket.recs]

theorem BP_mapFilter {B : Bucket} (h : BP P B) (q : Rec → Bool) :
    BP P (B.map fun s => s.filter q) := by
  intro r hr
  obtain ⟨s, hs, e⟩ := List.mem_map.1 hr
  have := (Option.filter_eq_some_iff.1 e).1
  subst this
  exact h r hs

theorem fill_BP : ∀ (B : Bucket) (L : List Rec), BP P B → RP P L →
    BP P (fill B L).1 ∧ RP P (fill B L).2
  | [], L, _, hL => ⟨BP_nil, hL⟩
  | some x :: B, L, hB, hL => by
    have ih := fill_BP B L (fun r hr => hB r (List.mem_cons_of_mem _ hr)) hL
    refine ⟨?_, ih.2⟩
    intro r hr
    rcases List.mem_cons.1 hr with e | hr
    · exact hB r (by rw [e]; exact List.mem_cons_self)
    · exact ih.1 r hr
  | none :: B, [], hB, _ => ⟨hB, RP_nil⟩
  | none :: B, y :: L, hB, hL => by
    have ih := fill_BP B L (fun r hr => hB r (List.mem_cons_of_mem _ hr))
      (fun r hr => hL r (List.mem_cons_of_mem _ hr))
    refine ⟨?_, ih.2⟩
    intro r hr
    rcases List.mem_cons.1 hr with e | hr
    · cases e; exact hL _ List.mem_cons_self
    · exact ih.1 r hr

theorem pick_RP (dir : Rec → Bool) : ∀ (S : List Rec) (n0 n1 : Nat), RP P S →
    RP P (pick dir n0 n1 S).1 ∧ RP P (pick dir n0 n1 S).2.1 ∧ RP P (pick dir n0 n1 S).2.2
  | [], _, _, _ => ⟨RP_nil, RP_nil, RP_nil⟩
  | r :: S, n0, n1, h => by
    have hr : P r := h r List.mem_cons_self
    have ih := fun a b => pick_RP dir S a b (fun x hx => h x (List.mem_cons_of_mem _ hx))
    by_cases hd : dir r = true <;> cases n0 <;> cases n1 <;>
      simp only [pick, hd, RP, List.forall_mem_cons, Bool.false_eq_true, ite_true,
        ite_false] at ih ⊢ <;>
      refine ⟨?_, ?_, ?_⟩ <;>
      first
        | exact (ih _ _).1 | exact (ih _ _).2.1 | exact (ih _ _).2.2
        | exact ⟨hr, (ih _ _).1⟩ | exact ⟨hr, (ih _ _).2.1⟩ | exact ⟨hr, (ih _ _).2.2⟩

theorem pickClass_RP (cls : Rec → Nat) : ∀ (S : List Rec) (n : Nat → Nat), RP P S →
    RP P (pickClass cls n S).1 ∧ RP P (pickClass cls n S).2
  | [], _, _ => ⟨RP_nil, RP_nil⟩
  | x :: S, n, h => by
    have hx : P x := h x List.mem_cons_self
    have ih := fun m => pickClass_RP cls S m (fun y hy => h y (List.mem_cons_of_mem _ hy))
    unfold pickClass
    split_ifs
    · exact ⟨(ih _).1, fun r hr => by
        rcases List.mem_cons.1 hr with e | hr
        · rw [e]; exact hx
        · exact (ih _).2 r hr⟩
    · exact ⟨fun r hr => by
        rcases List.mem_cons.1 hr with e | hr
        · rw [e]; exact hx
        · exact (ih _).1 r hr, (ih _).2⟩

end Pred

/-! ### Folds that carry an invariant and a congruence together -/

theorem foldl_wl {α β : Type} (Inv : α → Prop) (f f' : α → β → α) :
    ∀ (l : List β) (a : α), (∀ a b, b ∈ l → Inv a → f a b = f' a b ∧ Inv (f a b)) → Inv a →
      l.foldl f a = l.foldl f' a ∧ Inv (l.foldl f a)
  | [], _, _, h => ⟨rfl, h⟩
  | b :: l, a, hs, h => by
    obtain ⟨e, h1⟩ := hs a b List.mem_cons_self h
    simp only [List.foldl_cons]
    rw [← e]
    exact foldl_wl Inv f f' l (f a b) (fun a b hb ha => hs a b (List.mem_cons_of_mem _ hb) ha) h1

theorem foldl_inv {α β : Type} (Inv : α → Prop) (f : α → β → α) :
    ∀ (l : List β) (a : α), (∀ a b, b ∈ l → Inv a → Inv (f a b)) → Inv a → Inv (l.foldl f a)
  | [], _, _, h => h
  | b :: l, a, hs, h => by
    simp only [List.foldl_cons]
    exact foldl_inv Inv f l (f a b) (fun a b hb ha => hs a b (List.mem_cons_of_mem _ hb) ha)
      (hs a b List.mem_cons_self h)

/-! ### The engine's merge-split -/

theorem pick_congr (dir dir' : Rec → Bool) :
    ∀ (S : List Rec) (n0 n1 : Nat), (∀ r ∈ S, dir r = dir' r) →
      pick dir n0 n1 S = pick dir' n0 n1 S
  | [], _, _, _ => rfl
  | r :: S, n0, n1, h => by
    have hr := h r List.mem_cons_self
    have ih := fun n0 n1 =>
      pick_congr dir dir' S n0 n1 (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases n0 <;> cases n1 <;> simp only [pick, hr, ih]

theorem engineSplit_congr (C : Nat) (dir dir' : Rec → Bool) (F S : Bucket)
    (hF : ∀ r, some r ∈ F → dir r = dir' r) (hS : ∀ r, some r ∈ S → dir r = dir' r) :
    engineSplit C dir F S = engineSplit C dir' F S := by
  have h0 : F.map (fun s => s.filter fun r => !dir r) =
      F.map (fun s => s.filter fun r => !dir' r) := by
    apply List.map_congr_left
    intro s hs; cases s with
    | none => rfl
    | some x => simp [Option.filter, hF x hs]
  have h1 : F.map (fun s => s.filter dir) = F.map (fun s => s.filter dir') := by
    apply List.map_congr_left
    intro s hs; cases s with
    | none => rfl
    | some x => simp [Option.filter, hF x hs]
  have hS' : ∀ r ∈ S.recs, dir r = dir' r := fun r hr => hS r (by simpa [Bucket.recs] using hr)
  unfold engineSplit
  simp only [h0, h1, pick_congr dir dir' (Bucket.recs S) _ _ hS']

theorem engineSplit_BP {P : Rec → Prop} (C : Nat) (dir : Rec → Bool) (F S : Bucket)
    (hF : BP P F) (hS : BP P S) :
    BP P (engineSplit C dir F S).1 ∧ BP P (engineSplit C dir F S).2.1 ∧
      RP P (engineSplit C dir F S).2.2 := by
  unfold engineSplit
  have hp := fun a b => pick_RP (P := P) dir (Bucket.recs S) a b (BP_recs.1 hS)
  exact ⟨(fill_BP _ _ (BP_mapFilter hF _) (hp _ _).1).1,
    (fill_BP _ _ (BP_mapFilter hF _) (hp _ _).2.1).1, (hp _ _).2.2⟩

/-- `w` and `w'` agree at the record's key. -/
def Agr (w w' : Model.LogicalKey → Nat) (r : Rec) : Prop := w r.key = w' r.key

/-! ### Phases 1 and 2: A's route -/

/-- The route state's records all satisfy `P`. -/
def RInv (P : Rec → Prop) (st : SRoute) : Prop := MP P st.main ∧ LP P st.stash ∧ RP P st.radix

theorem sPairStep_wl (g : SepGeom) (w w' : Model.LogicalKey → Nat) (j i : Nat) (st : SRoute)
    (h : RInv (Agr w w') st) :
    sPairStep engineRule g w j i st = sPairStep engineRule g w' j i st ∧
      RInv (Agr w w') (sPairStep engineRule g w j i st) := by
  obtain ⟨hm, hs, hr⟩ := h
  have hd : ∀ (B : Bucket), BP (Agr w w') B → ∀ r, some r ∈ B → dirBit w j r = dirBit w' j r :=
    fun B hB r hr => by simp only [dirBit, show w r.key = w' r.key from hB r hr]
  have he := engineSplit_congr g.C (dirBit w j) (dirBit w' j) (st.main.getD i [])
    (st.main.getD (i + 2 ^ j) []) (hd _ (MP_getD hm i)) (hd _ (MP_getD hm _))
  have hi := engineSplit_BP g.C (dirBit w j) _ _ (MP_getD hm i) (MP_getD hm (i + 2 ^ j))
  refine ⟨?_, ?_⟩
  · simp only [sPairStep, engineRule, he]
  · exact ⟨MP_set (MP_set hm hi.1 _) hi.2.1 _, LP_set hs (RP_append (LP_getD hs j) hi.2.2) _, hr⟩

theorem runSOps_wl (g : SepGeom) (w w' : Model.LogicalKey → Nat) (ops : List (Nat × Nat)) (st : SRoute)
    (h : RInv (Agr w w') st) :
    runSOps engineRule g w ops st = runSOps engineRule g w' ops st ∧
      RInv (Agr w w') (runSOps engineRule g w ops st) :=
  foldl_wl _ _ _ ops st (fun a o _ ha => sPairStep_wl g w w' o.1 o.2 a ha) h

theorem radixOutput_BP {P : Rec → Prop} (cls : Rec → Nat) (X : List Bucket) (hX : MP P X)
    (a : Nat) : BP P (radixOutput cls X a).1 := by
  unfold radixOutput
  refine foldl_inv (fun acc : Bucket × List Nat => BP P acc.1) _ _ _ ?_ ?_
  · intro acc i _ hacc
    dsimp only
    split_ifs
    · exact hacc
    · exact (fill_BP _ _ hacc (RP_filter (BP_recs.1 (MP_getD hX i)) _)).1
  · exact BP_mapFilter (MP_getD hX a) _

theorem radixSplit_BP {P : Rec → Prop} (cls : Rec → Nat) (X : List Bucket) (hX : MP P X) :
    MP P (radixSplit cls X).1 ∧ RP P (radixSplit cls X).2 := by
  unfold radixSplit
  dsimp only
  constructor
  · intro B hB
    simp only [List.map_map, List.mem_map] at hB
    obtain ⟨a, _, rfl⟩ := hB
    exact radixOutput_BP cls X hX a
  · intro r hr
    obtain ⟨i, _, hr⟩ := List.mem_flatMap.1 hr
    exact (pickClass_RP cls _ _ (BP_recs.1 (MP_getD hX i))).2 r hr

theorem radixStep_wl (g : SepGeom) (w w' : Model.LogicalKey → Nat) (p : Nat) (st : SRoute)
    (h : RInv (Agr w w') st) :
    radixStep g w p st = radixStep g w' p st ∧ RInv (Agr w w') (radixStep g w p st) := by
  obtain ⟨hm, hs, hr⟩ := h
  refine ⟨S05.radixStep_congr g w w' p st (fun a _ x hx => by
    rw [show w x.key = w' x.key from BP_recs.1 (MP_getD hm _) x hx]), ?_⟩
  have hX : MP (Agr w w')
      (((List.range g.r).map fun a => a * g.blk + p).map fun j => st.main.getD j []) := by
    intro B hB
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hB
    exact MP_getD hm j
  have hsp := radixSplit_BP (fun x => g.cls (w x.key)) _ hX
  refine ⟨?_, hs, RP_append hr hsp.2⟩
  refine foldl_inv (MP (Agr w w')) _ _ _ ?_ hm
  intro m q hq hm'
  exact MP_set hm' (hsp.1 _ (List.of_mem_zip hq).2) _

theorem radixPass_wl (g : SepGeom) (w w' : Model.LogicalKey → Nat) (st : SRoute) (h : RInv (Agr w w') st) :
    radixPass g w st = radixPass g w' st ∧ RInv (Agr w w') (radixPass g w st) := by
  unfold radixPass
  split_ifs
  · exact foldl_wl _ _ _ _ _ (fun a p _ ha => radixStep_wl g w w' p a ha) h
  · exact ⟨rfl, h⟩

theorem sRouteWith_wl (g : SepGeom) (w w' : Model.LogicalKey → Nat) (aMain : List Bucket)
    (ops : List (Nat × Nat)) (hA : MP (Agr w w') aMain) :
    sRouteWith engineRule g w aMain ops = sRouteWith engineRule g w' aMain ops ∧
      RInv (Agr w w') (sRouteWith engineRule g w aMain ops) := by
  have h0 : RInv (Agr w w') (sRouteInit g aMain) := by
    refine ⟨?_, ?_, RP_nil⟩
    · intro B hB
      rcases List.mem_append.1 hB with hB | hB
      · rw [List.eq_of_mem_replicate hB]; intro r hr; simp [Bucket.empty] at hr
      · exact hA B hB
    · intro s hs; rw [List.eq_of_mem_replicate hs]; exact RP_nil
  have h1 := runSOps_wl g w w' ops _ h0
  have h2 := radixPass_wl g w w' _ h1.2
  unfold sRouteWith
  rw [← h1.1]
  exact h2

/-! ### Phases 3 and 4: pool, leaves and DFS -/

theorem sPool_RP {P : Rec → Prop} (st : SRoute) (aTier : List Rec) (bTier : List (List Rec))
    (h : RInv P st) (ha : RP P aTier) : RP P (sPool st aTier bTier) :=
  RP_filter (RP_append (RP_append (LP_flatten h.2.1) h.2.2) ha) _

theorem sHome_congr (g : SepGeom) (w w' : Model.LogicalKey → Nat) (x : Rec) (hx : Agr w w' x) :
    sHome g w x = sHome g w' x := by
  unfold sHome; rw [show w x.key = w' x.key from hx]

theorem sRange_congr (g : SepGeom) (w w' : Model.LogicalKey → Nat) (x : Rec) (hx : Agr w w' x) :
    sRange g w x = sRange g w' x := by
  unfold sRange; rw [sHome_congr g w w' x hx]

theorem sLeaves_wl (g : SepGeom) (w w' : Model.LogicalKey → Nat) (pool : List Rec)
    (h : RP (Agr w w') pool) :
    sLeaves g w pool = sLeaves g w' pool ∧ LP (Agr w w') (sLeaves g w pool) := by
  have hf : ∀ v, pool.filter (fun x => sRange g w x == v) =
      pool.filter (fun x => sRange g w' x == v) :=
    fun v => List.filter_congr (fun x hx => by rw [sRange_congr g w w' x (h x hx)])
  refine ⟨by simp only [sLeaves, hf], ?_⟩
  intro s hs
  obtain ⟨v, _, rfl⟩ := List.mem_map.1 hs
  exact RP_filter h _

theorem sDfsTrace_congr (g : SepGeom) (w w' : Model.LogicalKey → Nat) (pool : List Rec)
    (h : RP (Agr w w') pool) : sDfsTrace g w pool = sDfsTrace g w' pool := by
  have hf : ∀ dd c, pool.filter (fun x => sRange g w x / 2 ^ (g.rangeBits - dd) == c) =
      pool.filter (fun x => sRange g w' x / 2 ^ (g.rangeBits - dd) == c) :=
    fun dd c => List.filter_congr (fun x hx => by rw [sRange_congr g w w' x (h x hx)])
  simp only [sDfsTrace, hf]

/-! ### Phase 5: B's insertion and the offers -/

/-- The finish state's records all satisfy `P`. -/
def FInv (P : Rec → Prop) (st : SFin) : Prop :=
  MP P st.main ∧ RP P st.ins ∧ LP P st.leaves ∧ LP P st.bcopy

theorem BP_clear {P : Rec → Prop} {B : Bucket} (h : BP P B) (p : Model.LogicalKey → Bool) :
    BP P (B.clear p) := BP_mapFilter h _

theorem sOfferA_wl (g : SepGeom) (w w' : Model.LogicalKey → Nat) (ci : Nat) (st : SFin)
    (h : FInv (Agr w w') st) :
    sOfferA g w ci st = sOfferA g w' ci st ∧ FInv (Agr w w') (sOfferA g w ci st) := by
  obtain ⟨hm, hi, hl, hb⟩ := h
  have hleaf := LP_getD hl (ci / 2 ^ g.I)
  have hc : (st.leaves.getD (ci / 2 ^ g.I) []).filter (fun x => sHome g w x == ci) =
      (st.leaves.getD (ci / 2 ^ g.I) []).filter (fun x => sHome g w' x == ci) :=
    List.filter_congr (fun x hx => by rw [sHome_congr g w w' x (hleaf x hx)])
  refine ⟨by simp only [sOfferA, hc], ?_⟩
  have hcand := RP_filter hleaf (fun x => sHome g w x == ci)
  exact ⟨MP_set hm (fill_BP _ _ (MP_getD hm ci) (RP_filter hcand _)).1 _, hi,
    LP_set hl (RP_filter hleaf _) _, hb⟩

theorem sOfferPage_wl (g : SepGeom) (w w' : Model.LogicalKey → Nat) (ci : Nat) (st : SFin) (pg : Nat)
    (h : FInv (Agr w w') st) :
    sOfferPage g w ci st pg = sOfferPage g w' ci st pg ∧
      FInv (Agr w w') (sOfferPage g w ci st pg) := by
  obtain ⟨hm, hi, hl, hb⟩ := h
  have hpage := LP_getD hb pg
  have hc : (st.bcopy.getD pg []).filter (fun x => sHome g w x == ci) =
      (st.bcopy.getD pg []).filter (fun x => sHome g w' x == ci) :=
    List.filter_congr (fun x hx => by rw [sHome_congr g w w' x (hpage x hx)])
  refine ⟨by simp only [sOfferPage, hc], ?_⟩
  have hfc := RP_filter hpage (fun x => sHome g w x == ci)
  exact ⟨MP_set hm (fill_BP _ _ (BP_clear (MP_getD hm ci) _) hfc).1 _, hi, hl,
    LP_set hb (RP_filter hpage _) _⟩

theorem sOfferB_wl (g : SepGeom) (w w' : Model.LogicalKey → Nat) (ci : Nat) (st : SFin)
    (h : FInv (Agr w w') st) :
    sOfferB g w ci st = sOfferB g w' ci st ∧ FInv (Agr w w') (sOfferB g w ci st) :=
  foldl_wl _ _ _ _ _ (fun a pg _ ha => sOfferPage_wl g w w' ci a pg ha) h

theorem offers_wl (g : SepGeom) (w w' : Model.LogicalKey → Nat) (ci : Nat) (X : SFin) (s : List Rec)
    (hX : FInv (Agr w w') X) (hs : RP (Agr w w') s) :
    (sOfferB g w ci (sOfferA g w ci X), s) = (sOfferB g w' ci (sOfferA g w' ci X), s) ∧
      (FInv (Agr w w') (sOfferB g w ci (sOfferA g w ci X)) ∧ RP (Agr w w') s) := by
  have hA := sOfferA_wl g w w' ci X hX
  have hB := sOfferB_wl g w w' ci _ hA.2
  rw [← hA.1, ← hB.1]
  exact ⟨rfl, hB.2, hs⟩

theorem sInsertBucket_wl (g : SepGeom) (w w' : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat)
    (st : SFin) (hB : MP (Agr w w') bMain) (h : FInv (Agr w w') st) :
    sInsertBucket g w bMain i st = sInsertBucket g w' bMain i st ∧
      FInv (Agr w w') (sInsertBucket g w bMain i st) := by
  unfold sInsertBucket
  dsimp only
  refine (foldl_wl (fun acc : SFin × List Rec => FInv (Agr w w') acc.1 ∧ RP (Agr w w') acc.2)
    _ _ _ _ ?_ ?_).imp (congrArg Prod.fst) And.left
  · intro acc q _ hacc
    dsimp only
    obtain ⟨⟨hm, hi, hl, hb⟩, hs⟩ := hacc
    have hBi := BP_recs.1 (MP_getD hB i)
    have hf : (bMain.getD i []).recs.filter (fun x => g.wayOf (w x.key) == q) =
        (bMain.getD i []).recs.filter (fun x => g.wayOf (w' x.key) == q) :=
      List.filter_congr (fun x hx => by rw [show w x.key = w' x.key from hBi x hx])
    rw [← hf]
    have hfill := fill_BP _ _ (MP_getD hm (i + q * g.U)) (RP_filter hBi
      (fun x => g.wayOf (w x.key) == q))
    have hsh := RP_append hs hfill.2
    refine offers_wl g w w' _ _ _ ?_ hsh
    split_ifs
    · exact ⟨MP_set hm hfill.1 _, RP_append hi hsh, hl, hb⟩
    · exact ⟨MP_set hm hfill.1 _, hi, hl, hb⟩
  · obtain ⟨hm, hi, hl, hb⟩ := h
    refine ⟨⟨?_, hi, hl, hb⟩, RP_nil⟩
    refine foldl_inv (MP (Agr w w')) _ _ _ ?_ hm
    intro m q _ hm'
    exact MP_set hm' (BP_clear (MP_getD hm' _) _) _

theorem sFinish_wl (g : SepGeom) (w w' : Model.LogicalKey → Nat) (inp : SInputs) (routed : List Bucket)
    (leaves : List (List Rec)) (hb : MP (Agr w w') inp.bMain) (hbt : LP (Agr w w') inp.bTier)
    (hr : MP (Agr w w') routed) (hl : LP (Agr w w') leaves) :
    sFinish g w inp routed leaves = sFinish g w' inp routed leaves := by
  unfold sFinish
  exact (foldl_wl _ _ _ _ _ (fun a i _ ha => sInsertBucket_wl g w w' inp.bMain i a hb ha)
    ⟨hr, RP_nil, hl, hbt⟩).1

/-! ### The reference execution and the bounded job -/

theorem sReferenceWith_wl (g : SepGeom) (w w' : Model.LogicalKey → Nat) (inp : SInputs)
    (ops : List (Nat × Nat)) (hA : MP (Agr w w') inp.aMain) (hAt : RP (Agr w w') inp.aTier)
    (hB : MP (Agr w w') inp.bMain) (hBt : LP (Agr w w') inp.bTier) :
    sReferenceWith engineRule g w inp ops = sReferenceWith engineRule g w' inp ops := by
  obtain ⟨hr1, hr2⟩ := sRouteWith_wl g w w' inp.aMain ops hA
  have hpool := sPool_RP _ inp.aTier inp.bTier hr2 hAt
  obtain ⟨hl1, hl2⟩ := sLeaves_wl g w w' _ hpool
  have hd := sDfsTrace_congr g w w' _ hpool
  have hf := sFinish_wl g w w' inp _ _ hB hBt hr2.1 hl2
  simp only [sReferenceWith, ← hr1, ← hl1, ← hd, ← hf]

theorem sJob_wl (g : SepGeom) (w w' : Model.LogicalKey → Nat) (inp : SInputs)
    (h : ∀ x ∈ inp.aAll ++ inp.bAll, w x.key = w' x.key) :
    sJob engineRule g w inp = sJob engineRule g w' inp := by
  have hm : ∀ {B : Bucket} {r : Rec}, some r ∈ B → r ∈ B.recs := by
    intro B r hr; simpa [Bucket.recs] using hr
  have hA : MP (Agr w w') inp.aMain := fun B hB r hr => h r (by
    simp only [SInputs.aAll, SInputs.bAll, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl ⟨B, hB, hm hr⟩))
  have hAt : RP (Agr w w') inp.aTier := fun r hr => h r (by
    simp only [SInputs.aAll, List.mem_append]
    exact Or.inl (Or.inr hr))
  have hB : MP (Agr w w') inp.bMain := fun B hB r hr => h r (by
    simp only [SInputs.aAll, SInputs.bAll, List.mem_append, List.mem_flatMap]
    exact Or.inr (Or.inl ⟨B, hB, hm hr⟩))
  have hBt : LP (Agr w w') inp.bTier := fun s hs r hr => h r (by
    simp only [SInputs.bAll, List.mem_append, List.mem_flatten]
    exact Or.inr (Or.inr ⟨s, hs, hr⟩))
  unfold sJob sJobWith
  rw [sReferenceWith_wl g w w' inp _ hA hAt hB hBt]

end RebuildBound.WordLocalS

/-- The separated job depends on the word only at the keys of A and B. -/
theorem RebuildBound.SJobWordLocal : RebuildBound.Spec.SJobWordLocal_statement := by
  intro g w w' inp h
  exact RebuildBound.WordLocalS.sJob_wl g w w' inp h

