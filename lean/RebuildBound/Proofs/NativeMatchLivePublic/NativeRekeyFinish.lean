import RebuildBound.Proofs.NativeMatchLivePublic.NativeRekeyLocal
import RebuildBound.Spec.NativeMatch.Jobs

namespace RebuildBound.NativeRekeyFinish
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace
open NativeMatchJobTrace NativeRekeyLocal

structure GhostRel (f : LogicalKey → LogicalKey) (p q : FinishGhost) : Prop where
  state : q.state = sfin f p.state
  groups : List.Forall₂ (List.Forall₂ (PageRel f)) p.groups q.groups

def Good (q : FinishGhost) : Prop :=
  (∀ rs ∈ q.state.bcopy, (rs.map Rec.key).Nodup) ∧
  (∀ ps ∈ q.groups, ∀ p ∈ ps, (p.bucket.recs.map Rec.key).Nodup)

theorem forall₂_getD {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (d : α) (e : β) (hd : R d e) (i : Nat) :
    R (xs.getD i d) (ys.getD i e) := by
  induction h generalizing i with
  | nil => exact hd
  | cons hxy hrest ih =>
    cases i with
    | zero => exact hxy
    | succ i => exact ih i

theorem forall₂_set {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (a : α) (b : β) (hab : R a b) (i : Nat) :
    List.Forall₂ R (xs.set i a) (ys.set i b) := by
  induction h generalizing i with
  | nil => exact List.Forall₂.nil
  | cons hxy hrest ih =>
    cases i with
    | zero => exact List.Forall₂.cons hab hrest
    | succ i => exact List.Forall₂.cons hxy (ih i)

theorem nodup_source {f : LogicalKey → LogicalKey} {p q : Page} (h : PageRel f p q)
    (hu : (q.bucket.recs.map Rec.key).Nodup) :
    (p.bucket.recs.map (fun r => f r.key)).Nodup := by
  rw [rel_bucket h,bucket_recs,List.map_map] at hu
  exact hu


theorem all_getD {α : Type} {P : α → Prop} {xs : List α}
    (h : ∀ x ∈ xs, P x) (d : α) (hd : P d) (i : Nat) : P (xs.getD i d) := by
  induction xs generalizing i with
  | nil => exact hd
  | cons x xs ih =>
    cases i with
    | zero => exact h x List.mem_cons_self
    | succ i => exact ih (fun y hy => h y (List.mem_cons_of_mem x hy)) i

theorem all_set {α : Type} {P : α → Prop} {xs : List α}
    (h : ∀ x ∈ xs, P x) (y : α) (hy : P y) (i : Nat) :
    ∀ x ∈ xs.set i y, P x := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
    cases i with
    | zero =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hy
      · exact h x (List.mem_cons_of_mem _ hx)
    | succ i =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h _ List.mem_cons_self
      · exact ih (fun z hz => h z (List.mem_cons_of_mem _ hz)) i x hx

theorem group_good (s : LogicalKey → Stored) (a : Bucket) (home : Rec → Bool) (p : Page)
    (hu : (p.bucket.recs.map Rec.key).Nodup) :
    ((groupOfferNative s a home p).2.bucket.recs.map Rec.key).Nodup := by
  dsimp only [groupOfferNative]
  rw [NativeMatchPageProof.filter_records]
  exact hu.sublist (List.filter_sublist.map Rec.key)

theorem grouped_good (s : LogicalKey → Stored) (a : Bucket) (home : Rec → Bool) (ps : List Page)
    (hu : ∀ p ∈ ps, (p.bucket.recs.map Rec.key).Nodup) :
    ∀ p ∈ (groupedOfferNative s a home ps).2, (p.bucket.recs.map Rec.key).Nodup := by
  induction ps generalizing a with
  | nil => simp [groupedOfferNative]
  | cons p ps ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact group_good s a home p (hu p List.mem_cons_self)
    · exact ih _ (fun p hp => hu p (List.mem_cons_of_mem _ hp)) q hq


theorem forall₂_all_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {P : α → Prop} {Q : β → Prop}
    (hr : ∀ x y, R x y → Q y → P x) (hq : ∀ y ∈ ys, Q y) : ∀ x ∈ xs, P x := by
  induction h with
  | nil => simp
  | cons hxy hrest ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hr _ _ hxy (hq _ List.mem_cons_self)
    · exact ih (fun y hy => hq y (List.mem_cons_of_mem _ hy)) x hx

theorem offerA_rel {f : LogicalKey → LogicalKey} {p q : FinishGhost} (h : GhostRel f p q)
    (hq : Good q) (s s' : LogicalKey → Stored) (hs : ∀ key, s' (f key)=s key)
    (g : SepGeom) (w w' : LogicalKey → Nat) (hw : ∀ key,w' (f key)=w key) (ci : Nat) :
    GhostRel f (NativeMatchJobTrace.offerANative s g w ci p)
      (NativeMatchJobTrace.offerANative s' g w' ci q) := by
  let R := ci / 2 ^ g.I
  have hgroups := forall₂_getD h.groups [] [] List.Forall₂.nil R
  have hqgroups : ∀ pg ∈ q.groups.getD R [], (pg.bucket.recs.map Rec.key).Nodup :=
    all_getD hq.2 [] (by simp) R
  have hu : ∀ pg ∈ p.groups.getD R [], (pg.bucket.recs.map (fun r => f r.key)).Nodup :=
    forall₂_all_left hgroups (fun _ _ hp hg => nodup_source hp hg) hqgroups
  have hstep := rel_offerAGroups hgroups s s' hs g w w' hw ci p.state hu
  rw [←h.state] at hstep
  exact ⟨hstep.1,forall₂_set h.groups _ _ hstep.2 R⟩

theorem offerA_good (q : FinishGhost) (hq : Good q) (s : LogicalKey → Stored)
    (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) :
    Good (NativeMatchJobTrace.offerANative s g w ci q) := by
  refine ⟨hq.1,?_⟩
  apply all_set hq.2
  apply grouped_good
  exact all_getD hq.2 [] (by simp) _


theorem default_rel (f : LogicalKey → LogicalKey) : PageRel f default default := by
  constructor
  · rfl
  · intro i hi
    change (0 : Mask).getLsbD i.val = true at hi
    simp at hi

theorem retained_native (s : LogicalKey → Stored) (a b : Page) :
    retainedPage (cacheSource (storedKeys s a.1) a.2) b s = nativePage s a b := by
  unfold retainedPage nativePage
  rw [NativeMatchRetained.1]

theorem rel_fixed {f : LogicalKey → LogicalKey} {a a' : Page} {ps qs : List Page}
    (ha : PageRel f a a') (hpages : List.Forall₂ (PageRel f) ps qs)
    (s s' : LogicalKey → Stored) (hs : ∀ key,s' (f key)=s key) (destinations : List Nat) :
    List.Forall₂ (PageRel f) (fixedNative s a ps destinations) (fixedNative s' a' qs destinations) := by
  unfold fixedNative
  induction destinations generalizing ps qs with
  | nil => exact hpages
  | cons i rest ih =>
    simp only [fixedNativeCached]
    rw [retained_native,retained_native]
    exact ih (forall₂_set hpages _ _
      (rel_native_page ha (forall₂_getD hpages default default (default_rel f) i) s s' hs) i)


theorem fold_guarded {α β Op : Type} (R : α → β → Prop) (Q : β → Prop)
    (step : α → Op → α) (step' : β → Op → β)
    (hstep : ∀ a b op, R a b → Q b → R (step a op) (step' b op))
    (hgood : ∀ b op, Q b → Q (step' b op))
    (ops : List Op) (a : α) (b : β) (hab : R a b) (hb : Q b) :
    R (ops.foldl step a) (ops.foldl step' b) ∧ Q (ops.foldl step' b) := by
  induction ops generalizing a b with
  | nil => exact ⟨hab,hb⟩
  | cons op ops ih => exact ih _ _ (hstep a b op hab hb) (hgood b op hb)

def StateGood (st : SFin) : Prop := ∀ rs ∈ st.bcopy, (rs.map Rec.key).Nodup

theorem bpage_good (st : SFin) (hu : StateGood st) (s : LogicalKey → Stored)
    (g : SepGeom) (w : LogicalKey → Nat) (ci pg : Nat) :
    StateGood (NativeMatchTrace.offerBNative s g w ci st pg) := by
  apply all_set hu
  exact (all_getD hu [] (by simp) pg).sublist (List.filter_sublist.map Rec.key)

theorem bpage_rel (f : LogicalKey → LogicalKey) (p q : SFin) (hpq : q=sfin f p)
    (hu : StateGood q) (s s' : LogicalKey → Stored) (hs : ∀ key,s' (f key)=s key)
    (g : SepGeom) (w w' : LogicalKey → Nat) (hw : ∀ key,w' (f key)=w key) (ci pg : Nat) :
    NativeMatchTrace.offerBNative s' g w' ci q pg =
      sfin f (NativeMatchTrace.offerBNative s g w ci p pg) := by
  have hnodup := all_getD hu [] (by simp) pg
  rw [hpq] at hnodup ⊢
  simp only [sfin,records_getD,List.map_map] at hnodup
  exact NativeRekeyLocal.offerB f s s' hs g w w' hw ci p pg hnodup

theorem offerB_rel {f : LogicalKey → LogicalKey} {p q : FinishGhost} (h : GhostRel f p q)
    (hq : Good q) (s s' : LogicalKey → Stored) (hs : ∀ key,s' (f key)=s key)
    (g : SepGeom) (w w' : LogicalKey → Nat) (hw : ∀ key,w' (f key)=w key) (ci : Nat) :
    GhostRel f (NativeMatchJobTrace.offerBNative s g w ci p)
      (NativeMatchJobTrace.offerBNative s' g w' ci q) := by
  have hlen : q.state.bcopy.length=p.state.bcopy.length := by rw [h.state]; simp [sfin]
  have hf := fold_guarded (fun a b => b=sfin f a) StateGood
    (NativeMatchTrace.offerBNative s g w ci) (NativeMatchTrace.offerBNative s' g w' ci)
    (fun a b pg hab hb => bpage_rel f a b hab hb s s' hs g w w' hw ci pg)
    (fun b pg hb => bpage_good b hb s' g w' ci pg)
    (List.range p.state.bcopy.length) p.state q.state h.state hq.1
  constructor
  · simpa only [NativeMatchJobTrace.offerBNative,hlen] using hf.1
  · exact h.groups

theorem offerB_good (q : FinishGhost) (hq : Good q) (s : LogicalKey → Stored)
    (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) :
    Good (NativeMatchJobTrace.offerBNative s g w ci q) := by
  refine ⟨?_,hq.2⟩
  have hf := fold_guarded (fun a b : SFin => a=b) StateGood
    (NativeMatchTrace.offerBNative s g w ci) (NativeMatchTrace.offerBNative s g w ci)
    (fun a b pg hab _ => by rw [hab])
    (fun b pg hb => bpage_good b hb s g w ci pg)
    (List.range q.state.bcopy.length) q.state q.state rfl hq.1
  exact hf.2


theorem page_buckets_rel {f : LogicalKey → LogicalKey} {ps qs : List Page}
    (h : List.Forall₂ (PageRel f) ps qs) :
    qs.map Page.bucket = (ps.map Page.bucket).map (bucket f) := by
  induction h with
  | nil => rfl
  | cons hp hrest ih => simp only [List.map_cons,rel_bucket hp,ih]

theorem bucket_pages_rel (f : LogicalKey → LogicalKey) (bs : List Bucket) :
    List.Forall₂ (PageRel f) (bs.map Page.ofBucket) ((bs.map (bucket f)).map Page.ofBucket) := by
  induction bs with
  | nil => exact List.Forall₂.nil
  | cons b bs ih => exact List.Forall₂.cons (rel_ofBucket f b) ih

theorem clear_rel {f : LogicalKey → LogicalKey} {p q : FinishGhost} (h : GhostRel f p q)
    (s s' : LogicalKey → Stored) (hs : ∀ key,s' (f key)=s key)
    (g : SepGeom) (Bi : Bucket) (i : Nat) :
    GhostRel f (NativeMatchJobTrace.clearNative s g Bi i p)
      (NativeMatchJobTrace.clearNative s' g (bucket f Bi) i q) := by
  have hp := page_buckets_rel (rel_fixed (rel_ofBucket f Bi) (bucket_pages_rel f p.state.main)
    s s' hs ((List.range g.d).map (fun v => i+v*g.U)))
  constructor
  · simp only [NativeMatchJobTrace.clearNative,h.state,sfin,hp]
  · exact h.groups

theorem clear_good (q : FinishGhost) (hq : Good q) (s : LogicalKey → Stored)
    (g : SepGeom) (Bi : Bucket) (i : Nat) :
    Good (NativeMatchJobTrace.clearNative s g Bi i q) := hq


def AccRel (f : LogicalKey → LogicalKey) (p q : FinishGhost × List Rec) : Prop :=
  GhostRel f p.1 q.1 ∧ q.2=p.2.map (rec f)

theorem wayBase_rel {f : LogicalKey → LogicalKey} {p q : FinishGhost × List Rec}
    (h : AccRel f p q) (g : SepGeom) (w w' : LogicalKey → Nat)
    (hw : ∀ key,w' (f key)=w key) (Bi : Bucket) (i way : Nat) :
    AccRel f (wayBase g w Bi i p way) (wayBase g w' (bucket f Bi) i q way) := by
  have hh : ∀ r, (g.wayOf (w' (rec f r).key)==way)=(g.wayOf (w r.key)==way) := by
    intro r
    simp only [rec,hw]
  have hc := KeyRelabel.map_filter (rec f) (fun r => g.wayOf (w r.key)==way)
    (fun r => g.wayOf (w' r.key)==way) hh Bi.recs
  have hfill (B : Bucket) (rs : List Rec) : fill (bucket f B) (rs.map (rec f)) =
      (bucket f (fill B rs).1,(fill B rs).2.map (rec f)) := KeyRelabel.fill_map (rec f) B rs
  simp only [wayBase,AccRel,h.1.state,h.2,sfin,buckets_getD,bucket_recs,hc,hfill]
  split <;> constructor
  · constructor
    · simp only [sfin,List.map_set,List.map_append,List.length_map,List.length_append]
    · exact h.1.groups
  · simp only [List.map_append]
  · constructor
    · simp only [sfin,List.map_set]
    · exact h.1.groups
  · simp only [List.map_append]

theorem wayBase_good (p : FinishGhost × List Rec) (hp : Good p.1)
    (g : SepGeom) (w : LogicalKey → Nat) (Bi : Bucket) (i way : Nat) :
    Good (wayBase g w Bi i p way).1 := by
  unfold wayBase
  split <;> exact hp

theorem way_rel {f : LogicalKey → LogicalKey} {p q : FinishGhost × List Rec}
    (h : AccRel f p q) (hq : Good q.1) (s s' : LogicalKey → Stored)
    (hs : ∀ key,s' (f key)=s key) (g : SepGeom) (w w' : LogicalKey → Nat)
    (hw : ∀ key,w' (f key)=w key) (Bi : Bucket) (i way : Nat) :
    AccRel f (wayNative s g w Bi i p way) (wayNative s' g w' (bucket f Bi) i q way) := by
  have hb := wayBase_rel h g w w' hw Bi i way
  have hgood := wayBase_good q hq g w' (bucket f Bi) i way
  have ha := offerA_rel hb.1 hgood s s' hs g w w' hw (i+way*g.U)
  have hagood := offerA_good _ hgood s' g w' (i+way*g.U)
  exact ⟨offerB_rel ha hagood s s' hs g w w' hw (i+way*g.U),hb.2⟩

theorem way_good (q : FinishGhost × List Rec) (hq : Good q.1) (s : LogicalKey → Stored)
    (g : SepGeom) (w : LogicalKey → Nat) (Bi : Bucket) (i way : Nat) :
    Good (wayNative s g w Bi i q way).1 :=
  offerB_good _ (offerA_good _ (wayBase_good q hq g w Bi i way) s g w (i+way*g.U))
    s g w (i+way*g.U)


theorem fold_good {α Op : Type} (Q : α → Prop) (step : α → Op → α)
    (hstep : ∀ a op, Q a → Q (step a op)) (ops : List Op) (a : α) (ha : Q a) :
    Q (ops.foldl step a) := by
  induction ops generalizing a with
  | nil => exact ha
  | cons op ops ih => exact ih _ (hstep a op ha)

theorem bucket_rel {f : LogicalKey → LogicalKey} {p q : FinishGhost}
    (h : GhostRel f p q) (hq : Good q) (s s' : LogicalKey → Stored)
    (hs : ∀ key,s' (f key)=s key) (g : SepGeom) (w w' : LogicalKey → Nat)
    (hw : ∀ key,w' (f key)=w key) (bMain : List Bucket) (i : Nat) :
    GhostRel f (bucketNative s g w bMain p i)
      (bucketNative s' g w' (bMain.map (bucket f)) q i) := by
  let Bi := bMain.getD i []
  have hclear := clear_rel h s s' hs g Bi i
  have hgclear := clear_good q hq s' g (bucket f Bi) i
  have hstart : AccRel f (NativeMatchJobTrace.clearNative s g Bi i p,[])
      (NativeMatchJobTrace.clearNative s' g (bucket f Bi) i q,[]) := ⟨hclear,rfl⟩
  have hf := fold_guarded (AccRel f) (fun a => Good a.1)
    (wayNative s g w Bi i) (wayNative s' g w' (bucket f Bi) i)
    (fun a b way hab hb => way_rel hab hb s s' hs g w w' hw Bi i way)
    (fun b way hb => way_good b hb s' g w' (bucket f Bi) i way)
    (List.range g.d) _ _ hstart hgclear
  simpa only [bucketNative,buckets_getD] using hf.1.1

theorem bucket_good (q : FinishGhost) (hq : Good q) (s : LogicalKey → Stored)
    (g : SepGeom) (w : LogicalKey → Nat) (bMain : List Bucket) (i : Nat) :
    Good (bucketNative s g w bMain q i) :=
  fold_good (fun a => Good a.1) (wayNative s g w (bMain.getD i []) i)
    (fun a way ha => way_good a ha s g w (bMain.getD i []) i way)
    (List.range g.d) _ (clear_good q hq s g (bMain.getD i []) i)

theorem finish_rel {f : LogicalKey → LogicalKey} {p q : FinishGhost}
    (h : GhostRel f p q) (hq : Good q) (s s' : LogicalKey → Stored)
    (hs : ∀ key,s' (f key)=s key) (g : SepGeom) (w w' : LogicalKey → Nat)
    (hw : ∀ key,w' (f key)=w key) (bMain : List Bucket) :
    GhostRel f (finishNative s g w bMain p)
      (finishNative s' g w' (bMain.map (bucket f)) q) :=
  (fold_guarded (GhostRel f) Good (bucketNative s g w bMain)
    (bucketNative s' g w' (bMain.map (bucket f)))
    (fun _ _ i hab hb => bucket_rel hab hb s s' hs g w w' hw bMain i)
    (fun b i hb => bucket_good b hb s' g w' (bMain.map (bucket f)) i)
    (List.range g.U) p q h hq).1

theorem finish_good (q : FinishGhost) (hq : Good q) (s : LogicalKey → Stored)
    (g : SepGeom) (w : LogicalKey → Nat) (bMain : List Bucket) :
    Good (finishNative s g w bMain q) :=
  fold_good Good (bucketNative s g w bMain)
    (fun a i ha => bucket_good a ha s g w bMain i) (List.range g.U) q hq

end RebuildBound.NativeRekeyFinish
