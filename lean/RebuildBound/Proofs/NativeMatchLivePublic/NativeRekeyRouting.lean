import RebuildBound.Proofs.KeyRelabel.Jobs.Base
namespace RebuildBound.NativeRekeyRouting
open Model
def rec (e : LogicalKey → LogicalKey) (r : Rec) : Rec := { r with key := e r.key }
def records (e : LogicalKey → LogicalKey) (rs : List Rec) : List Rec := rs.map (rec e)
def bucket (e : LogicalKey → LogicalKey) (b : Bucket) : Bucket := b.map (Option.map (rec e))
def buckets (e : LogicalKey → LogicalKey) (bs : List Bucket) : List Bucket := bs.map (bucket e)
def output (e : LogicalKey → LogicalKey) (out : Output) : Output := ⟨buckets e out.main, bucket e out.tier⟩

structure Word (e : LogicalKey → LogicalKey) where
  source : LogicalKey → Nat
  target : LogicalKey → Nat
  commute : ∀ k, target (e k) = source k
instance {e} : CoeFun (Word e) (fun _ => LogicalKey → Nat) := ⟨Word.source⟩
def word (e : LogicalKey → LogicalKey) (w : Word e) := w.target
@[simp] theorem word_apply (e : LogicalKey → LogicalKey) (w : Word e) (k) :
    word e w (e k) = w k := w.commute k
structure Flag (e : LogicalKey → LogicalKey) where
  source : Rec → Bool
  target : Rec → Bool
  commute : ∀ r, target (rec e r) = source r
instance {e} : CoeFun (Flag e) (fun _ => Rec → Bool) := ⟨Flag.source⟩
def unsh (e : LogicalKey → LogicalKey) (u : Flag e) := u.target
@[simp] theorem unsh_apply (e : LogicalKey → LogicalKey) (u : Flag e) (r) :
    unsh e u (rec e r) = u r := u.commute r
@[simp] theorem rec_key (e : LogicalKey → LogicalKey) (r : Rec) : (rec e r).key = e r.key := rfl
@[simp] theorem rec_val (e : LogicalKey → LogicalKey) (r : Rec) : (rec e r).val = r.val := rfl
@[simp] theorem rec_tomb (e : LogicalKey → LogicalKey) (r : Rec) : (rec e r).tomb = r.tomb := rfl
@[simp] theorem records_length (e : LogicalKey → LogicalKey) (rs : List Rec) : (records e rs).length = rs.length := by simp [records]
@[simp] theorem bucket_length (e : LogicalKey → LogicalKey) (b : Bucket) : (bucket e b).length = b.length := by simp [bucket]
@[simp] theorem buckets_length (e : LogicalKey → LogicalKey) (bs : List Bucket) : (buckets e bs).length = bs.length := by simp [buckets]
@[simp] theorem records_nil (e : LogicalKey → LogicalKey) : records e [] = [] := rfl
@[simp] theorem bucket_nil (e : LogicalKey → LogicalKey) : bucket e [] = [] := rfl
@[simp] theorem buckets_nil (e : LogicalKey → LogicalKey) : buckets e [] = [] := rfl
@[simp] theorem records_append (e : LogicalKey → LogicalKey) (rs ss : List Rec) : records e (rs ++ ss) = records e rs ++ records e ss := by simp [records]
@[simp] theorem bucket_append (e : LogicalKey → LogicalKey) (b c : Bucket) : bucket e (b ++ c) = bucket e b ++ bucket e c := by simp [bucket]
@[simp] theorem buckets_append (e : LogicalKey → LogicalKey) (b c : List Bucket) : buckets e (b ++ c) = buckets e b ++ buckets e c := by simp [buckets]
@[simp] theorem bucket_empty (e : LogicalKey → LogicalKey) (n : Nat) : bucket e (Bucket.empty n) = Bucket.empty n := by simp [bucket, Bucket.empty]
@[simp] theorem bucket_replicate (e : LogicalKey → LogicalKey) (n : Nat) : bucket e (List.replicate n none) = List.replicate n none := by simp [bucket]
@[simp] theorem bucket_recs (e : LogicalKey → LogicalKey) (b : Bucket) : (bucket e b).recs = records e b.recs := by
  induction b with
  | nil => rfl
  | cons x xs ih => cases x <;> simp_all [bucket, Bucket.recs, records]
@[simp] theorem records_keys (e : LogicalKey → LogicalKey) (rs : List Rec) : (records e rs).map Rec.key = (rs.map Rec.key).map e := by simp [records, List.map_map, Function.comp_def]
@[simp] theorem bucket_keys (e : LogicalKey → LogicalKey) (b : Bucket) : (bucket e b).keys = b.keys.map e := by simp [Bucket.keys]
 theorem map_filter {α β : Type} (f : α → β) (p : α → Bool) (q : β → Bool)
    (h : ∀ x, q (f x) = p x) (xs : List α) : (xs.map f).filter q = (xs.filter p).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.filter_cons, h, ih]; split <;> rfl
 theorem option_filter {α β : Type} (f : α → β) (p : α → Bool) (q : β → Bool)
    (h : ∀ x, q (f x) = p x) (x : Option α) : (x.map f).filter q = (x.filter p).map f := by
  cases x with
  | none => rfl
  | some x => simp [Option.filter, h]
 theorem fill_map {α β : Type} (f : α → β) (b : List (Option α)) (rs : List α) :
    fill (b.map (Option.map f)) (rs.map f) = ((fill b rs).1.map (Option.map f), (fill b rs).2.map f) := by
  induction b generalizing rs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | none => cases rs <;> simp [fill, ih]
    | some x =>
      have h := ih rs
      cases rs <;> simp only [List.map_cons, List.map_nil, Option.map_some, fill] at * <;> rw [h]
 theorem appendFill_map {α β : Type} (f : α → β) (b : List (Option α)) (rs : List α) :
    appendFill (b.map (Option.map f)) (rs.map f) = (appendFill b rs).map (Option.map f) := by
  simp [appendFill, fill_map, List.map_map, Function.comp_def]
@[simp] theorem occupied_map {α β : Type} (f : α → β) (b : List (Option α)) :
    occupied (b.map (Option.map f)) = occupied b := by
  induction b with
  | nil => rfl
  | cons x xs ih => cases x <;> simp_all [occupied]

theorem pick_map (e : LogicalKey → LogicalKey) (dir : Flag e) (n m : Nat) (rs : List Rec) :
    pick (unsh e dir) n m (records e rs) =
      (records e (pick dir n m rs).1, records e (pick dir n m rs).2.1,
       records e (pick dir n m rs).2.2) := by
  induction rs generalizing n m with
  | nil => rfl
  | cons x xs ih =>
    simp only [records] at ih
    cases n <;> cases m <;> cases hd : dir x <;> simp [records, pick, hd, ih]
theorem engineSplit_map (e : LogicalKey → LogicalKey) (C : Nat) (dir : Flag e) (b c : Bucket) :
    engineSplit C (unsh e dir) (bucket e b) (bucket e c) =
      (bucket e (engineSplit C dir b c).1, bucket e (engineSplit C dir b c).2.1,
       records e (engineSplit C dir b c).2.2) := by
  have hm (bs : Bucket) (p : Flag e) :
      (bucket e bs).map (fun s => s.filter (unsh e p)) = bucket e (bs.map (fun s => s.filter p)) := by
    simp only [bucket, List.map_map]
    apply List.map_congr_left
    intro x hx
    exact option_filter (rec e) p (unsh e p) (unsh_apply e p) x
  have hn (bs : Bucket) : (bucket e bs).countP (·.isNone) = bs.countP (·.isNone) := by
    induction bs with
    | nil => rfl
    | cons x xs ih => cases x <;> simp_all [bucket]
  let neg : Flag e := ⟨fun r => !dir r, fun r => !unsh e dir r, fun r => by simp⟩
  have hneg : (fun r => !(unsh e dir) r) = unsh e neg := rfl
  simp only [engineSplit, hneg, hm, hn, bucket_recs, pick_map]
  simp only [bucket, records, fill_map, neg]
@[simp] theorem records_filter (e : LogicalKey → LogicalKey) (p : Rec → Bool) (xs : List Rec) :
    (records e xs).filter p = records e (xs.filter (fun r => p (rec e r))) :=
  List.filter_map

@[simp] theorem map_getD' {α β : Type} (f : α → β) (xs : List α) (n : Nat) (d : α) :
    (xs.map f).getD n (f d) = f (xs.getD n d) := by
  simp only [List.getD, List.getElem?_map]
  cases xs[n]? <;> rfl

@[simp] theorem option_map_getD' {α β : Type} (f : α → β) (x : Option α) (d : α) :
    (x.map f).getD (f d) = f (x.getD d) := by cases x <;> rfl

@[simp] theorem records_getD (e : LogicalKey → LogicalKey) (xs : List (List Rec)) (n : Nat) :
    (xs.map (records e)).getD n [] = records e (xs.getD n []) :=
  map_getD' (records e) xs n []
@[simp] theorem buckets_getD (e : LogicalKey → LogicalKey) (xs : List Bucket) (n : Nat) :
    (buckets e xs).getD n [] = bucket e (xs.getD n []) :=
  map_getD' (bucket e) xs n []
@[simp] theorem records_set (e : LogicalKey → LogicalKey) (xs : List (List Rec)) (n : Nat) (v : List Rec) :
    (xs.map (records e)).set n (records e v) = (xs.set n v).map (records e) :=
  List.map_set.symm
@[simp] theorem buckets_set (e : LogicalKey → LogicalKey) (xs : List Bucket) (n : Nat) (v : Bucket) :
    (buckets e xs).set n (bucket e v) = buckets e (xs.set n v) :=
  List.map_set.symm
@[simp] theorem records_take (e : LogicalKey → LogicalKey) (xs : List Rec) (n : Nat) :
    (records e xs).take n = records e (xs.take n) := List.map_take.symm
@[simp] theorem records_flatten (e : LogicalKey → LogicalKey) (xs : List (List Rec)) :
    (xs.map (records e)).flatten = records e xs.flatten := List.map_flatten.symm
@[simp] theorem fill_relabel (e : LogicalKey → LogicalKey) (b : Bucket) (xs : List Rec) :
    fill (bucket e b) (records e xs) = (bucket e (fill b xs).1, records e (fill b xs).2) :=
  fill_map (rec e) b xs
@[simp] theorem appendFill_relabel (e : LogicalKey → LogicalKey) (b : Bucket) (xs : List Rec) :
    appendFill (bucket e b) (records e xs) = bucket e (appendFill b xs) :=
  appendFill_map (rec e) b xs
@[simp] theorem occupied_bucket (e : LogicalKey → LogicalKey) (b : Bucket) : occupied (bucket e b) = occupied b :=
  occupied_map (rec e) b
@[simp] theorem dirBit_rec (e : LogicalKey → LogicalKey) (w : Word e) (j : Nat) (r : Rec) :
    dirBit (word e w) j (rec e r) = dirBit w j r := by simp [dirBit]
def dirFlag (e : LogicalKey → LogicalKey) (w : Word e) (j : Nat) : Flag e :=
  ⟨dirBit w j, dirBit (word e w) j, fun r => by simp [dirBit]⟩
@[simp] theorem split_relabel (e : LogicalKey → LogicalKey) (C : Nat) (w : Word e) (j : Nat)
    (b c : Bucket) : engineRule.split C (dirBit (word e w) j) (bucket e b) (bucket e c) =
      (bucket e (engineRule.split C (dirBit w j) b c).1,
       bucket e (engineRule.split C (dirBit w j) b c).2.1,
       records e (engineRule.split C (dirBit w j) b c).2.2) := by
  exact engineSplit_map e C (dirFlag e w j) b c

/-- Relabel the inputs of top preparation. -/
def tpInputs (e : LogicalKey → LogicalKey) (i : TPInputs) : TPInputs :=
  ⟨buckets e i.aMain, records e i.aTier⟩

def tpRoute (e : LogicalKey → LogicalKey) (s : TPRoute) : TPRoute :=
  ⟨buckets e s.main, s.stash.map (records e), s.trace⟩

def tpFin (e : LogicalKey → LogicalKey) (s : TPFin) : TPFin :=
  ⟨buckets e s.main, records e s.last, s.leaves.map (records e), s.trace⟩

def tpRun (e : LogicalKey → LogicalKey) (s : TPRun) : TPRun :=
  ⟨tpRoute e s.route, records e s.pool, s.leaves.map (records e), tpFin e s.fin,
    output e s.output, s.trace⟩

@[simp] theorem tpRoute_main (e : LogicalKey → LogicalKey) (s : TPRoute) : (tpRoute e s).main = buckets e s.main := rfl
@[simp] theorem tpRoute_trace (e : LogicalKey → LogicalKey) (s : TPRoute) : (tpRoute e s).trace = s.trace := rfl
@[simp] theorem tpFin_main (e : LogicalKey → LogicalKey) (s : TPFin) : (tpFin e s).main = buckets e s.main := rfl
@[simp] theorem tpFin_trace (e : LogicalKey → LogicalKey) (s : TPFin) : (tpFin e s).trace = s.trace := rfl

/-- Transport a state through a fold whose step commutes with the transport. -/
theorem foldl_transport {α β γ : Type*} (f : α → β) (a : α → γ → α)
    (b : β → γ → β) (h : ∀ s x, b (f s) x = f (a s x)) (xs : List γ) (s : α) :
    xs.foldl b (f s) = f (xs.foldl a s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons, h] using ih (a s x)

@[simp] theorem flagged_rec (e : LogicalKey → LogicalKey) (u : Flag e) (r : Rec) :
    flagged (unsh e u) (rec e r) = flagged u r := by simp [flagged]

@[simp] theorem tpHome_rec (e : LogicalKey → LogicalKey) (g : TPGeom) (w : Word e) (r : Rec) :
    tpHome g (word e w) (rec e r) = tpHome g w r := by simp [tpHome]

@[simp] theorem tpRange_rec (e : LogicalKey → LogicalKey) (g : TPGeom) (w : Word e) (r : Rec) :
    tpRange g (word e w) (rec e r) = tpRange g w r := by simp [tpRange]

@[simp] theorem copyMain_relabel (e : LogicalKey → LogicalKey) (u : Flag e) (m : List Bucket) :
    copyMain (unsh e u) (buckets e m) = buckets e (copyMain u m) := by
  simp only [copyMain, buckets, List.map_map]
  apply List.map_congr_left
  intro b hb
  simp only [Function.comp_apply, bucket, List.map_map]
  apply List.map_congr_left
  intro x hx
  apply option_filter
  intro r
  simp

@[simp] theorem initMain_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (xs : List Rec) :
    initMain g (records e xs) = buckets e (initMain g xs) := by
  simp only [initMain, buckets, bucket, records, List.map_map, Function.comp_def, List.getElem?_map]
  apply List.map_congr_left
  intro b hb
  apply List.map_congr_left
  intro l hl
  split <;> rfl

@[simp] theorem tpPairStep_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (w : Word e)
    (j i : Nat) (s : TPRoute) :
    tpPairStep engineRule g (word e w) j i (tpRoute e s) =
      tpRoute e (tpPairStep engineRule g w j i s) := by
  simp only [tpPairStep, tpRoute, buckets_getD, records_getD, split_relabel,
    ← records_append, buckets_set, records_set, records_length]

@[simp] theorem runTPOps_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (w : Word e)
    (ops : List (Nat × Nat)) (s : TPRoute) :
    runTPOps engineRule g (word e w) ops (tpRoute e s) =
      tpRoute e (runTPOps engineRule g w ops s) := by
  apply foldl_transport
  intro s x
  exact tpPairStep_relabel e g w x.1 x.2 s

@[simp] theorem tpRouteInit_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (m : List Bucket) :
    tpRouteInit g (buckets e m) = tpRoute e (tpRouteInit g m) := by
  simp [tpRouteInit, tpRoute]

@[simp] theorem tpPool_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (u : Flag e)
    (s : TPRoute) (t : List Rec) :
    tpPool g (unsh e u) (tpRoute e s) (records e t) = records e (tpPool g u s t) := by
  simp only [tpPool, tpRoute, ← List.map_take, records_flatten, ← records_append, records_filter]
  simp

@[simp] theorem tpLeaves_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (w : Word e)
    (p : List Rec) :
    tpLeaves g (word e w) (records e p) = (tpLeaves g w p).map (records e) := by
  simp [tpLeaves, List.map_map, Function.comp_def]

@[simp] theorem tpDfsTrace_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (w : Word e)
    (p : List Rec) : tpDfsTrace g (word e w) (records e p) = tpDfsTrace g w p := by
  simp [tpDfsTrace]

/-- Erasing selected occurrences commutes with a map that preserves the predicate. -/
theorem eraseFirst_map (f : Rec → Rec) (p q : Rec → Bool) (h : ∀ r, q (f r) = p r)
    (n : Nat) (xs : List Rec) : eraseFirst q n (xs.map f) = (eraseFirst p n xs).map f := by
  induction xs generalizing n with
  | nil => cases n <;> rfl
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n => simp only [List.map_cons, eraseFirst, h]; split <;> simp_all

@[simp] theorem tpOffer_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (w : Word e)
    (b : Nat) (s : TPFin) :
    tpOffer g (word e w) b (tpFin e s) = tpFin e (tpOffer g w b s) := by
  simp only [tpOffer, tpFin, buckets_getD, records_getD, records_filter, tpHome_rec, fill_relabel,
    records_length, buckets_set]
  congr 1
  rw [show eraseFirst (fun r => tpHome g (word e w) r == b) _ (records e _) = records e
    (eraseFirst (fun r => tpHome g w r == b) _ _) from
      eraseFirst_map (rec e) _ _ (fun r => by simp) _ _]
  exact records_set e _ _ _

@[simp] theorem tpLastStep_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (w : Word e)
    (i : Nat) (s : TPFin) :
    tpLastStep engineRule g (word e w) i (tpFin e s) =
      tpFin e (tpLastStep engineRule g w i s) := by
  unfold tpLastStep
  simp only [tpFin, buckets_getD, split_relabel, ← records_append, buckets_set, records_length]
  have h := tpOffer_relabel e g w i
    { main := (s.main.set i (engineRule.split g.C (dirBit w (g.k - 1))
        (s.main.getD i []) (s.main.getD (i + g.half) [])).1).set (i + g.half)
        (engineRule.split g.C (dirBit w (g.k - 1))
        (s.main.getD i []) (s.main.getD (i + g.half) [])).2.1
      last := s.last ++ (engineRule.split g.C (dirBit w (g.k - 1))
        (s.main.getD i []) (s.main.getD (i + g.half) [])).2.2
      leaves := s.leaves
      trace := s.trace ++ [(.stash (g.k - 1), (s.last ++
        (engineRule.split g.C (dirBit w (g.k - 1))
        (s.main.getD i []) (s.main.getD (i + g.half) [])).2.2).length)] }
  simpa only [tpFin] using
    (congrArg (tpOffer g (word e w) (i + g.half)) h).trans
      (tpOffer_relabel e g w (i + g.half) _)

@[simp] theorem tpFinish_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (w : Word e)
    (m : List Bucket) (ls : List (List Rec)) :
    tpFinish engineRule g (word e w) (buckets e m) (ls.map (records e)) =
      tpFin e (tpFinish engineRule g w m ls) := by
  unfold tpFinish
  change (List.range g.half).foldl _ (tpFin e ⟨m, [], ls, []⟩) = _
  apply foldl_transport
  intro s i
  exact tpLastStep_relabel e g w i s

@[simp] theorem tpDrainStep_relabel (e : LogicalKey → LogicalKey)
    (acc : List (Option Rec) × List (TPTest × Nat)) (xs : List Rec) :
    tpDrainStep (bucket e acc.1, acc.2) (records e xs) =
      (bucket e (tpDrainStep acc xs).1, (tpDrainStep acc xs).2) := by
  simp [tpDrainStep]

@[simp] theorem tpDrain_relabel (e : LogicalKey → LogicalKey) (s : TPFin) :
    tpDrain (tpFin e s) = (bucket e (tpDrain s).1, (tpDrain s).2) := by
  unfold tpDrain
  change (s.leaves.map (records e) ++ [records e s.last]).foldl _ _ = _
  rw [show s.leaves.map (records e) ++ [records e s.last] = (s.leaves ++ [s.last]).map (records e) by simp]
  rw [List.foldl_map]
  exact foldl_transport (fun (acc : Bucket × List (TPTest × Nat)) => (bucket e acc.1, acc.2))
    tpDrainStep (fun acc xs => tpDrainStep acc (records e xs)) (tpDrainStep_relabel e)
    (s.leaves ++ [s.last]) ([], [])

@[simp] theorem tpReferenceWith_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (u : Flag e)
    (w : Word e) (inp : TPInputs) (ops : List (Nat × Nat)) :
    tpReferenceWith engineRule g (unsh e u) (word e w) (tpInputs e inp) ops =
      tpRun e (tpReferenceWith engineRule g u w inp ops) := by
  unfold tpReferenceWith
  simp only [tpInputs, copyMain_relabel, tpRouteInit_relabel, runTPOps_relabel,
    tpPool_relabel, tpLeaves_relabel, tpDfsTrace_relabel]
  simp only [tpRoute_main, tpFinish_relabel, tpDrain_relabel]
  rfl

@[simp] theorem tpReference_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (u : Flag e)
    (w : Word e) (inp : TPInputs) :
    tpReference engineRule g (unsh e u) (word e w) (tpInputs e inp) =
      tpRun e (tpReference engineRule g u w inp) := by
  exact tpReferenceWith_relabel e g u w inp _

@[simp] theorem tpJobWith_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (u : Flag e)
    (w : Word e) (inp : TPInputs) (ops : List (Nat × Nat)) :
    tpJobWith engineRule g (unsh e u) (word e w) (tpInputs e inp) ops =
      (tpJobWith engineRule g u w inp ops).map (output e) := by
  simp only [tpJobWith, tpReferenceWith_relabel, tpRun]
  cases tpFirstFailure g (tpReferenceWith engineRule g u w inp ops).trace <;> rfl

@[simp] theorem tpJob_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (u : Flag e)
    (w : Word e) (inp : TPInputs) :
    tpJob engineRule g (unsh e u) (word e w) (tpInputs e inp) =
      (tpJob engineRule g u w inp).map (output e) := by
  exact tpJobWith_relabel e g u w inp _

@[simp] theorem initJob_relabel (e : LogicalKey → LogicalKey) (g : TPGeom) (w : Word e)
    (xs : List Rec) : initJob engineRule g (word e w) (records e xs) =
      (initJob engineRule g w xs).map (output e) := by
  unfold initJob
  rw [initMain_relabel]
  exact tpJob_relabel e g ⟨fun _ => false, fun _ => false, fun _ => rfl⟩ w ⟨initMain g xs, []⟩



/-- Relabel the separated job inputs and phase states. -/
def sInputs (e : LogicalKey → LogicalKey) (i : SInputs) : SInputs :=
  ⟨buckets e i.aMain, records e i.aTier, buckets e i.bMain, i.bTier.map (records e)⟩
def sRoute (e : LogicalKey → LogicalKey) (s : SRoute) : SRoute :=
  ⟨buckets e s.main, s.stash.map (records e), records e s.radix, s.trace⟩
def sFin (e : LogicalKey → LogicalKey) (s : SFin) : SFin :=
  ⟨buckets e s.main, records e s.ins, s.leaves.map (records e), s.bcopy.map (records e), s.trace⟩
def sRun (e : LogicalKey → LogicalKey) (s : SRun) : SRun :=
  ⟨sRoute e s.route, records e s.pool, s.leaves.map (records e), sFin e s.fin,
    output e s.output, s.trace⟩
def topInputs (e : LogicalKey → LogicalKey) (i : TopInputs) : TopInputs :=
  ⟨buckets e i.cMain, records e i.carry, buckets e i.bMain, records e i.bTier⟩
def finState (e : LogicalKey → LogicalKey) (s : FinState) : FinState :=
  ⟨buckets e s.main, records e s.ins, s.leaves.map (records e), records e s.bcopy, s.trace⟩
def topRun (e : LogicalKey → LogicalKey) (s : TopRun) : TopRun :=
  ⟨records e s.pool, s.leaves.map (records e), finState e s.fin, output e s.output, s.trace⟩

@[simp] theorem home_rec (e : LogicalKey → LogicalKey) (g : Geom) (w : Word e) (r : Rec) :
    home g (word e w) (rec e r) = home g w r := by simp [home]
@[simp] theorem rangeOf_rec (e : LogicalKey → LogicalKey) (g : Geom) (w : Word e) (r : Rec) :
    rangeOf g (word e w) (rec e r) = rangeOf g w r := by simp [rangeOf]
@[simp] theorem leavesOf_relabel (e : LogicalKey → LogicalKey) (g : Geom) (w : Word e) (p : List Rec) :
    leavesOf g (word e w) (records e p) = (leavesOf g w p).map (records e) := by
  simp [leavesOf, List.map_map, Function.comp_def]
@[simp] theorem dfsTrace_relabel (e : LogicalKey → LogicalKey) (g : Geom) (w : Word e) (p : List Rec) :
    dfsTrace g (word e w) (records e p) = dfsTrace g w p := by simp [dfsTrace]
@[simp] theorem topHome_rec (e : LogicalKey → LogicalKey) (g : TopGeom) (w : Word e) (r : Rec) :
    topHome g (word e w) (rec e r) = topHome g w r := by simp [topHome]
@[simp] theorem topWay_rec (e : LogicalKey → LogicalKey) (g : TopGeom) (w : Word e) (r : Rec) :
    topWay g (word e w) (rec e r) = topWay g w r := by simp [topWay]
@[simp] theorem earlyDrop_rec (e : LogicalKey → LogicalKey) (u : Flag e) (r : Rec) :
    earlyDrop (unsh e u) (rec e r) = earlyDrop u r := by simp [earlyDrop]
@[simp] theorem topTierCopy_relabel (e : LogicalKey → LogicalKey) (u : Flag e) (i : TopInputs) :
    topTierCopy (unsh e u) (topInputs e i) = records e (topTierCopy u i) := by
  simp [topTierCopy, topInputs]
@[simp] theorem topDfsTrace_relabel (e : LogicalKey → LogicalKey) (g : TopGeom) (w : Word e) (p : List Rec) :
    topDfsTrace g (word e w) (records e p) = topDfsTrace g w p := by simp [topDfsTrace]
@[simp] theorem dropTombs_relabel (e : LogicalKey → LogicalKey) (b : Bucket) :
    dropTombs (bucket e b) = bucket e (dropTombs b) := by
  simp only [dropTombs, bucket, List.map_map]
  apply List.map_congr_left
  intro x hx
  exact option_filter (rec e) _ _ (fun r => by simp) x

@[simp] theorem finState_main (e : LogicalKey → LogicalKey) (s : FinState) : (finState e s).main = buckets e s.main := rfl
@[simp] theorem finState_ins (e : LogicalKey → LogicalKey) (s : FinState) : (finState e s).ins = records e s.ins := rfl
@[simp] theorem finState_trace (e : LogicalKey → LogicalKey) (s : FinState) : (finState e s).trace = s.trace := rfl
@[simp] theorem finState_update_main (e : LogicalKey → LogicalKey) (s : FinState) (m : List Bucket) :
    {finState e s with main := buckets e m} = finState e {s with main := m} := rfl

@[simp] theorem sRoute_main (e : LogicalKey → LogicalKey) (s : SRoute) : (sRoute e s).main = buckets e s.main := rfl
@[simp] theorem sRoute_trace (e : LogicalKey → LogicalKey) (s : SRoute) : (sRoute e s).trace = s.trace := rfl
@[simp] theorem sFin_main (e : LogicalKey → LogicalKey) (s : SFin) : (sFin e s).main = buckets e s.main := rfl
@[simp] theorem sFin_ins (e : LogicalKey → LogicalKey) (s : SFin) : (sFin e s).ins = records e s.ins := rfl
@[simp] theorem sFin_trace (e : LogicalKey → LogicalKey) (s : SFin) : (sFin e s).trace = s.trace := rfl
@[simp] theorem sFin_update_main (e : LogicalKey → LogicalKey) (s : SFin) (m : List Bucket) :
    {sFin e s with main := buckets e m} = sFin e {s with main := m} := rfl

@[simp] theorem sPairStep_relabel (e : LogicalKey → LogicalKey) (g : SepGeom) (w : Word e)
    (j i : Nat) (s : SRoute) :
    sPairStep engineRule g (word e w) j i (sRoute e s) =
      sRoute e (sPairStep engineRule g w j i s) := by
  simp only [sPairStep, sRoute, buckets_getD, records_getD, split_relabel,
    ← records_append, buckets_set, records_set, records_length]

@[simp] theorem runSOps_relabel (e : LogicalKey → LogicalKey) (g : SepGeom) (w : Word e)
    (ops : List (Nat × Nat)) (s : SRoute) :
    runSOps engineRule g (word e w) ops (sRoute e s) =
      sRoute e (runSOps engineRule g w ops s) := by
  apply foldl_transport
  intro s x
  exact sPairStep_relabel e g w x.1 x.2 s

@[simp] theorem bucket_filter (e : LogicalKey → LogicalKey) (b : Bucket) (p : Rec → Bool) :
    (bucket e b).map (fun s => s.filter p) =
      bucket e (b.map (fun s => s.filter (fun r => p (rec e r)))) := by
  simp only [bucket, List.map_map]
  apply List.map_congr_left
  intro x hx
  exact option_filter (rec e) _ _ (fun _ => rfl) x

/-- Class-based selection preserves the exact kept and shed orders. -/
theorem pickClass_relabel (e : LogicalKey → LogicalKey) (cls cls' : Rec → Nat)
    (h : ∀ r, cls' (rec e r) = cls r) (n : Nat → Nat) (xs : List Rec) :
    pickClass cls' n (records e xs) =
      (records e (pickClass cls n xs).1, records e (pickClass cls n xs).2) := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih =>
    simp only [records] at ih
    change pickClass cls' n (rec e x :: records e xs) = _
    simp only [pickClass, h]
    split <;> simp only [ih, records, List.map_cons]

/-- Every radix output keeps its lanes and its per-input placement counts. -/
theorem radixOutput_relabel (e : LogicalKey → LogicalKey) (cls cls' : Rec → Nat)
    (h : ∀ r, cls' (rec e r) = cls r) (xs : List Bucket) (a : Nat) :
    radixOutput cls' (buckets e xs) a =
      (bucket e (radixOutput cls xs a).1, (radixOutput cls xs a).2) := by
  let step (x : List Bucket) (c : Rec → Nat) (acc : Bucket × List Nat) (i : Nat) :=
    if i = a then (acc.1, acc.2 ++ [0]) else
      let cand := (x.getD i []).recs.filter (fun r => c r == a)
      let f := fill acc.1 cand
      (f.1, acc.2 ++ [cand.length - f.2.length])
  have hs (acc : Bucket × List Nat) (i : Nat) :
      step (buckets e xs) cls' (bucket e acc.1, acc.2) i =
      (bucket e (step xs cls acc i).1, (step xs cls acc i).2) := by
    dsimp only [step]
    by_cases hi : i = a <;>
      simp only [hi, ite_true, ite_false, buckets_getD, bucket_recs, records_filter,
        h, fill_relabel, records_length]
  have hinit : ((buckets e xs).getD a []).map (fun s => s.filter (fun r => cls' r == a)) =
      bucket e ((xs.getD a []).map (fun s => s.filter (fun r => cls r == a))) := by
    simp only [buckets_getD, bucket_filter, h]
  unfold radixOutput
  rw [buckets_length, hinit]
  exact foldl_transport (fun (acc : Bucket × List Nat) => (bucket e acc.1, acc.2))
    (step xs cls) (step (buckets e xs) cls') hs _
    ((xs.getD a []).map (fun s => s.filter (fun r => cls r == a)), [])

/-- A radix split relabels records while retaining tuple and shed ordering. -/
theorem radixSplit_relabel (e : LogicalKey → LogicalKey) (cls cls' : Rec → Nat)
    (h : ∀ r, cls' (rec e r) = cls r) (xs : List Bucket) :
    radixSplit cls' (buckets e xs) =
      (buckets e (radixSplit cls xs).1, records e (radixSplit cls xs).2) := by
  have ho : (List.range xs.length).map (radixOutput cls' (buckets e xs)) =
      ((List.range xs.length).map (radixOutput cls xs)).map
        (fun acc => (bucket e acc.1, acc.2)) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro a ha
    exact radixOutput_relabel e cls cls' h xs a
  unfold radixSplit
  simp only [buckets_length, ho]
  apply Prod.ext
  · simp [buckets, List.map_map, Function.comp_def]
  · simp only [records, List.map_flatMap]
    apply congrArg (fun f : Nat → List Rec => (List.range xs.length).flatMap f)
    funext i
    simp only [buckets_getD, bucket_recs, bucket_length]
    have hget (a : Nat) :
        (((List.range xs.length).map (radixOutput cls xs)).map
          (fun acc => (bucket e acc.1, acc.2))).getD a ([], []) =
        (bucket e (((List.range xs.length).map (radixOutput cls xs)).getD a ([], [])).1,
         (((List.range xs.length).map (radixOutput cls xs)).getD a ([], [])).2) :=
      map_getD' (fun (acc : Bucket × List Nat) => (bucket e acc.1, acc.2)) _ a ([], [])
    simp only [hget]
    exact congrArg Prod.snd (pickClass_relabel e cls cls' h _ _)

@[simp] theorem radixStep_relabel (e : LogicalKey → LogicalKey) (g : SepGeom) (w : Word e)
    (p : Nat) (s : SRoute) :
    radixStep g (word e w) p (sRoute e s) = sRoute e (radixStep g w p s) := by
  unfold radixStep
  have hm : ((List.range g.r).map (fun a => a * g.blk + p)).map
      (fun j => (buckets e s.main).getD j []) =
      buckets e (((List.range g.r).map (fun a => a * g.blk + p)).map
        (fun j => s.main.getD j [])) := by
    simp only [buckets_getD]
    simp only [buckets, List.map_map, Function.comp_def]
  simp only [sRoute_main, hm]
  rw [radixSplit_relabel e (fun x => g.cls (w x.key))
    (fun x => g.cls (word e w x.key)) (fun r => by simp)]
  have hf (idx : List Nat) (bs : List Bucket) (m : List Bucket) :
      (idx.zip (buckets e bs)).foldl (fun m q => m.set q.1 q.2) (buckets e m) =
      buckets e ((idx.zip bs).foldl (fun m q => m.set q.1 q.2) m) := by
    simp only [buckets, List.zip_map_right, List.foldl_map]
    exact foldl_transport (buckets e) _ _ (fun m q => buckets_set e m q.1 q.2) _ m
  simp only [sRoute, hf, ← records_append, records_length]

@[simp] theorem radixPass_relabel (e : LogicalKey → LogicalKey) (g : SepGeom) (w : Word e)
    (s : SRoute) : radixPass g (word e w) (sRoute e s) = sRoute e (radixPass g w s) := by
  unfold radixPass
  split
  · apply foldl_transport
    intro s p
    exact radixStep_relabel e g w p s
  · rfl

@[simp] theorem sRouteInit_relabel (e : LogicalKey → LogicalKey) (g : SepGeom) (m : List Bucket) :
    sRouteInit g (buckets e m) = sRoute e (sRouteInit g m) := by
  simp [sRouteInit, sRoute, buckets]

@[simp] theorem sRouteWith_relabel (e : LogicalKey → LogicalKey) (g : SepGeom) (w : Word e)
    (m : List Bucket) (ops : List (Nat × Nat)) :
    sRouteWith engineRule g (word e w) (buckets e m) ops =
      sRoute e (sRouteWith engineRule g w m ops) := by
  simp only [sRouteWith, sRouteInit_relabel, runSOps_relabel, radixPass_relabel]

@[simp] theorem sLeaves_relabel (e : LogicalKey → LogicalKey) (g : SepGeom) (w : Word e)
    (p : List Rec) : sLeaves g (word e w) (records e p) =
      (sLeaves g w p).map (records e) := by
  simp [sLeaves, sRange, sHome, List.map_map, Function.comp_def]

@[simp] theorem sDfsTrace_relabel (e : LogicalKey → LogicalKey) (g : SepGeom) (w : Word e)
    (p : List Rec) : sDfsTrace g (word e w) (records e p) = sDfsTrace g w p := by
  simp [sDfsTrace, sRange, sHome]

@[simp] theorem sInputs_aMain (e : LogicalKey → LogicalKey) (inp : SInputs) :
    (sInputs e inp).aMain = buckets e inp.aMain := rfl
@[simp] theorem sInputs_aTier (e : LogicalKey → LogicalKey) (inp : SInputs) :
    (sInputs e inp).aTier = records e inp.aTier := rfl
@[simp] theorem sInputs_bTier (e : LogicalKey → LogicalKey) (inp : SInputs) :
    (sInputs e inp).bTier = inp.bTier.map (records e) := rfl



open Model.DirectJob
def inputs (e : LogicalKey → LogicalKey) (inp : DirectJob.Inputs) : DirectJob.Inputs :=
  ⟨buckets e inp.aMain, records e inp.aTier, buckets e inp.units⟩
def table (e : LogicalKey → LogicalKey) (b : Table) : Table :=
  ⟨b.main.map (records e), records e b.tier⟩
def laneResult (e : LogicalKey → LogicalKey) : LaneResult → LaneResult
  | .rejected r => .rejected r
  | .failed ev => .failed ev
  | .published out => .published (output e out)
def reference (e : LogicalKey → LogicalKey) (st : ReferenceTable) : ReferenceTable :=
  ⟨buckets e st.main, records e st.tier⟩
@[simp] theorem records_flatMap_recs (e : LogicalKey → LogicalKey) (bs : List Bucket) :
    (buckets e bs).flatMap Bucket.recs = records e (bs.flatMap Bucket.recs) := by
  simp [buckets, records, List.flatMap_map, List.map_flatMap, bucket_recs]
@[simp] theorem inputs_aRecords (e : LogicalKey → LogicalKey) (inp : DirectJob.Inputs) :
    (inputs e inp).aRecords = records e inp.aRecords := by
  simp [inputs, DirectJob.Inputs.aRecords]
@[simp] theorem inputs_bRecords (e : LogicalKey → LogicalKey) (inp : DirectJob.Inputs) :
    (inputs e inp).bRecords = records e inp.bRecords := by
  simp [inputs, DirectJob.Inputs.bRecords, DirectMasks.records]
@[simp] theorem adopt_output (e : LogicalKey → LogicalKey) (out : Output) (us : List Bucket) :
    adopt (output e out) (buckets e us) = inputs e (adopt out us) := by
  simp [adopt, output, inputs]
@[simp] theorem bLanes_table (e : LogicalKey → LogicalKey) (t : Table) :
    (table e t).bLanes = buckets e t.bLanes := by
  simp [Table.bLanes, table, buckets, records, bucket, List.map_map, Function.comp_def]
@[simp] theorem finishOutput_map (e : LogicalKey → LogicalKey) (g : Geometry) (main : List Bucket) (tier : Bucket) :
    finishOutput g (buckets e main) (bucket e tier) = output e (finishOutput g main tier) := by
  simp only [finishOutput, output, bucket_append, bucket_length, bucket_replicate]

 theorem stepsBounded_transport {σ τ α : Type} (f : σ → τ)
    (step : Nat → σ → α → σ × CheckEvent) (step' : Nat → τ → α → τ × CheckEvent)
    (hs : ∀ n st op, step' n (f st) op = (f (step n st op).1, (step n st op).2))
    (n : Nat) (st : σ) (ops : List α) :
    stepsBounded step' n (f st) ops = (stepsBounded step n st ops).map f := by
  induction ops generalizing n st with
  | nil => rfl
  | cons op ops ih =>
    simp only [stepsBounded, hs]
    split <;> simp_all [Except.map]

 def distribution (e : LogicalKey → LogicalKey) (d : ADistribution) : ADistribution :=
   ⟨d.leaves.map (records e), d.trace⟩
 theorem distributeA_relabel (e : LogicalKey → LogicalKey) (g : Geometry) (w : Word e) (pool : List Rec) :
    distributeA g (word e w) (records e pool) = distribution e (distributeA g w pool) := by
  cases hg : g.ranges with
  | direct => simp [distributeA, hg, distribution]
  | dfs i r p =>
    simp only [distributeA, hg, distribution, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro v hv
      apply map_filter
      intro x
      simp
    · apply List.map_congr_left
      intro v hv
      congr 1
      have hf : ((records e pool).filter fun x => g.home (word e w x.key) / 2 ^ i / 2 ^ (r - v.1.1) == v.1.2) =
          records e (pool.filter fun x => g.home (w x.key) / 2 ^ i / 2 ^ (r - v.1.1) == v.1.2) := by
        apply map_filter
        intro x
        simp
      rw [hf, records_length]
 theorem distributeABounded_relabel (e : LogicalKey → LogicalKey) (g : Geometry) (w : Word e) (pool : List Rec) :
    distributeABounded g (word e w) (records e pool) =
      (distributeABounded g w pool).map (List.map (records e)) := by
  simp only [distributeABounded, distributeA_relabel, distribution]
  cases firstFailure (distributeA g w pool).trace <;> rfl

 theorem aTransition_relabel (e : LogicalKey → LogicalKey) (g : Geometry) (w : Word e)
    (n : Nat) (st : SRoute) (op : AOp) :
    aTransition g (word e w) n (sRoute e st) op =
      (sRoute e (aTransition g w n st op).1, (aTransition g w n st op).2) := by
  cases op <;> simp only [aTransition, sPairStep_relabel, radixStep_relabel]
  · simp only [sRoute, records_getD, records_length]
  · simp [sRoute]
 theorem aInitial_relabel (e : LogicalKey → LogicalKey) (g : Geometry) (main : List Bucket) :
    aInitial g (buckets e main) = sRoute e (aInitial g main) := by
  simp [aInitial, sRouteInit, sRoute, buckets]
 theorem prepareA_relabel (e : LogicalKey → LogicalKey) (g : Geometry) (w : Word e) (main : List Bucket) :
    prepareA g (word e w) (buckets e main) = (prepareA g w main).map (sRoute e) := by
  simp only [prepareA, aInitial_relabel]
  exact stepsBounded_transport (sRoute e) _ _ (aTransition_relabel e g w) _ _ _

theorem stepsAnalytical_transport {σ τ α : Type} (f : σ → τ)
    (step : Nat → σ → α → σ × CheckEvent) (step' : Nat → τ → α → τ × CheckEvent)
    (hs : ∀ n st op, step' n (f st) op = (f (step n st op).1, (step n st op).2))
    (n : Nat) (st : σ) (ops : List α) :
    stepsAnalytical step' n (f st) ops =
      ⟨f (stepsAnalytical step n st ops).state, (stepsAnalytical step n st ops).trace⟩ := by
  induction ops generalizing n st with
  | nil => rfl
  | cons op ops ih => simp only [stepsAnalytical, hs, ih]
@[simp] theorem analyticalA_relabel (e : LogicalKey → LogicalKey) (g : Geometry) (w : Word e)
    (main : List Bucket) :
    analyticalA g (word e w) (buckets e main) =
      ⟨sRoute e (analyticalA g w main).state, (analyticalA g w main).trace⟩ := by
  unfold analyticalA
  rw [aInitial_relabel]
  exact stepsAnalytical_transport (sRoute e) _ _ (aTransition_relabel e g w) _ _ _

end RebuildBound.NativeRekeyRouting
