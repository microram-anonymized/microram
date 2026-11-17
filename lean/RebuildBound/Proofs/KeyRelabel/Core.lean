import Mathlib.Logic.Equiv.Basic
import RebuildBound.Spec.Model.DirectJobReference

namespace RebuildBound.KeyRelabel
open Model

def rec (e : LogicalKey ≃ LogicalKey) (r : Rec) : Rec := { r with key := e r.key }
def records (e : LogicalKey ≃ LogicalKey) (rs : List Rec) : List Rec := rs.map (rec e)
def bucket (e : LogicalKey ≃ LogicalKey) (b : Bucket) : Bucket := b.map (Option.map (rec e))
def buckets (e : LogicalKey ≃ LogicalKey) (bs : List Bucket) : List Bucket := bs.map (bucket e)
def word (e : LogicalKey ≃ LogicalKey) (w : LogicalKey → Nat) : LogicalKey → Nat := w ∘ e.symm
def words (e : LogicalKey ≃ LogicalKey) (w : Nat → Nat → LogicalKey → Nat) : Nat → Nat → LogicalKey → Nat :=
   fun l v => word e (w l v)
def unsh (e : LogicalKey ≃ LogicalKey) (u : Rec → Bool) : Rec → Bool := u ∘ rec e.symm
def output (e : LogicalKey ≃ LogicalKey) (out : Output) : Output := ⟨buckets e out.main, bucket e out.tier⟩

@[simp] theorem rec_key (e : LogicalKey ≃ LogicalKey) (r : Rec) : (rec e r).key = e r.key := rfl
@[simp] theorem rec_val (e : LogicalKey ≃ LogicalKey) (r : Rec) : (rec e r).val = r.val := rfl
@[simp] theorem rec_tomb (e : LogicalKey ≃ LogicalKey) (r : Rec) : (rec e r).tomb = r.tomb := rfl
@[simp] theorem rec_symm (e : LogicalKey ≃ LogicalKey) (r : Rec) : rec e.symm (rec e r) = r := by cases r; simp [rec]
@[simp] theorem rec_symm' (e : LogicalKey ≃ LogicalKey) (r : Rec) : rec e (rec e.symm r) = r := by cases r; simp [rec]
 theorem rec_injective (e : LogicalKey ≃ LogicalKey) : Function.Injective (rec e) := by
  intro x y h
  simpa using congrArg (rec e.symm) h
@[simp] theorem word_apply (e : LogicalKey ≃ LogicalKey) (w : LogicalKey → Nat) (k : LogicalKey) : word e w (e k) = w k := by simp [word]
@[simp] theorem unsh_apply (e : LogicalKey ≃ LogicalKey) (u : Rec → Bool) (r : Rec) : unsh e u (rec e r) = u r := by simp [unsh]
@[simp] theorem records_length (e : LogicalKey ≃ LogicalKey) (rs : List Rec) : (records e rs).length = rs.length := by simp [records]
@[simp] theorem bucket_length (e : LogicalKey ≃ LogicalKey) (b : Bucket) : (bucket e b).length = b.length := by simp [bucket]
@[simp] theorem buckets_length (e : LogicalKey ≃ LogicalKey) (bs : List Bucket) : (buckets e bs).length = bs.length := by simp [buckets]
@[simp] theorem records_nil (e : LogicalKey ≃ LogicalKey) : records e [] = [] := rfl
@[simp] theorem bucket_nil (e : LogicalKey ≃ LogicalKey) : bucket e [] = [] := rfl
@[simp] theorem buckets_nil (e : LogicalKey ≃ LogicalKey) : buckets e [] = [] := rfl
@[simp] theorem records_append (e : LogicalKey ≃ LogicalKey) (rs ss : List Rec) : records e (rs ++ ss) = records e rs ++ records e ss := by simp [records]
@[simp] theorem bucket_append (e : LogicalKey ≃ LogicalKey) (b c : Bucket) : bucket e (b ++ c) = bucket e b ++ bucket e c := by simp [bucket]
@[simp] theorem buckets_append (e : LogicalKey ≃ LogicalKey) (b c : List Bucket) : buckets e (b ++ c) = buckets e b ++ buckets e c := by simp [buckets]
@[simp] theorem bucket_empty (e : LogicalKey ≃ LogicalKey) (n : Nat) : bucket e (Bucket.empty n) = Bucket.empty n := by simp [bucket, Bucket.empty]
@[simp] theorem bucket_replicate (e : LogicalKey ≃ LogicalKey) (n : Nat) : bucket e (List.replicate n none) = List.replicate n none := by simp [bucket]
@[simp] theorem bucket_recs (e : LogicalKey ≃ LogicalKey) (b : Bucket) : (bucket e b).recs = records e b.recs := by
  induction b with
  | nil => rfl
  | cons x xs ih => cases x <;> simp_all [bucket, Bucket.recs, records]
@[simp] theorem records_keys (e : LogicalKey ≃ LogicalKey) (rs : List Rec) : (records e rs).map Rec.key = (rs.map Rec.key).map e := by simp [records, List.map_map, Function.comp_def]
@[simp] theorem bucket_keys (e : LogicalKey ≃ LogicalKey) (b : Bucket) : (bucket e b).keys = b.keys.map e := by simp [Bucket.keys]
@[simp] theorem key_mem (e : LogicalKey ≃ LogicalKey) (k : LogicalKey) (ks : List LogicalKey) : e k ∈ ks.map e ↔ k ∈ ks := by simp
@[simp] theorem key_contains (e : LogicalKey ≃ LogicalKey) (k : LogicalKey) (ks : List LogicalKey) : (ks.map e).contains (e k) = ks.contains k := by simp
@[simp] theorem key_beq (e : LogicalKey ≃ LogicalKey) (a b : LogicalKey) : (e a == e b) = (a == b) := by simp

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
@[simp] theorem bucket_clear (e : LogicalKey ≃ LogicalKey) (p : LogicalKey → Bool) (b : Bucket) :
    Bucket.clear (p ∘ e.symm) (bucket e b) = bucket e (Bucket.clear p b) := by
  induction b with
  | nil => rfl
  | cons x xs ih => cases x <;> simp_all [Bucket.clear, bucket, Option.filter, Function.comp_def]
 theorem pick_map (e : LogicalKey ≃ LogicalKey) (dir : Rec → Bool) (n m : Nat) (rs : List Rec) :
    pick (unsh e dir) n m (records e rs) =
      (records e (pick dir n m rs).1, records e (pick dir n m rs).2.1,
       records e (pick dir n m rs).2.2) := by
  induction rs generalizing n m with
  | nil => rfl
  | cons x xs ih =>
    simp only [records] at ih
    cases n <;> cases m <;> cases hd : dir x <;> simp [records, pick, unsh_apply, hd, ih]
 theorem engineSplit_map (e : LogicalKey ≃ LogicalKey) (C : Nat) (dir : Rec → Bool) (b c : Bucket) :
    engineSplit C (unsh e dir) (bucket e b) (bucket e c) =
      (bucket e (engineSplit C dir b c).1, bucket e (engineSplit C dir b c).2.1,
       records e (engineSplit C dir b c).2.2) := by
  have hm (p : Rec → Bool) :
      (bucket e b).map (fun s => s.filter (unsh e p)) = bucket e (b.map (fun s => s.filter p)) := by
    simp only [bucket, List.map_map]
    apply List.map_congr_left
    intro x hx
    exact option_filter (rec e) p (unsh e p) (unsh_apply e p) x
  have hn (bs : Bucket) : (bucket e bs).countP (·.isNone) = bs.countP (·.isNone) := by
    induction bs with
    | nil => rfl
    | cons x xs ih => cases x <;> simp_all [bucket]
  have hneg : (fun r => !(unsh e dir) r) = unsh e (fun r => !dir r) := rfl
  simp only [engineSplit, hneg, hm, hn, bucket_recs, pick_map]
  simp only [bucket, records, fill_map]

end RebuildBound.KeyRelabel
