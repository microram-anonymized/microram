import Mathlib
import RebuildBound.Spec.Model.TopPrepContract
import RebuildBound.Proofs.RouteCore.GInv

/-!
# TP4 helpers: invariants of the top preparation's stage-by-stage route

The top-preparation analogue of `S4a/Route.lean`. After the stages that read
bits `< n` (`GInv n`, `n ≤ k - 1`): every main record sits at `dest n`; main
and stashes together hold the arrival's records (A's main minus its flagged
tombstones); the stash of bit `j < n` has at most `tpRawStageExcess j` records.
`GInv` is the TP form of `GInvCore.GInv`, proved once by `GInvCore.ginv_range`
with the full bases `GInvCore.bases_full`.
-/

namespace RebuildBound.TP4Proof

open RebuildBound.Model
open RebuildBound.D4aProof (getD_of_le)

section Route

variable (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (pos w : Model.LogicalKey → Nat) (inp : TPInputs)

/-- The pair bases of the stage reading bit `n`. -/
def bases (n : ℕ) : List ℕ := (List.range g.T).filter fun i => !i.testBit n

/-- The bucket of a record after the stages that read bits `< n`. -/
def dest (n : ℕ) (x : Rec) : ℕ := 2 ^ n * (pos x.key / 2 ^ n) + w x.key % 2 ^ n

structure Shape (st : TPRoute) : Prop where
  mainLen : st.main.length = g.T
  lanes : ∀ B ∈ st.main, B.length = g.C
  stashLen : st.stash.length = g.k

/-- Main and stashes together hold the arrival's records exactly. -/
def Cons (st : TPRoute) : Prop :=
  ∀ p : Rec → Bool, (st.main.flatMap Bucket.recs).countP p + st.stash.flatten.countP p =
    ((copyMain unsh inp.aMain).flatMap Bucket.recs).countP p

structure GInv (n : ℕ) (st : TPRoute) : Prop where
  shape : Shape g st
  cons : Cons unsh inp st
  later : ∀ j, n ≤ j → st.stash.getD j [] = []
  early : ∀ j, j < n → (st.stash.getD j []).length ≤ tpRawStageExcess g unsh pos w inp j
  at_dest : ∀ m, ∀ r ∈ (st.main.getD m []).recs, m = dest pos w n r

end Route

lemma T_eq (g : TPGeom) (hg : g.Valid) : g.T = 2 ^ ((g.k - 1) + 1) := by
  have := hg.1
  unfold TPGeom.T
  congr 1; omega

lemma bucket_map_filter_recs (q : Rec → Bool) (B : Bucket) :
    Bucket.recs (B.map fun s => s.filter q) = B.recs.filter q := by
  induction B with
  | nil => simp [Bucket.recs]
  | cons s B ih =>
    unfold Bucket.recs at *
    cases s with
    | none => simpa using ih
    | some r =>
      simp only [List.map_cons, List.filterMap_cons, id, Option.filter] at ih ⊢
      by_cases h : q r = true
      · simp [h, ih]
      · simp [h, ih]

lemma copyMain_getD (unsh : Rec → Bool) (aMain : List Bucket) (m : ℕ) :
    (copyMain unsh aMain).getD m [] =
      ((aMain.getD m []).map fun s => s.filter fun r => !flagged unsh r) := by
  unfold copyMain
  by_cases h : m < aMain.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h]
    simp
  · rw [getD_of_le _ _ _ (by simpa using h), getD_of_le _ _ _ (by omega)]
    simp

lemma copyMain_recs_getD (unsh : Rec → Bool) (aMain : List Bucket) (m : ℕ) :
    ((copyMain unsh aMain).getD m []).recs =
      ((aMain.getD m []).recs).filter fun r => !flagged unsh r := by
  rw [copyMain_getD, bucket_map_filter_recs]

lemma copyMain_flatMap (unsh : Rec → Bool) (aMain : List Bucket) :
    (copyMain unsh aMain).flatMap Bucket.recs =
      (aMain.flatMap Bucket.recs).filter fun r => !flagged unsh r := by
  unfold copyMain
  rw [List.flatMap_map, List.filter_flatMap]
  apply List.flatMap_congr
  intro B _
  exact bucket_map_filter_recs _ B

lemma copyMain_countP_le (unsh : Rec → Bool) (inp : TPInputs) (p : Rec → Bool) :
    ((copyMain unsh inp.aMain).flatMap Bucket.recs).countP p ≤
      (inp.survivors unsh).countP p := by
  rw [copyMain_flatMap]
  unfold TPInputs.survivors TPInputs.aAll
  rw [List.filter_append, List.countP_append]
  omega

section Route2

variable (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (pos w : Model.LogicalKey → Nat) (inp : TPInputs)

lemma ginv_init (hin : TPShape g pos inp) :
    GInv g unsh pos w inp 0 (tpRouteInit g (copyMain unsh inp.aMain)) := by
  have hstash : ∀ j, (tpRouteInit g (copyMain unsh inp.aMain)).stash.getD j [] = [] := by
    intro j
    simp only [tpRouteInit, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_, fun j _ => hstash j, fun j hj => absurd hj (by omega), ?_⟩
  · simp [tpRouteInit, copyMain, hin.aLen]
  · intro B hB
    simp only [tpRouteInit, copyMain, List.mem_map] at hB
    obtain ⟨B', hB', rfl⟩ := hB
    simpa using hin.aLanes B' hB'
  · simp [tpRouteInit]
  · intro p
    simp [tpRouteInit]
  · intro m r hr
    unfold dest; simp only [pow_zero, Nat.div_one, Nat.one_mul, Nat.mod_one, Nat.add_zero]
    simp only [tpRouteInit] at hr
    rw [copyMain_recs_getD] at hr
    have hr' := (List.mem_filter.mp hr).1
    rcases Nat.lt_or_ge m g.T with hm | hm
    · exact (hin.aHome m hm r hr').symm
    · rw [getD_of_le _ _ _ (by rw [hin.aLen]; exact hm)] at hr'
      simp [Bucket.recs] at hr'

lemma canon_fold_eq (st : TPRoute) :
    runTPOps rule g w g.canonicalOps st =
      (List.range (g.k - 1)).foldl
        (fun st n => (bases g n).foldl (fun st i => tpPairStep rule g w n i st) st) st := by
  unfold runTPOps TPGeom.canonicalOps
  rw [List.foldl_flatMap]
  apply List.foldl_ext
  intro st' n _
  rw [List.foldl_map]
  rfl

/-- The invariant after the complete route in the stage-by-stage order. -/
lemma ginv_canon (hv : rule.Valid) (hin : TPShape g pos inp) (hg : g.Valid) :
    GInv g unsh pos w inp (g.k - 1)
      (runTPOps rule g w g.canonicalOps (tpRouteInit g (copyMain unsh inp.aMain))) := by
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7⟩ := ginv_init g unsh pos w inp hin
  have h := GInvCore.ginv_range rule g.C g.T g.k (fun r => pos r.key) w (inp.survivors unsh)
    ((copyMain unsh inp.aMain).flatMap Bucket.recs) hv (copyMain_countP_le unsh inp) (bases g)
    (g.k - 1) (by omega) (fun n hn => ?_) ((tpRouteInit g (copyMain unsh inp.aMain)).main,
      (tpRouteInit g (copyMain unsh inp.aMain)).stash) ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7⟩ _ le_rfl
  · rw [← GInvCore.stages_proj rule g.C w (fun s : TPRoute => (s.main, s.stash))
      (fun n i s => tpPairStep rule g w n i s) (fun _ _ _ => rfl), ← canon_fold_eq] at h
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7⟩ := h
    exact ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7⟩
  · have := GInvCore.bases_full (fun r => pos r.key) n (g.k - 1) (by omega)
    rwa [← T_eq g hg] at this

end Route2

end RebuildBound.TP4Proof
