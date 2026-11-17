import RebuildBound.Proofs.SG2.Blind
import RebuildBound.Proofs.S12.Radix
import RebuildBound.Proofs.ListAux.Fill

/-!
# SG2 helpers: the terminal radix

* One tuple's radix split sheds, in class `a`, `(Σ_i (class-a records of input i) - C)₊`
  records: `S12.radixSplit_countP`.
* `radix_fold`: the radix stash of the pass is the concatenation of the tuples'
  sheds, each tuple read off the binary route's final buckets.
-/

namespace RebuildBound.SG2

open RebuildBound.Model RebuildBound.Spec RebuildBound.G2

/-! ### The pass -/

/-- The inputs of tuple `p`: the buckets `a 2^k + p`, `a < r`. -/
def rin (g : SepGeom) (st : SRoute) (p : ℕ) : List Bucket :=
  ((List.range g.r).map fun a => a * g.blk + p).map fun j => st.main.getD j []

/-- The radix sheds of tuple `p`. -/
def rshed (g : SepGeom) (w : Model.LogicalKey → ℕ) (st : SRoute) (p : ℕ) : List Rec :=
  (radixSplit (fun x => g.cls (w x.key)) (rin g st p)).2

theorem radixStep_radix (g : SepGeom) (w : Model.LogicalKey → ℕ) (p : ℕ) (st : SRoute) :
    (radixStep g w p st).radix = st.radix ++ rshed g w st p := rfl

theorem radixStep_stash (g : SepGeom) (w : Model.LogicalKey → ℕ) (p : ℕ) (st : SRoute) :
    (radixStep g w p st).stash = st.stash := rfl

theorem rin_step (g : SepGeom) (w : Model.LogicalKey → ℕ) {p p' : ℕ} (st : SRoute) (hp : p < g.blk)
    (hp' : p' < g.blk) (hne : p' ≠ p) : rin g (radixStep g w p st) p' = rin g st p' := by
  unfold rin
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro a ha
  simp only [Function.comp]
  apply S05.radixStep_getD_ne
  intro a' _ e
  apply hne
  have h1 := S05.idx_mod g (a := a) hp'
  have h2 := S05.idx_mod g (a := a') hp
  rw [e] at h1; omega

theorem radix_fold (g : SepGeom) (w : Model.LogicalKey → ℕ) :
    ∀ (P : List ℕ) (st : SRoute), P.Nodup → (∀ p ∈ P, p < g.blk) →
      (P.foldl (fun st p => radixStep g w p st) st).radix = st.radix ++ P.flatMap (rshed g w st) ∧
      (P.foldl (fun st p => radixStep g w p st) st).stash = st.stash
  | [], st, _, _ => by simp
  | p :: P, st, hnd, hlt => by
    simp only [List.foldl_cons]
    obtain ⟨ih1, ih2⟩ := radix_fold g w P (radixStep g w p st) (List.nodup_cons.1 hnd).2
      (fun p' hp' => hlt p' (List.mem_cons_of_mem _ hp'))
    refine ⟨?_, by rw [ih2, radixStep_stash]⟩
    rw [ih1, radixStep_radix, List.flatMap_cons, List.append_assoc]
    congr 2
    apply List.flatMap_congr
    intro p' hp'
    unfold rshed
    rw [rin_step g w st (hlt p List.mem_cons_self) (hlt p' (List.mem_cons_of_mem _ hp'))
      (fun e => (List.nodup_cons.1 hnd).1 (e ▸ hp'))]

theorem radixPass_stash (g : SepGeom) (w : Model.LogicalKey → ℕ) (st : SRoute) :
    (radixPass g w st).stash = st.stash := by
  unfold radixPass
  split_ifs
  · exact (radix_fold g w _ st List.nodup_range (fun p hp => List.mem_range.1 hp)).2
  · rfl

theorem radixPass_radix (g : SepGeom) (w : Model.LogicalKey → ℕ) (st : SRoute) :
    (radixPass g w st).radix =
      st.radix ++ if 1 < g.r then (List.range g.blk).flatMap (rshed g w st) else [] := by
  unfold radixPass
  split_ifs
  · exact (radix_fold g w _ st List.nodup_range (fun p hp => List.mem_range.1 hp)).1
  · simp

end RebuildBound.SG2
