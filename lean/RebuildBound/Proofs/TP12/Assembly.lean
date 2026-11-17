import RebuildBound.Proofs.TP12.FinStep

/-!
# TP12: the finish and the drain, from the routed main and the pool
-/

namespace RebuildBound.TP12

open RebuildBound.Model RebuildBound.D23 RebuildBound.S12

/-! ### The leaves partition the pool -/

theorem filter_lt_perm (f : Rec → Nat) (L : List Rec) :
    ∀ R : Nat, List.Perm (L.filter fun x => decide (f x < R))
      ((List.range R).flatMap fun v => L.filter fun x => f x == v)
  | 0 => by simp
  | R + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine List.Perm.trans ?_ ((filter_lt_perm f L R).append_right _)
    have h := List.filter_append_perm (fun x => decide (f x < R))
      (L.filter fun x => decide (f x < R + 1))
    have e1 : (L.filter fun x => decide (f x < R + 1)).filter (fun x => decide (f x < R)) =
        L.filter fun x => decide (f x < R) := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro x _
      by_cases h1 : f x < R
      · simp [h1, show f x < R + 1 by omega]
      · simp [h1]
    have e2 : (L.filter fun x => decide (f x < R + 1)).filter (fun x => !decide (f x < R)) =
        L.filter fun x => f x == R := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro x _
      by_cases h1 : f x < R
      · simp [h1, show ¬ f x = R by omega]
      · by_cases h2 : f x = R
        · simp [h1, h2]
        · have h3 : ¬ f x < R + 1 := by omega
          simp [h1, h2, h3]
    rw [e1, e2] at h
    exact h.symm

theorem leaves_getD (g : TPGeom) (w : Model.LogicalKey → Nat) (pool : List Rec) {R : Nat} (hR : R < g.ranges) :
    (tpLeaves g w pool).getD R [] = pool.filter fun r => tpRange g w r == R := by
  unfold tpLeaves
  rw [getD_eq_getElem' _ _ _ (by simpa using hR)]
  simp

theorem leaves_length (g : TPGeom) (w : Model.LogicalKey → Nat) (pool : List Rec) :
    (tpLeaves g w pool).length = g.ranges := by
  simp [tpLeaves]

theorem leaves_perm (g : TPGeom) (hg : g.Valid) (w : Model.LogicalKey → Nat) (pool : List Rec) :
    List.Perm (tpLeaves g w pool).flatten pool := by
  have h := filter_lt_perm (tpRange g w) pool g.ranges
  have e : pool.filter (fun x => decide (tpRange g w x < g.ranges)) = pool := by
    rw [List.filter_eq_self]; intro x _; simpa using range_lt g hg w x
  rw [e] at h
  unfold tpLeaves
  rw [← List.flatMap_def]
  exact h.symm

theorem fInv_init (g : TPGeom) (hg : g.Valid) {w : Model.LogicalKey → Nat} {M : List Bucket} {pool : List Rec}
    (hM : MData g w M) :
    FInv g w M pool 0 { main := M, last := [], leaves := tpLeaves g w pool, trace := [] } where
  mlen := hM.len
  mlanes := hM.lanes
  llen := leaves_length g w pool
  lrange := by
    intro R x hx
    by_cases hR : R < g.ranges
    · rw [leaves_getD g w pool hR] at hx
      have := (List.mem_filter.1 hx).2
      simpa using this
    · rw [getD_nil_of_ge _ _ (by rw [leaves_length]; omega)] at hx
      simp at hx
  cons := by
    have := leaves_perm g hg w pool
    simpa using this.append_left (M.flatMap Bucket.recs)
  unproc := by
    intro b hb _
    refine ⟨rfl, ?_⟩
    rw [leaves_getD g w pool (div_lt_ranges g hg hb), List.countP_filter]
    apply List.countP_congr
    intro x _
    unfold tpRange
    by_cases h : tpHome g w x = b
    · simp [h]
    · simp [h]
  proc := fun b _ h => absurd h (Nat.not_lt_zero _)
  leafFull := fun r _ h => absurd h (Nat.not_lt_zero _)
  lastFull := fun r hr => absurd hr List.not_mem_nil

theorem fInv_fold {rule : CapRule} (hv : rule.Valid) {g : TPGeom} (hg : g.Valid) {w : Model.LogicalKey → Nat}
    {M : List Bucket} {pool : List Rec} (hM : MData g w M) :
    ∀ n ≤ g.half, FInv g w M pool n
      ((List.range n).foldl (fun st i => tpLastStep rule g w i st)
        { main := M, last := [], leaves := tpLeaves g w pool, trace := [] })
  | 0, _ => fInv_init g hg hM
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append]
    exact fInv_step hv hg hM (by omega) (fInv_fold hv hg hM n (by omega))

/-! ### The drain -/

theorem foldl_tpDrainStep_perm :
    ∀ (Ls : List (List Rec)) (acc : List (Option Rec) × List (TPTest × Nat)),
      List.Perm ((Ls.foldl tpDrainStep acc).1.filterMap id) (acc.1.filterMap id ++ Ls.flatten)
  | [], acc => by simp
  | L :: Ls, acc => by
    rw [List.foldl_cons, List.flatten_cons]
    refine (foldl_tpDrainStep_perm Ls (tpDrainStep acc L)).trans ?_
    rw [← List.append_assoc]
    exact (appendFill_recs acc.1 L).append_right _

theorem tpDrain_perm (st : TPFin) :
    List.Perm ((tpDrain st).1.filterMap id) (st.leaves.flatten ++ st.last) := by
  have := foldl_tpDrainStep_perm (st.leaves ++ [st.last]) ([], [])
  simpa [tpDrain, List.flatten_append] using this

/-! ### The core -/

theorem tp12_core {rule : CapRule} (hv : rule.Valid) {g : TPGeom} (hg : g.Valid) {w : Model.LogicalKey → Nat}
    {M : List Bucket} {pool S : List Rec} (hM : MData g w M)
    (hS : List.Perm (M.flatMap Bucket.recs ++ pool) S) (fin : TPFin)
    (hfin : fin = tpFinish rule g w M (tpLeaves g w pool)) :
    List.Perm (fin.main.flatMap Bucket.recs ++ (tpDrain fin).1.filterMap id) S ∧
    fin.main.length = g.T ∧
    (∀ B ∈ fin.main, B.length = g.C) ∧
    (∀ v < g.T, ∀ r ∈ (fin.main.getD v []).recs, tpHome g w r = v) ∧
    (∀ v < g.T, (fin.main.getD v []).recs.length = min (tpHomeCount g w S v) g.C) ∧
    (∀ r ∈ (tpDrain fin).1.filterMap id, (fin.main.getD (tpHome g w r) []).recs.length = g.C) := by
  have hf : FInv g w M pool g.half fin := by
    have := fInv_fold hv hg (pool := pool) hM g.half (Nat.le_refl _)
    rw [hfin]; exact this
  have hdr := tpDrain_perm fin
  refine ⟨?_, hf.mlen, hf.mlanes, ?_, ?_, ?_⟩
  · refine List.Perm.trans ?_ hS
    have hc := hf.cons
    rw [List.perm_iff_count] at hc ⊢
    intro x
    have c1 := hc x
    have c2 := hdr.count_eq x
    simp only [List.count_append] at c1 c2 ⊢
    omega
  · intro v hv' r hr
    exact (hf.proc v hv' (Nat.mod_lt _ (half_pos g))).1 r hr
  · intro v hv'
    rw [(hf.proc v hv' (Nat.mod_lt _ (half_pos g))).2]
    have : tpHomeCount g w S v = (M.flatMap Bucket.recs).countP (fun r => tpHome g w r == v) +
        pool.countP (fun r => tpHome g w r == v) := by
      unfold tpHomeCount
      rw [← hS.countP_eq, List.countP_append]
    rw [this, Nat.min_comm]
  · intro r hr
    have hmem := hdr.mem_iff.1 hr
    have hlt : tpHome g w r % g.half < g.half := Nat.mod_lt _ (half_pos g)
    rcases List.mem_append.1 hmem with h | h
    · exact hf.leafFull r h hlt
    · exact (hf.lastFull r h).2

end RebuildBound.TP12
