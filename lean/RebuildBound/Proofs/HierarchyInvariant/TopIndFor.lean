import RebuildBound.Proofs.HierarchyInvariant.Top

/-!
# HierarchyInvariant: top induction over explicit geometry
-/

namespace RebuildBound.HierarchyInvariantProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.DirectJob RebuildBound.Spec

theorem prep_aAll (t : Output) : (prepInputs t).aAll = t.records := rfl

section
variable (g : HierarchyGeometry)
variable {tr : Trace} {N : Nat}

theorem top_table_eqFor (F : LowFacts g.cfg g.rows g.direct) (words : Words) {v : Nat} (hv : g.cfg.seed g.cfg.levels < v) :
    table g.cfg g.shapes tr words g.cfg.levels v =
      (topReference g.top tr.unsh (jobWord g.cfg words g.cfg.levels v)
        (finishInputsAt g.cfg g.shapes tr words v)).output := by
  have := F.levels2
  rw [table_step (by omega) le_rfl hv]
  simp only [step, if_true]
  rw [if_neg (by omega)]
  rfl

theorem top_base_eqFor (hInit : g.cfg.initialized = true) (words : Words) {v : Nat} (hv : v ≤ g.cfg.seed g.cfg.levels) :
    table g.cfg g.shapes tr words g.cfg.levels v =
      (tpReference engineRule g.init (fun _ => false)
        (jobWord g.cfg words g.cfg.levels (g.cfg.seed g.cfg.levels))
        ⟨initMain g.init tr.init, []⟩).output := by
  rw [table_base (Or.inr (Or.inr hv))]
  simp only [base, if_true, hInit]
  rfl

/-- The empty-start base table is independent of the tape. -/
theorem top_base_emptyFor (hInit : g.cfg.initialized = false) (words : Words)
    {v : Nat} (hv : v ≤ g.cfg.seed g.cfg.levels) :
    table g.cfg g.shapes tr words g.cfg.levels v =
      ⟨List.replicate g.prep.T (Bucket.empty g.prep.C), []⟩ := by
  rw [table_base (Or.inr (Or.inr hv))]
  simp [base, hInit, HierarchyGeometry.shapes, hierarchyShapesWith]

theorem finishInputsAt_eqFor (words : Words) (v : Nat) :
    finishInputsAt g.cfg g.shapes tr words v =
      finishInputs (tpReference engineRule g.prep tr.unsh (jobWord g.cfg words g.cfg.levels v)
        (prepInputs (table g.cfg g.shapes tr words g.cfg.levels (v - 1)))).output
        (carryOf g.cfg g.shapes tr words g.cfg.levels v) := rfl

theorem prepInputsAt_eqFor (words : Words) (v : Nat) :
    prepInputsAt g.cfg g.shapes tr words v =
      prepInputs (table g.cfg g.shapes tr words g.cfg.levels (v - 1)) := rfl

theorem init_lenFor (G : TopFacts g) (hT : TracePremises g.cfg N tr)
    (hN : N ≤ g.keyCapacity) : tr.init.length ≤ g.init.C / 2 * g.init.T := by
  rw [G.initC, G.topC, G.initT]
  exact (length_le_of_nodup _ hT.initNodup hT.initKeys).trans (hN.trans G.capacity)

/-- Both starts share the top invariant. The initialized start contains the
initial records; the empty start contains none, even if unused trace metadata
supplies an initial list. -/
theorem top_base_outFor_of_initLength (G : TopFacts g) (hT : TracePremises g.cfg N tr)
    (hInitLen : tr.init.length ≤ g.init.C / 2 * g.init.T) (words : Words) {v : Nat}
    (hv : v ≤ g.cfg.seed g.cfg.levels) :
    TInvFor g.top N (jobWord g.cfg words g.cfg.levels (g.cfg.seed g.cfg.levels))
        (table g.cfg g.shapes tr words g.cfg.levels v) ∧
      (table g.cfg g.shapes tr words g.cfg.levels v).records.Perm
        (if g.cfg.initialized then tr.init else []) := by
  cases hInit : g.cfg.initialized with
  | false =>
    rw [top_base_emptyFor g hInit words hv, G.prepT, G.prepC]
    have h := empty_outFor g.top N (jobWord g.cfg words g.cfg.levels (g.cfg.seed g.cfg.levels))
    exact ⟨h.1, by simpa only [hInit, Bool.false_eq_true, ↓reduceIte, h.2] using List.Perm.refl ([] : List Rec)⟩
  | true =>
    rw [top_base_eqFor g hInit words hv]
    simpa only [hInit, ↓reduceIte] using
      init_outFor g.top g.init G.initValid G.initC G.initT tr.init _
        hInitLen hT.initNodup hT.initKeys


/-- Legacy bounded-universe wrapper; semantic initialization needs only its list length. -/
theorem top_base_outFor (G : TopFacts g) (hT : TracePremises g.cfg N tr)
    (hN : N ≤ g.keyCapacity) (words : Words) {v : Nat}
    (hv : v ≤ g.cfg.seed g.cfg.levels) :
    TInvFor g.top N (jobWord g.cfg words g.cfg.levels (g.cfg.seed g.cfg.levels))
        (table g.cfg g.shapes tr words g.cfg.levels v) ∧
      (table g.cfg g.shapes tr words g.cfg.levels v).records.Perm
        (if g.cfg.initialized then tr.init else []) :=
  top_base_outFor_of_initLength g G hT (init_lenFor g G hT hN) words hv

/-- The carry consumed at level `2 ≤ ℓ ≤ L`. -/
theorem carry_invFor (F : LowFacts g.cfg g.rows g.direct) (hT : TracePremises g.cfg N tr) (words : Words) {ℓ v : Nat}
    (h2 : 2 ≤ ℓ) (hL : ℓ ≤ g.cfg.levels) (hv : g.cfg.seed ℓ < v) :
    CInv g.cfg N ℓ (jobWord g.cfg words ℓ v) (carryOf g.cfg g.shapes tr words ℓ v) := by
  obtain ⟨hc2, -, -⟩ := F.fan (ℓ - 1) (by omega) (by omega)
  have hseed : g.cfg.seed (ℓ - 1) < v * g.cfg.fanout (ℓ - 1) := by
    have := F.seed (ℓ - 1) (by omega) (by omega)
    rw [show ℓ - 1 + 1 = ℓ by omega] at this
    rw [this, Nat.mul_comm v]
    exact Nat.mul_lt_mul_of_pos_left hv (by omega)
  have := (lowFor g F hT words (ℓ - 1) (by omega) (by omega) _ hseed).1
  rw [jobWord_carry g.cfg words v h2 hL (by omega)] at this
  exact carry_ofFor F h2 hL (by omega) this

/-- The carry consumed by the top finish. -/
theorem top_carryFor (F : LowFacts g.cfg g.rows g.direct) (hT : TracePremises g.cfg N tr) (words : Words) {v : Nat}
    (hv : g.cfg.seed g.cfg.levels < v) :
    CInv g.cfg N g.cfg.levels (jobWord g.cfg words g.cfg.levels v)
      (carryOf g.cfg g.shapes tr words g.cfg.levels v) := by
  exact carry_invFor g F hT words F.levels2 le_rfl hv

/-- The top step at a potential ordinal, from the previous top table. -/
theorem top_stepFor (F : LowFacts g.cfg g.rows g.direct) (G : TopFacts g) (hT : TracePremises g.cfg N tr)
    (hU : UnshPromise g.cfg g.shapes tr) (words : Words) {v : Nat}
    (hv : g.cfg.seed g.cfg.levels < v) (hvh : v ≤ g.cfg.seed g.cfg.levels + g.cfg.ordinals g.cfg.levels)
    (hp : TInvFor g.top N (jobWord g.cfg words g.cfg.levels (v - 1))
      (table g.cfg g.shapes tr words g.cfg.levels (v - 1))) :
    TopShape g.top tr.unsh (jobWord g.cfg words g.cfg.levels v)
        (finishInputsAt g.cfg g.shapes tr words v) ∧
      TInvFor g.top N (jobWord g.cfg words g.cfg.levels v) (table g.cfg g.shapes tr words g.cfg.levels v) ∧
      (table g.cfg g.shapes tr words g.cfg.levels v).records.Perm
        (finishInputsAt g.cfg g.shapes tr words v).live ∧
      (finishInputsAt g.cfg g.shapes tr words v).aAll.Perm
        ((prepInputsAt g.cfg g.shapes tr words v).survivors tr.unsh) := by
  have hc := top_carryFor g F hT words hv
  obtain ⟨pperm, plen, planes, phome, pfull⟩ := prep_outFor g.top g.prep G.prepValid G.prepC G.prepT tr.unsh (jobWord g.cfg words g.cfg.levels v) hp
  have hun := hU words v (finish_mem hv hvh)
  rw [finishInputsAt_eqFor g] at hun
  have h := finish_stepFor g.top G.topValid tr.unsh hp pperm plen planes phome pfull G.carryTop hc.len (by simpa only [G.topC] using hc.lanes) hc.nodup
    hc.home hc.below hun
  rw [top_table_eqFor g F words hv, finishInputsAt_eqFor g, prepInputsAt_eqFor g, fin_aAll]
  exact ⟨h.1, h.2.1, h.2.2, pperm⟩

/-- The top tables within the horizon. -/
theorem top_invFor_of_initLength (F : LowFacts g.cfg g.rows g.direct) (G : TopFacts g) (hT : TracePremises g.cfg N tr) (hInitLen : tr.init.length ≤ g.init.C / 2 * g.init.T)
    (hU : UnshPromise g.cfg g.shapes tr) (words : Words) :
    ∀ v, v ≤ g.cfg.seed g.cfg.levels + g.cfg.ordinals g.cfg.levels →
      TInvFor g.top N (jobWord g.cfg words g.cfg.levels (max v (g.cfg.seed g.cfg.levels)))
        (table g.cfg g.shapes tr words g.cfg.levels v) := by
  intro v
  induction v with
  | zero =>
    intro _
    rw [Nat.max_eq_right (Nat.zero_le _)]
    exact (top_base_outFor_of_initLength g G hT hInitLen words (Nat.zero_le _)).1
  | succ v ih =>
    intro hvh
    by_cases hv : g.cfg.seed g.cfg.levels < v + 1
    · have hp := ih (by omega)
      rw [Nat.max_eq_left (by omega)]
      rw [Nat.max_eq_left (by omega)] at hp
      exact (top_stepFor g F G hT hU words hv hvh hp).2.1
    · rw [Nat.max_eq_right (by omega)]
      exact (top_base_outFor_of_initLength g G hT hInitLen words (by omega)).1


/-- Legacy bounded-universe wrapper for the length-based structural induction. -/
theorem top_invFor (F : LowFacts g.cfg g.rows g.direct) (G : TopFacts g)
    (hT : TracePremises g.cfg N tr) (hN : N ≤ g.keyCapacity)
    (hU : UnshPromise g.cfg g.shapes tr) (words : Words) :
    ∀ v, v ≤ g.cfg.seed g.cfg.levels + g.cfg.ordinals g.cfg.levels →
      TInvFor g.top N (jobWord g.cfg words g.cfg.levels (max v (g.cfg.seed g.cfg.levels)))
        (table g.cfg g.shapes tr words g.cfg.levels v) :=
  top_invFor_of_initLength g F G hT (init_lenFor g G hT hN) hU words

theorem top_inv'For_of_initLength (F : LowFacts g.cfg g.rows g.direct) (G : TopFacts g) (hT : TracePremises g.cfg N tr) (hInitLen : tr.init.length ≤ g.init.C / 2 * g.init.T)
    (hU : UnshPromise g.cfg g.shapes tr) (words : Words) {v : Nat}
    (h1 : g.cfg.seed g.cfg.levels ≤ v) (h2 : v ≤ g.cfg.seed g.cfg.levels + g.cfg.ordinals g.cfg.levels) :
    TInvFor g.top N (jobWord g.cfg words g.cfg.levels v) (table g.cfg g.shapes tr words g.cfg.levels v) := by
  have := top_invFor_of_initLength g F G hT hInitLen hU words v h2
  rwa [Nat.max_eq_left h1] at this


theorem top_inv'For (F : LowFacts g.cfg g.rows g.direct) (G : TopFacts g)
    (hT : TracePremises g.cfg N tr) (hN : N ≤ g.keyCapacity)
    (hU : UnshPromise g.cfg g.shapes tr) (words : Words) {v : Nat}
    (h1 : g.cfg.seed g.cfg.levels ≤ v)
    (h2 : v ≤ g.cfg.seed g.cfg.levels + g.cfg.ordinals g.cfg.levels) :
    TInvFor g.top N (jobWord g.cfg words g.cfg.levels v)
      (table g.cfg g.shapes tr words g.cfg.levels v) :=
  top_inv'For_of_initLength g F G hT (init_lenFor g G hT hN) hU words h1 h2

/-- The top's record sets within the horizon do not depend on the tape. -/
theorem top_recsFor (F : LowFacts g.cfg g.rows g.direct) (G : TopFacts g) (hT : TracePremises g.cfg N tr) (hN : N ≤ g.keyCapacity)
    (hU : UnshPromise g.cfg g.shapes tr) (words words' : Words) :
    ∀ v, v ≤ g.cfg.seed g.cfg.levels + g.cfg.ordinals g.cfg.levels →
      (table g.cfg g.shapes tr words g.cfg.levels v).records.toFinset =
        (table g.cfg g.shapes tr words' g.cfg.levels v).records.toFinset := by
  have hI : ∀ ws : Words, ∀ v, v ≤ g.cfg.seed g.cfg.levels →
      (table g.cfg g.shapes tr ws g.cfg.levels v).records.toFinset =
        (if g.cfg.initialized then tr.init else []).toFinset := by
    intro ws v hv
    exact List.toFinset_eq_of_perm _ _ (top_base_outFor g G hT hN ws hv).2
  have hS : ∀ ws : Words, ∀ v, g.cfg.seed g.cfg.levels < v →
      v ≤ g.cfg.seed g.cfg.levels + g.cfg.ordinals g.cfg.levels →
      (table g.cfg g.shapes tr ws g.cfg.levels v).records.toFinset =
        (winSet ((table g.cfg g.shapes tr ws g.cfg.levels (v - 1)).records.filter
            fun r => !flagged tr.unsh r).toFinset
          (carryOf g.cfg g.shapes tr ws g.cfg.levels v).records.toFinset).filter
          fun r => !r.tomb := by
    intro ws v hv hvh
    have h := top_stepFor g F G hT hU ws hv hvh (top_inv'For g F G hT hN hU ws (by omega) (by omega))
    rw [List.toFinset_eq_of_perm _ _ h.2.2.1]
    unfold TopInputs.live
    rw [List.toFinset_filter, tWinners_eq, win_toFinset,
      List.toFinset_eq_of_perm _ _ h.2.2.2, prepInputsAt_eqFor g, survivors_eq, finishInputsAt_eqFor g,
      fin_bAll]
  intro v hvh
  induction v with
  | zero => rw [hI words 0 (Nat.zero_le _), hI words' 0 (Nat.zero_le _)]
  | succ v ih =>
    by_cases hv : g.cfg.seed g.cfg.levels < v + 1
    · rw [hS words (v + 1) hv hvh, hS words' (v + 1) hv hvh]
      simp only [Nat.add_sub_cancel]
      rw [List.toFinset_filter, List.toFinset_filter, ih (by omega)]
      have := F.levels2
      rw [show (carryOf g.cfg g.shapes tr words g.cfg.levels (v + 1)).records.toFinset =
          (carryOf g.cfg g.shapes tr words' g.cfg.levels (v + 1)).records.toFinset from
        low_recsFor g F hT words words' (g.cfg.levels - 1) (by omega) (by omega) _]
    · rw [hI words (v + 1) (by omega), hI words' (v + 1) (by omega)]

/-- Every key of a top table lies below `N`, at every top ordinal. -/
theorem top_belowFor (F : LowFacts g.cfg g.rows g.direct) (G : TopFacts g) (hT : TracePremises g.cfg N tr) (hN : N ≤ g.keyCapacity)
    (words : Words) :
    ∀ v, ∀ x ∈ (table g.cfg g.shapes tr words g.cfg.levels v).records, x.key.toNat < N := by
  intro v
  induction v with
  | zero =>
    exact (top_base_outFor g G hT hN words (Nat.zero_le _)).1.below
  | succ v ih =>
    by_cases hv : g.cfg.seed g.cfg.levels < v + 1
    · rw [top_table_eqFor g F words hv]
      apply topReference_P (P := fun x => x.key.toNat < N)
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · rw [finishInputsAt_eqFor g, fin_aAll] at h
        refine tpReference_P (P := fun x => x.key.toNat < N) _ _ _ _ ?_ x h
        intro y hy
        rw [prep_aAll, Nat.add_sub_cancel] at hy
        exact ih y hy
      · rw [finishInputsAt_eqFor g, fin_bAll] at h
        have hL2 := F.levels2
        exact low_belowFor g F hT words (by omega) (by omega) _ x h
    · exact (top_base_outFor g G hT hN words (by omega)).1.below

end

end RebuildBound.HierarchyInvariantProof
