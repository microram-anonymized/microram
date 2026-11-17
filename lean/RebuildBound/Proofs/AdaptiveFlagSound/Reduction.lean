import RebuildBound.Proofs.UnshReduction
import RebuildBound.Proofs.OnlineCorrectness

/-!
# AdaptiveFlagSound: the localized top induction over explicit geometry

`Proofs/UnshReduction.lean` at an explicit `HierarchyGeometry` (lower facts
`LowFacts`, top facts `TopFacts`) instead of the two selected configurations:
the top step, invariant and record sets with the unshadowed promise only at
the finishes up to the current ordinal, under one tape, and the reduction
`unshPromise_of_sufficientFor` (the word-independent sufficient form at every
potential finish under one tape implies `UnshPromise`).

`top_raw`: the raw (tombstones kept) lookup in a top table, from the
initialization and the consumed trace prefix, with the promise only at the
finishes up to the table's ordinal under its own tape. Initialization is
bounded by its actual input length, independently of the trace's numeric key bound.
-/

namespace RebuildBound.AdaptiveFlagSoundProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.DirectJob RebuildBound.Spec
open RebuildBound.HierarchyInvariantProof RebuildBound.OnlineCorrectnessProof RebuildBound.OnlineFreshProof
open RebuildBound.Oracle.HierarchyDiff (UnshInstance UnshSufficient UnshSufficient.instance)

section
variable (geo : HierarchyGeometry) {tr : Trace} {N : Nat}

/-- The promise's body at one finish under one tape. -/
abbrev Inst (geo : HierarchyGeometry) (tr : Trace) (ws : Words) (v : Nat) : Prop :=
  UnshInstance tr.unsh (finishInputsAt geo.cfg geo.shapes tr ws v)

/-- `top_stepFor` with the promise at this one finish only. -/
theorem top_step_loc (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hT : TracePremises geo.cfg N tr) (words : Words) {v : Nat}
    (hv : geo.cfg.seed geo.cfg.levels < v) (hun : Inst geo tr words v)
    (hp : TInvFor geo.top N (jobWord geo.cfg words geo.cfg.levels (v - 1))
      (table geo.cfg geo.shapes tr words geo.cfg.levels (v - 1))) :
    TopShape geo.top tr.unsh (jobWord geo.cfg words geo.cfg.levels v)
        (finishInputsAt geo.cfg geo.shapes tr words v) ∧
      TInvFor geo.top N (jobWord geo.cfg words geo.cfg.levels v)
        (table geo.cfg geo.shapes tr words geo.cfg.levels v) ∧
      (table geo.cfg geo.shapes tr words geo.cfg.levels v).records.Perm
        (finishInputsAt geo.cfg geo.shapes tr words v).live ∧
      (finishInputsAt geo.cfg geo.shapes tr words v).aAll.Perm
        ((prepInputsAt geo.cfg geo.shapes tr words v).survivors tr.unsh) := by
  have hc := top_carryFor geo F hT words hv
  obtain ⟨pperm, plen, planes, phome, pfull⟩ := prep_outFor geo.top geo.prep G.prepValid G.prepC
    G.prepT tr.unsh (jobWord geo.cfg words geo.cfg.levels v) hp
  have hun' := hun
  unfold Inst UnshInstance at hun'
  rw [finishInputsAt_eqFor geo] at hun'
  have h := finish_stepFor geo.top G.topValid tr.unsh hp pperm plen planes phome pfull G.carryTop
    hc.len (by simpa only [G.topC] using hc.lanes) hc.nodup hc.home hc.below hun'
  rw [top_table_eqFor geo F words hv, finishInputsAt_eqFor geo, prepInputsAt_eqFor geo, fin_aAll]
  exact ⟨h.1, h.2.1, h.2.2, pperm⟩

theorem init_out (G : TopFacts geo) (hT : TracePremises geo.cfg N tr)
    (hInitLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T) (w : LogicalKey → Nat) :
    TInvFor geo.top N w (tpReference engineRule geo.init (fun _ => false) w
        ⟨initMain geo.init tr.init, []⟩).output ∧
      (tpReference engineRule geo.init (fun _ => false) w
        ⟨initMain geo.init tr.init, []⟩).output.records.Perm tr.init :=
  init_outFor geo.top geo.init G.initValid G.initC G.initT tr.init _ hInitLen
    hT.initNodup hT.initKeys

/-- `top_invFor` with the promise at the finishes up to `v` only. -/
theorem top_inv_loc (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hT : TracePremises geo.cfg N tr) (hInitLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T) (words : Words) :
    ∀ v, (∀ v', geo.cfg.seed geo.cfg.levels < v' → v' ≤ v → Inst geo tr words v') →
      TInvFor geo.top N (jobWord geo.cfg words geo.cfg.levels (max v (geo.cfg.seed geo.cfg.levels)))
        (table geo.cfg geo.shapes tr words geo.cfg.levels v) := by
  intro v
  induction v with
  | zero =>
    intro _
    rw [Nat.max_eq_right (Nat.zero_le _)]
    exact (top_base_outFor_of_initLength geo G hT hInitLen words (Nat.zero_le _)).1
  | succ v ih =>
    intro hI
    by_cases hv : geo.cfg.seed geo.cfg.levels < v + 1
    · have hp := ih (fun v' h1 h2 => hI v' h1 (by omega))
      rw [Nat.max_eq_left (by omega)]
      have hun := hI (v + 1) hv le_rfl
      rw [Nat.max_eq_left (by omega)] at hp
      exact (top_step_loc geo F G hT words hv hun hp).2.1
    · rw [Nat.max_eq_right (by omega)]
      exact (top_base_outFor_of_initLength geo G hT hInitLen words (by omega)).1

theorem top_inv_loc' (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hT : TracePremises geo.cfg N tr) (hInitLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T) (words : Words) {v : Nat}
    (h1 : geo.cfg.seed geo.cfg.levels ≤ v)
    (hI : ∀ v', geo.cfg.seed geo.cfg.levels < v' → v' ≤ v → Inst geo tr words v') :
    TInvFor geo.top N (jobWord geo.cfg words geo.cfg.levels v)
      (table geo.cfg geo.shapes tr words geo.cfg.levels v) := by
  have := top_inv_loc geo F G hT hInitLen words v hI
  rwa [Nat.max_eq_left h1] at this

/-- Every top table is distinct by key, with the promise up to its ordinal. -/
theorem top_nodup_loc (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hT : TracePremises geo.cfg N tr) (hInitLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T) (words : Words) (v : Nat)
    (hI : ∀ v', geo.cfg.seed geo.cfg.levels < v' → v' ≤ v → Inst geo tr words v') :
    ((table geo.cfg geo.shapes tr words geo.cfg.levels v).records.map Rec.key).Nodup :=
  (top_inv_loc geo F G hT hInitLen words v hI).nodup

/-- `top_recsFor` with the promise at the finishes up to `v` (both tapes) only. -/
theorem top_recs_loc (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hT : TracePremises geo.cfg N tr) (hInitLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T) (words words' : Words) :
    ∀ v, (∀ v', geo.cfg.seed geo.cfg.levels < v' → v' ≤ v →
        Inst geo tr words v' ∧ Inst geo tr words' v') →
      (table geo.cfg geo.shapes tr words geo.cfg.levels v).records.toFinset =
        (table geo.cfg geo.shapes tr words' geo.cfg.levels v).records.toFinset := by
  have hI : ∀ ws : Words, ∀ v, v ≤ geo.cfg.seed geo.cfg.levels →
      (table geo.cfg geo.shapes tr ws geo.cfg.levels v).records.toFinset =
        (if geo.cfg.initialized then tr.init else []).toFinset := by
    intro ws v hv
    exact List.toFinset_eq_of_perm _ _ (top_base_outFor_of_initLength geo G hT hInitLen ws hv).2
  have hS : ∀ ws : Words, ∀ v, geo.cfg.seed geo.cfg.levels < v →
      (∀ v', geo.cfg.seed geo.cfg.levels < v' → v' ≤ v → Inst geo tr ws v') →
      (table geo.cfg geo.shapes tr ws geo.cfg.levels v).records.toFinset =
        (winSet ((table geo.cfg geo.shapes tr ws geo.cfg.levels (v - 1)).records.filter
            fun r => !flagged tr.unsh r).toFinset
          (carryOf geo.cfg geo.shapes tr ws geo.cfg.levels v).records.toFinset).filter
          fun r => !r.tomb := by
    intro ws v hv hIv
    have h := top_step_loc geo F G hT ws hv (hIv v hv le_rfl)
      (top_inv_loc' geo F G hT hInitLen ws (by omega) (fun v' a b => hIv v' a (by omega)))
    rw [List.toFinset_eq_of_perm _ _ h.2.2.1]
    unfold TopInputs.live
    rw [List.toFinset_filter, tWinners_eq, win_toFinset,
      List.toFinset_eq_of_perm _ _ h.2.2.2, prepInputsAt_eqFor geo, survivors_eq,
      finishInputsAt_eqFor geo, fin_bAll]
  intro v
  induction v with
  | zero => intro _; rw [hI words 0 (Nat.zero_le _), hI words' 0 (Nat.zero_le _)]
  | succ v ih =>
    intro hB
    by_cases hv : geo.cfg.seed geo.cfg.levels < v + 1
    · rw [hS words (v + 1) hv (fun v' a b => (hB v' a b).1),
        hS words' (v + 1) hv (fun v' a b => (hB v' a b).2)]
      simp only [Nat.add_sub_cancel]
      rw [List.toFinset_filter, List.toFinset_filter, ih (fun v' a b => hB v' a (by omega))]
      have := F.levels2
      rw [show (carryOf geo.cfg geo.shapes tr words geo.cfg.levels (v + 1)).records.toFinset =
          (carryOf geo.cfg geo.shapes tr words' geo.cfg.levels (v + 1)).records.toFinset from
        low_recsFor geo F hT words words' (geo.cfg.levels - 1) (by omega) (by omega) _]
    · rw [hI words (v + 1) (by omega), hI words' (v + 1) (by omega)]

/-- The finish's A records (as a set) at `ws`, from the previous top table. -/
theorem finish_aAll_set (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hT : TracePremises geo.cfg N tr) (hInitLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T)
    (ws : Words) {o : Nat} (ho : geo.cfg.seed geo.cfg.levels < o)
    (hI : ∀ v', geo.cfg.seed geo.cfg.levels < v' → v' ≤ o - 1 → Inst geo tr ws v') :
    (finishInputsAt geo.cfg geo.shapes tr ws o).aAll.toFinset =
      ((table geo.cfg geo.shapes tr ws geo.cfg.levels (o - 1)).records.filter
          fun r => !flagged tr.unsh r).toFinset := by
  have hp := top_inv_loc' geo F G hT hInitLen ws (v := o - 1) (by omega) hI
  have pperm := (prep_outFor geo.top geo.prep G.prepValid G.prepC G.prepT tr.unsh
    (jobWord geo.cfg ws geo.cfg.levels o) hp).1
  rw [finishInputsAt_eqFor geo, fin_aAll, List.toFinset_eq_of_perm _ _ pperm, survivors_eq]

/-- **The reduction.** The sufficient form at every potential finish under one
tape `w0` implies the promise under every tape. -/
theorem unshPromise_of_sufficientFor (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hT : TracePremises geo.cfg N tr) (hInitLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T) (w0 : Words)
    (hS : ∀ o, JobId.topFinish o ∈ geo.cfg.potentialJobs →
      UnshSufficient tr.unsh (finishInputsAt geo.cfg geo.shapes tr w0 o)) :
    UnshPromise geo.cfg geo.shapes tr := by
  have hL2 := F.levels2
  have h0 : ∀ o, geo.cfg.seed geo.cfg.levels < o →
      o ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels →
      Inst geo tr w0 o := fun o h1 h2 =>
    UnshSufficient.instance (fun x hx => hx) (fun x hx => hx) (hS o (finish_mem h1 h2))
  have key : ∀ o, ∀ ws : Words, geo.cfg.seed geo.cfg.levels < o →
      o ≤ geo.cfg.seed geo.cfg.levels + geo.cfg.ordinals geo.cfg.levels → Inst geo tr ws o := by
    intro o
    induction o using Nat.strong_induction_on with
    | _ o ih =>
      intro ws h1 h2
      have hIws : ∀ v', geo.cfg.seed geo.cfg.levels < v' → v' ≤ o - 1 → Inst geo tr ws v' :=
        fun v' a b => ih v' (by omega) ws a (by omega)
      have hIw0 : ∀ v', geo.cfg.seed geo.cfg.levels < v' → v' ≤ o - 1 → Inst geo tr w0 v' :=
        fun v' a b => h0 v' a (by omega)
      have hrec := top_recs_loc geo F G hT hInitLen ws w0 (o - 1)
        (fun v' a b => ⟨hIws v' a b, hIw0 v' a b⟩)
      have hA : (finishInputsAt geo.cfg geo.shapes tr ws o).aAll.toFinset =
          (finishInputsAt geo.cfg geo.shapes tr w0 o).aAll.toFinset := by
        rw [finish_aAll_set geo F G hT hInitLen ws h1 hIws, finish_aAll_set geo F G hT hInitLen w0 h1 hIw0,
          List.toFinset_filter, List.toFinset_filter, hrec]
      have hB : (finishInputsAt geo.cfg geo.shapes tr ws o).bAll.toFinset =
          (finishInputsAt geo.cfg geo.shapes tr w0 o).bAll.toFinset := by
        rw [finishInputsAt_eqFor geo, finishInputsAt_eqFor geo, fin_bAll, fin_bAll]
        unfold carryOf
        exact low_recsFor geo F hT ws w0 (geo.cfg.levels - 1) (by omega) (by omega) _
      refine UnshSufficient.instance (inp := finishInputsAt geo.cfg geo.shapes tr w0 o)
        ?_ ?_ (hS o (finish_mem h1 h2))
      · intro x hx
        have : x ∈ (finishInputsAt geo.cfg geo.shapes tr ws o).aAll.toFinset :=
          List.mem_toFinset.2 hx
        rw [hA] at this
        exact List.mem_toFinset.1 this
      · intro x hx
        have : x ∈ (finishInputsAt geo.cfg geo.shapes tr ws o).bAll.toFinset :=
          List.mem_toFinset.2 hx
        rw [hB] at this
        exact List.mem_toFinset.1 this
  intro ws o hj
  obtain ⟨h1, h2⟩ := pj_top (Or.inr hj)
  exact key o ws h1 h2

/-! ### The raw lookup in a top table -/

/-- The initialization and the trace prefix consumed by the top table `v`. -/
def topHist (geo : HierarchyGeometry) (tr : Trace) (v : Nat) : List Rec :=
  tr.init ++ traceSlice tr 0 (unitEnd geo.cfg geo.cfg.levels v)

theorem unitEnd_top_seed (F : LowFacts geo.cfg geo.rows geo.direct) {v : Nat}
    (hv : v ≤ geo.cfg.seed geo.cfg.levels) : unitEnd geo.cfg geo.cfg.levels v = 0 := by
  have := unitEnd_mono geo.cfg geo.cfg.levels hv
  rw [unitEnd_seed F (by have := F.levels2; omega) le_rfl] at this
  omega

theorem orElse_filter_filter (a b : Option Rec) (p q : Rec → Bool)
    (h : ∀ x, p x = true → q x = true) :
    (a.orElse (fun _ => b.filter q)).filter p = (a.orElse (fun _ => b)).filter p := by
  cases a with
  | some x => rfl
  | none =>
    cases b with
    | none => rfl
    | some y =>
      by_cases hp : p y = true
      · simp [Option.filter, h y hp, hp]
      · cases hq : q y <;> simp [Option.filter, hq, hp]

/-- The raw lookup in the top table `v`: the initialization's at and below the
seed, otherwise the newest record of the history if it is live. -/
theorem top_raw (F : LowFacts geo.cfg geo.rows geo.direct) (G : TopFacts geo)
    (hInit : geo.cfg.initialized = false → tr.init = []) (hT : TracePremises geo.cfg N tr) (hInitLen : tr.init.length ≤ geo.init.C / 2 * geo.init.T) (words : Words) :
    ∀ v, (∀ v', geo.cfg.seed geo.cfg.levels < v' → v' ≤ v → Inst geo tr words v') → ∀ key,
      DirectPrefix.latest key (table geo.cfg geo.shapes tr words geo.cfg.levels v).records =
        if v ≤ geo.cfg.seed geo.cfg.levels then DirectPrefix.latest key (topHist geo tr v)
        else (DirectPrefix.latest key (topHist geo tr v)).filter fun r => !r.tomb := by
  have hL2 := F.levels2
  have hbase : ∀ v, v ≤ geo.cfg.seed geo.cfg.levels → ∀ key,
      DirectPrefix.latest key (table geo.cfg geo.shapes tr words geo.cfg.levels v).records =
        DirectPrefix.latest key (topHist geo tr v) := by
    intro v hv key
    rw [topHist, unitEnd_top_seed geo F hv, traceSlice_self, List.append_nil]
    have hb := top_base_outFor_of_initLength geo G hT hInitLen words hv
    have he : (if geo.cfg.initialized then tr.init else []) = tr.init := by
      cases hi : geo.cfg.initialized <;> simp [hi, hInit]
    rw [he] at hb
    exact latest_perm hb.2 hb.1.nodup
  intro v
  induction v with
  | zero => intro _ key; rw [ite_eq_left (Nat.zero_le _)]; exact hbase 0 (Nat.zero_le _) key
  | succ v ih =>
    intro hI key
    by_cases hv : v + 1 ≤ geo.cfg.seed geo.cfg.levels
    · rw [ite_eq_left hv]; exact hbase (v + 1) hv key
    rw [ite_eq_right hv]
    have hv' : geo.cfg.seed geo.cfg.levels < v + 1 := by omega
    have hIv : ∀ v', geo.cfg.seed geo.cfg.levels < v' → v' ≤ v → Inst geo tr words v' :=
      fun v' a b => hI v' a (by omega)
    have hp := top_inv_loc' geo F G hT hInitLen words (v := v) (by omega) hIv
    have hs := top_step_loc geo F G hT words hv' (hI (v + 1) hv' le_rfl)
      (by simpa only [Nat.add_sub_cancel] using hp)
    -- the A side: the previous table's survivors
    have hA : DirectPrefix.latest key (finishInputsAt geo.cfg geo.shapes tr words (v + 1)).aAll =
        (DirectPrefix.latest key (table geo.cfg geo.shapes tr words geo.cfg.levels v).records).filter
          fun r => !flagged tr.unsh r := by
      rw [latest_perm hs.2.2.2 hs.1.aNodup, prepInputsAt_eqFor geo, survivors_eq,
        Nat.add_sub_cancel, latest_filter_unique hp.nodup]
    -- the B side: the carry's trace slice
    have hB : DirectPrefix.latest key (finishInputsAt geo.cfg geo.shapes tr words (v + 1)).bAll =
        DirectPrefix.latest key (traceSlice tr (unitEnd geo.cfg geo.cfg.levels v)
          (unitEnd geo.cfg geo.cfg.levels (v + 1))) := by
      have hf := fanout_pos F (ℓ := geo.cfg.levels - 1) (by omega) (by omega)
      have hseed : geo.cfg.seed (geo.cfg.levels - 1) < (v + 1) * geo.cfg.fanout (geo.cfg.levels - 1) := by
        rw [F.seed (geo.cfg.levels - 1) (by omega) (by omega), Nat.sub_add_cancel (by omega),
          Nat.mul_comm]
        exact Nat.mul_lt_mul_of_pos_right hv' hf
      rw [finishInputsAt_eqFor geo, fin_bAll]
      change DirectPrefix.latest key (table geo.cfg geo.shapes tr words
        (geo.cfg.levels - 1) ((v + 1) * geo.cfg.fanout (geo.cfg.levels - 1))).records = _
      rw [low_latestFor geo F hT words (geo.cfg.levels - 1) (by omega) (by omega) _ hseed key,
        unitEnd_carry_start F (by omega) (by omega) (by omega),
        unitEnd_carry F (by omega) (by omega), Nat.sub_add_cancel (by omega), Nat.add_sub_cancel]
    rw [latest_perm hs.2.2.1 hs.2.1.nodup]
    unfold TopInputs.live
    rw [tWinners_eq, latest_filter_unique (win_nodup hs.1.aNodup hs.1.bNodup), latest_win,
      latest_append, hA, hB, ih hIv key]
    have hsplit : topHist geo tr (v + 1) = topHist geo tr v ++
        traceSlice tr (unitEnd geo.cfg geo.cfg.levels v) (unitEnd geo.cfg geo.cfg.levels (v + 1)) := by
      rw [topHist, topHist, List.append_assoc, ← traceSlice_append tr (Nat.zero_le _)
        (unitEnd_mono geo.cfg geo.cfg.levels (Nat.le_succ v))]
    rw [hsplit, latest_append]
    split_ifs
    · apply orElse_filter_filter
      intro x hx
      cases hx' : x.tomb <;> simp_all [flagged]
    · rw [Option.filter_filter]
      apply orElse_filter_filter
      intro x hx
      cases hx' : x.tomb <;> simp_all [flagged]

end

end RebuildBound.AdaptiveFlagSoundProof
