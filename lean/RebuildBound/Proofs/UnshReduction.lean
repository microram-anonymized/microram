import RebuildBound.Proofs.HierarchyInvariant
import RebuildBound.Oracle.HierarchyDiff

/-!
# UnshReduction: the replay's sufficient form implies the unshadowed promise

Not a registered statement: the sufficient form `UnshSufficient` is the
replay's check (`Oracle/HierarchyDiff.lean`), not a Spec definition. Kernel-checked
with the library.

* `unshPromise_of_sufficient`: the word-independent sufficient form at every
  potential top finish under ONE tape implies `UnshPromise` (every tape), by
  strong induction over the top ordinals, reusing `HierarchyInvariant`'s
  lemmas with the promise localised to the finishes at or below the current
  ordinal.
* `unshPromise_of_flagSound`: a word-free condition on the trace. The logical
  top `logTop` folds the carries' record sets (word-independent, `low_recs`)
  as the reference top does. `FlagSound`: no flagged tombstone of a potential
  finish's carry has a live record of its key in the logical top before it.
  `unshPromise_selected` instantiates it at both selected configurations.

That the engine's flags satisfy `FlagSound` remains an informal argument.
-/

namespace RebuildBound.UnshReductionProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.DirectJob RebuildBound.Spec
open RebuildBound.HierarchyInvariantProof
open RebuildBound.Oracle.HierarchyDiff (UnshInstance UnshSufficient UnshSufficient.instance)

section
variable {cfg : Config} {rows : List (SepGeom × Nat)} {tr : Trace} {N : Nat}

/-- The promise's body at one finish under one tape. -/
abbrev Inst (cfg : Config) (rows : List (SepGeom × Nat)) (tr : Trace) (ws : Words) (v : Nat) : Prop :=
  UnshInstance tr.unsh (finishInputsAt cfg (hierarchyShapes cfg rows) tr ws v)

/-- `top_step` with the promise at this one finish only. -/
theorem top_step_loc (F : Facts cfg rows) (hT : TracePremises cfg N tr) (words : Words) {v : Nat}
    (hv : cfg.seed cfg.levels < v)
    (hun : Inst cfg rows tr words v)
    (hp : TInv N (jobWord cfg words cfg.levels (v - 1))
      (table cfg (hierarchyShapes cfg rows) tr words cfg.levels (v - 1))) :
    TopShape selectedTop tr.unsh (jobWord cfg words cfg.levels v)
        (finishInputsAt cfg (hierarchyShapes cfg rows) tr words v) ∧
      TInv N (jobWord cfg words cfg.levels v) (table cfg (hierarchyShapes cfg rows) tr words cfg.levels v) ∧
      (table cfg (hierarchyShapes cfg rows) tr words cfg.levels v).records.Perm
        (finishInputsAt cfg (hierarchyShapes cfg rows) tr words v).live ∧
      (finishInputsAt cfg (hierarchyShapes cfg rows) tr words v).aAll.Perm
        ((prepInputsAt cfg (hierarchyShapes cfg rows) tr words v).survivors tr.unsh) := by
  have hc := top_carry F hT words hv
  obtain ⟨pperm, plen, planes, phome, pfull⟩ := prep_out tr.unsh (jobWord cfg words cfg.levels v) hp
  have hun' := hun
  unfold Inst UnshInstance at hun'
  rw [finishInputsAt_eq] at hun'
  have h := finish_step tr.unsh hp pperm plen planes phome pfull F.carryTop hc.len hc.lanes hc.nodup
    hc.home hc.below hun'
  rw [top_table_eq F words hv, finishInputsAt_eq, prepInputsAt_eq, fin_aAll]
  exact ⟨h.1, h.2.1, h.2.2, pperm⟩

/-- `top_inv` with the promise at the finishes up to `v` only. -/
theorem top_inv_loc (F : Facts cfg rows) (hT : TracePremises cfg N tr) (hN : N ≤ 2 ^ 27)
    (words : Words) :
    ∀ v, (∀ v', cfg.seed cfg.levels < v' → v' ≤ v → Inst cfg rows tr words v') →
      TInv N (jobWord cfg words cfg.levels (max v (cfg.seed cfg.levels)))
        (table cfg (hierarchyShapes cfg rows) tr words cfg.levels v) := by
  intro v
  induction v with
  | zero =>
    intro _
    rw [top_base_eq F words (Nat.zero_le _), Nat.max_eq_right (Nat.zero_le _)]
    exact (init_out tr.init _ (init_len hT hN) hT.initNodup hT.initKeys).1
  | succ v ih =>
    intro hI
    by_cases hv : cfg.seed cfg.levels < v + 1
    · have hp := ih (fun v' h1 h2 => hI v' h1 (by omega))
      rw [Nat.max_eq_left (by omega)]
      have hun := hI (v + 1) hv le_rfl
      by_cases hv' : cfg.seed cfg.levels < v
      · rw [Nat.max_eq_left hv'.le] at hp
        exact (top_step_loc F hT words hv hun hp).2.1
      · rw [Nat.max_eq_right (by omega), show cfg.seed cfg.levels = v by omega] at hp
        exact (top_step_loc F hT words hv hun hp).2.1
    · rw [top_base_eq F words (by omega), Nat.max_eq_right (by omega)]
      exact (init_out tr.init _ (init_len hT hN) hT.initNodup hT.initKeys).1

theorem top_inv_loc' (F : Facts cfg rows) (hT : TracePremises cfg N tr) (hN : N ≤ 2 ^ 27)
    (words : Words) {v : Nat} (h1 : cfg.seed cfg.levels ≤ v)
    (hI : ∀ v', cfg.seed cfg.levels < v' → v' ≤ v → Inst cfg rows tr words v') :
    TInv N (jobWord cfg words cfg.levels v) (table cfg (hierarchyShapes cfg rows) tr words cfg.levels v) := by
  have := top_inv_loc F hT hN words v hI
  rwa [Nat.max_eq_left h1] at this

/-- `top_recs` with the promise at the finishes up to `v` (both tapes) only. -/
theorem top_recs_loc (F : Facts cfg rows) (hT : TracePremises cfg N tr) (hN : N ≤ 2 ^ 27)
    (words words' : Words) :
    ∀ v, (∀ v', cfg.seed cfg.levels < v' → v' ≤ v →
        Inst cfg rows tr words v' ∧ Inst cfg rows tr words' v') →
      (table cfg (hierarchyShapes cfg rows) tr words cfg.levels v).records.toFinset =
        (table cfg (hierarchyShapes cfg rows) tr words' cfg.levels v).records.toFinset := by
  have hI : ∀ ws : Words, ∀ v, v ≤ cfg.seed cfg.levels →
      (table cfg (hierarchyShapes cfg rows) tr ws cfg.levels v).records.toFinset = tr.init.toFinset := by
    intro ws v hv
    rw [top_base_eq F ws hv]
    exact List.toFinset_eq_of_perm _ _
      (init_out (N := N) tr.init _ (init_len hT hN) hT.initNodup hT.initKeys).2
  have hS : ∀ ws : Words, ∀ v, cfg.seed cfg.levels < v →
      (∀ v', cfg.seed cfg.levels < v' → v' ≤ v → Inst cfg rows tr ws v') →
      (table cfg (hierarchyShapes cfg rows) tr ws cfg.levels v).records.toFinset =
        (winSet ((table cfg (hierarchyShapes cfg rows) tr ws cfg.levels (v - 1)).records.filter
            fun r => !flagged tr.unsh r).toFinset
          (carryOf cfg (hierarchyShapes cfg rows) tr ws cfg.levels v).records.toFinset).filter
          fun r => !r.tomb := by
    intro ws v hv hIv
    have h := top_step_loc F hT ws hv (hIv v hv le_rfl)
      (top_inv_loc' F hT hN ws (by omega) (fun v' a b => hIv v' a (by omega)))
    rw [List.toFinset_eq_of_perm _ _ h.2.2.1]
    unfold TopInputs.live
    rw [List.toFinset_filter, tWinners_eq, win_toFinset,
      List.toFinset_eq_of_perm _ _ h.2.2.2, prepInputsAt_eq, survivors_eq, finishInputsAt_eq,
      fin_bAll]
  intro v
  induction v with
  | zero => intro _; rw [hI words 0 (Nat.zero_le _), hI words' 0 (Nat.zero_le _)]
  | succ v ih =>
    intro hB
    by_cases hv : cfg.seed cfg.levels < v + 1
    · rw [hS words (v + 1) hv (fun v' a b => (hB v' a b).1),
        hS words' (v + 1) hv (fun v' a b => (hB v' a b).2)]
      simp only [Nat.add_sub_cancel]
      rw [List.toFinset_filter, List.toFinset_filter, ih (fun v' a b => hB v' a (by omega))]
      have := F.levels2
      rw [show (carryOf cfg (hierarchyShapes cfg rows) tr words cfg.levels (v + 1)).records.toFinset =
          (carryOf cfg (hierarchyShapes cfg rows) tr words' cfg.levels (v + 1)).records.toFinset from
        low_recs F hT words words' (cfg.levels - 1) (by omega) (by omega) _]
    · rw [hI words (v + 1) (by omega), hI words' (v + 1) (by omega)]

/-- The finish's A records (as a set) at `ws`, from the previous top table. -/
theorem finish_aAll_set (F : Facts cfg rows) (hT : TracePremises cfg N tr) (hN : N ≤ 2 ^ 27)
    (ws : Words) {o : Nat} (ho : cfg.seed cfg.levels < o)
    (hI : ∀ v', cfg.seed cfg.levels < v' → v' ≤ o - 1 → Inst cfg rows tr ws v') :
    (finishInputsAt cfg (hierarchyShapes cfg rows) tr ws o).aAll.toFinset =
      ((table cfg (hierarchyShapes cfg rows) tr ws cfg.levels (o - 1)).records.filter
          fun r => !flagged tr.unsh r).toFinset := by
  have hp := top_inv_loc' F hT hN ws (v := o - 1) (by omega) hI
  have pperm := (prep_out tr.unsh (jobWord cfg ws cfg.levels o) hp).1
  rw [finishInputsAt_eq, fin_aAll, List.toFinset_eq_of_perm _ _ pperm, survivors_eq]

/-- **The reduction.** The sufficient form at every potential finish under one
tape `w0` implies the promise under every tape. -/
theorem unshPromise_of_sufficient (F : Facts cfg rows) (hT : TracePremises cfg N tr)
    (hN : N ≤ 2 ^ 27) (w0 : Words)
    (hS : ∀ o, JobId.topFinish o ∈ cfg.potentialJobs →
      UnshSufficient tr.unsh (finishInputsAt cfg (hierarchyShapes cfg rows) tr w0 o)) :
    UnshPromise cfg (hierarchyShapes cfg rows) tr := by
  have hL2 := F.levels2
  -- the promise at w0 itself
  have h0 : ∀ o, cfg.seed cfg.levels < o → o ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels →
      Inst cfg rows tr w0 o := fun o h1 h2 =>
    UnshSufficient.instance (fun x hx => hx) (fun x hx => hx) (hS o (finish_mem h1 h2))
  -- strong induction over the top ordinals
  have key : ∀ o, ∀ ws : Words, cfg.seed cfg.levels < o →
      o ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels → Inst cfg rows tr ws o := by
    intro o
    induction o using Nat.strong_induction_on with
    | _ o ih =>
      intro ws h1 h2
      have hIws : ∀ v', cfg.seed cfg.levels < v' → v' ≤ o - 1 → Inst cfg rows tr ws v' :=
        fun v' a b => ih v' (by omega) ws a (by omega)
      have hIw0 : ∀ v', cfg.seed cfg.levels < v' → v' ≤ o - 1 → Inst cfg rows tr w0 v' :=
        fun v' a b => h0 v' a (by omega)
      have hrec := top_recs_loc F hT hN ws w0 (o - 1) (fun v' a b => ⟨hIws v' a b, hIw0 v' a b⟩)
      have hA : (finishInputsAt cfg (hierarchyShapes cfg rows) tr ws o).aAll.toFinset =
          (finishInputsAt cfg (hierarchyShapes cfg rows) tr w0 o).aAll.toFinset := by
        rw [finish_aAll_set F hT hN ws h1 hIws, finish_aAll_set F hT hN w0 h1 hIw0,
          List.toFinset_filter, List.toFinset_filter, hrec]
      have hB : (finishInputsAt cfg (hierarchyShapes cfg rows) tr ws o).bAll.toFinset =
          (finishInputsAt cfg (hierarchyShapes cfg rows) tr w0 o).bAll.toFinset := by
        rw [finishInputsAt_eq, finishInputsAt_eq, fin_bAll, fin_bAll]
        unfold carryOf
        exact low_recs F hT ws w0 (cfg.levels - 1) (by omega) (by omega) _
      refine UnshSufficient.instance (inp := finishInputsAt cfg (hierarchyShapes cfg rows) tr w0 o)
        ?_ ?_ (hS o (finish_mem h1 h2))
      · intro x hx
        have : x ∈ (finishInputsAt cfg (hierarchyShapes cfg rows) tr ws o).aAll.toFinset :=
          List.mem_toFinset.2 hx
        rw [hA] at this
        exact List.mem_toFinset.1 this
      · intro x hx
        have : x ∈ (finishInputsAt cfg (hierarchyShapes cfg rows) tr ws o).bAll.toFinset :=
          List.mem_toFinset.2 hx
        rw [hB] at this
        exact List.mem_toFinset.1 this
  intro ws o hj
  obtain ⟨h1, h2⟩ := pj_top (Or.inr hj)
  exact key o ws h1 h2


/-- The carry's record set of top ordinal `v` (word-independent, `low_recs`). -/
def carryRecs (cfg : Config) (rows : List (SepGeom × Nat)) (tr : Trace) (v : Nat) : Finset Rec :=
  (carryOf cfg (hierarchyShapes cfg rows) tr (fun _ _ _ => 0) cfg.levels v).records.toFinset

/-- The logical top: the initialization's records at and below the seed, then
the reference finish's record set from the previous one and the carry. -/
def logTop (cfg : Config) (rows : List (SepGeom × Nat)) (tr : Trace) : Nat → Finset Rec
  | 0 => tr.init.toFinset
  | v + 1 =>
    if v + 1 ≤ cfg.seed cfg.levels then tr.init.toFinset
    else (winSet ((logTop cfg rows tr v).filter fun r => !flagged tr.unsh r)
      (carryRecs cfg rows tr (v + 1))).filter fun r => !r.tomb

/-- **The word-free condition**: no flagged tombstone of a potential finish's
carry has a live record of its key in the logical top before it. -/
def FlagSound (cfg : Config) (rows : List (SepGeom × Nat)) (tr : Trace) : Prop :=
  ∀ o, JobId.topFinish o ∈ cfg.potentialJobs →
    ∀ r ∈ carryRecs cfg rows tr o, flagged tr.unsh r = true →
      ∀ c ∈ logTop cfg rows tr (o - 1), flagged tr.unsh c = false → c.key = r.key → c.tomb = true

/-- At the all-zero tape the top table's record set is the logical top, given
the promise there up to `v`. -/
theorem table_logTop (F : Facts cfg rows) (hT : TracePremises cfg N tr) (hN : N ≤ 2 ^ 27) :
    ∀ v, (∀ v', cfg.seed cfg.levels < v' → v' ≤ v → Inst cfg rows tr (fun _ _ _ => 0) v') →
      (table cfg (hierarchyShapes cfg rows) tr (fun _ _ _ => 0) cfg.levels v).records.toFinset =
        logTop cfg rows tr v := by
  have hI : ∀ v, v ≤ cfg.seed cfg.levels →
      (table cfg (hierarchyShapes cfg rows) tr (fun _ _ _ => 0) cfg.levels v).records.toFinset =
        tr.init.toFinset := by
    intro v hv
    rw [top_base_eq F _ hv]
    exact List.toFinset_eq_of_perm _ _
      (init_out (N := N) tr.init _ (init_len hT hN) hT.initNodup hT.initKeys).2
  intro v
  induction v with
  | zero => intro _; rw [hI 0 (Nat.zero_le _)]; rfl
  | succ v ih =>
    intro hB
    by_cases hv : cfg.seed cfg.levels < v + 1
    · have h := top_step_loc F hT (fun _ _ _ => 0) hv (hB (v + 1) hv le_rfl)
        (top_inv_loc' F hT hN _ (by omega) (fun v' a b => hB v' a (by omega)))
      rw [List.toFinset_eq_of_perm _ _ h.2.2.1]
      unfold TopInputs.live
      rw [List.toFinset_filter, tWinners_eq, win_toFinset,
        List.toFinset_eq_of_perm _ _ h.2.2.2, prepInputsAt_eq, survivors_eq, finishInputsAt_eq,
        fin_bAll]
      simp only [Nat.add_sub_cancel]
      rw [List.toFinset_filter, ih (fun v' a b => hB v' a (by omega))]
      simp only [logTop, if_neg (show ¬ (v + 1 ≤ cfg.seed cfg.levels) by omega)]
      rfl
    · rw [hI (v + 1) (by omega)]
      simp only [logTop, if_pos (show v + 1 ≤ cfg.seed cfg.levels by omega)]

/-- **Word-free sufficient condition**: `FlagSound → UnshPromise`. -/
theorem unshPromise_of_flagSound (F : Facts cfg rows) (hT : TracePremises cfg N tr)
    (hN : N ≤ 2 ^ 27) (hF : FlagSound cfg rows tr) :
    UnshPromise cfg (hierarchyShapes cfg rows) tr := by
  have hL2 := F.levels2
  let w0 : Words := fun _ _ _ => 0
  -- the sufficient form at w0, by strong induction
  have key : ∀ o, cfg.seed cfg.levels < o → o ≤ cfg.seed cfg.levels + cfg.ordinals cfg.levels →
      UnshSufficient tr.unsh (finishInputsAt cfg (hierarchyShapes cfg rows) tr w0 o) := by
    intro o
    induction o using Nat.strong_induction_on with
    | _ o ih =>
      intro h1 h2
      have hIw0 : ∀ v', cfg.seed cfg.levels < v' → v' ≤ o - 1 → Inst cfg rows tr w0 v' :=
        fun v' a b => UnshSufficient.instance (fun x hx => hx) (fun x hx => hx)
          (ih v' (by omega) a (by omega))
      have hA := finish_aAll_set F hT hN w0 h1 hIw0
      rw [List.toFinset_filter, table_logTop F hT hN (o - 1) hIw0] at hA
      intro r hr hd c hc hk
      have hr' : r ∈ carryRecs cfg rows tr o := by
        rw [finishInputsAt_eq, fin_bAll] at hr
        exact List.mem_toFinset.2 hr
      have hc' : c ∈ (finishInputsAt cfg (hierarchyShapes cfg rows) tr w0 o).aAll.toFinset :=
        List.mem_toFinset.2 hc
      rw [hA, Finset.mem_filter] at hc'
      have hd' : flagged tr.unsh r = true := hd
      exact hF o (finish_mem h1 h2) r hr' hd' c hc'.1 (by simpa using hc'.2) hk
  exact unshPromise_of_sufficient F hT hN w0 fun o hj => by
    obtain ⟨a, b⟩ := pj_top (Or.inr hj); exact key o a b

end

/-- `FlagSound` implies the promise at both selected configurations. -/
theorem unshPromise_selected {N : Nat} {tr : Trace} (hN : N ≤ 2 ^ 27) :
    (TracePremises uniformConfig N tr → FlagSound uniformConfig uniformSeparated tr →
      UnshPromise uniformConfig (hierarchyShapes uniformConfig uniformSeparated) tr) ∧
    (TracePremises halfFanoutConfig N tr → FlagSound halfFanoutConfig halfFanoutSeparated tr →
      UnshPromise halfFanoutConfig (hierarchyShapes halfFanoutConfig halfFanoutSeparated) tr) :=
  ⟨fun hT hF => unshPromise_of_flagSound uniformFacts hT hN hF,
    fun hT hF => unshPromise_of_flagSound halfFanoutFacts hT hN hF⟩

end RebuildBound.UnshReductionProof
