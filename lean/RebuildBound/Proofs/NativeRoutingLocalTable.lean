import RebuildBound.Spec.NativeRouting.LocalTable
import RebuildBound.Proofs.NativeRoutingActual
import RebuildBound.Proofs.HierarchyInvariant.Provenance
import RebuildBound.Proofs.AdaptiveTracePrefix
import RebuildBound.Proofs.HierarchyHorizonFree

/-! Sparse table reconstruction reads only completed dependency inputs. The
proof covers every routing tape and every reference continuation, without a
capacity-success hypothesis. No probability or finite key universe is needed. -/
namespace RebuildBound.NativeRoutingLocalTableProof
open Model Model.Hierarchy Model.DirectJob Spec NativeRoutingActual NativeRoutingLocalTable
open NativeRoutingReadTreeProof NativeRoutingActualProof HierarchyLocalityProof
open ReadTree

lemma evaluate_bind {Q α β : Type} (tape : Q → Word64) (tree : ReadTree Q α)
    (next : α → ReadTree Q β) :
    evaluate tape (bind tree next) = evaluate tape (next (evaluate tape tree)) := by
  induction tree with
  | done result => rfl
  | read query resume ih => exact ih (tape query)

lemma gather_reads {Q α : Type} (queries : List Q) (memo : List (Q × Word64))
    (next : List (Q × Word64) → α) (tape : Q → Word64) :
    (reads tape (gather queries memo (fun m => .done (next m)))).map Prod.fst = queries := by
  induction queries generalizing memo with
  | nil => rfl
  | cons query queries ih => simp only [gather, reads, List.map_cons, ih]

lemma current_mem (cfg : Config) (tr : Trace) (level ordinal : Nat)
    (previous carry : Output) (r : Rec)
    (hr : r ∈ previous.records ++ carry.records ++
      if level = 1 then DirectMasks.records (tr.units (ordinal - cfg.seed 1 - 1)) else []) :
    Sum.inl (familyOf cfg level ordinal, r.key) ∈ stepQueries cfg tr level ordinal previous carry := by
  exact List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩)

lemma old_mem (cfg : Config) (tr : Trace) (level ordinal : Nat)
    (previous carry : Output) (h1 : level = 1) (hL : level ≠ cfg.levels) (r : Rec)
    (hr : r ∈ previous.main.flatMap Bucket.recs) :
    Sum.inl (familyOf cfg 1 (ordinal - 1), r.key) ∈ stepQueries cfg tr level ordinal previous carry := by
  apply List.mem_append_right
  have h : level = 1 ∧ level ≠ cfg.levels := ⟨h1, hL⟩
  simp only [ite_eq_left h, recordQueries]
  exact List.mem_map.mpr ⟨r, hr, rfl⟩

lemma evaluate_base (cfg : Config) (sh : Shapes) (tr : Trace) (tape : IdealKey.Tape)
    (level : Nat) : evaluate tape (baseProgram cfg sh tr level) =
      base cfg sh tr (IdealHierarchy.words tape) level := by
  unfold baseProgram
  rw [evaluate_gather]
  simp only [List.append_nil, evaluate]
  by_cases h : level = cfg.levels ∧ cfg.initialized = true
  · simp only [ite_eq_left h]
    apply base_congr
    intro _ r hr
    exact congrArg Fin.val (memo_lookup_graph _ tape _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
  · have hb : level ≠ cfg.levels ∨ cfg.initialized = false := by
      by_cases hl : level = cfg.levels
      · exact Or.inr (Bool.eq_false_iff.mpr (fun hi => h ⟨hl, hi⟩))
      · exact Or.inl hl
    rcases hb with hl | hi
    · simp [base, hl]
    · simp [base, hi]

lemma evaluate_step (cfg : Config) (sh : Shapes) (tr : Trace) (tape : IdealKey.Tape)
    (level ordinal : Nat) (previous carry : Output) :
    evaluate tape (stepProgram cfg sh tr level ordinal previous carry) =
      step cfg sh tr (IdealHierarchy.words tape) level ordinal previous carry := by
  unfold stepProgram
  rw [evaluate_gather]
  simp only [List.append_nil, evaluate]
  let memo := ((stepQueries cfg tr level ordinal previous carry).map fun q => (q, tape q)).reverse
  have hcur : ∀ r ∈ previous.records ++ carry.records ++
      if level = 1 then DirectMasks.records (tr.units (ordinal - cfg.seed 1 - 1)) else [],
      jobWord cfg (IdealHierarchy.words (memoTape memo)) level ordinal r.key =
        jobWord cfg (IdealHierarchy.words tape) level ordinal r.key := by
    intro r hr
    exact congrArg Fin.val (memo_lookup_graph _ tape _ (current_mem cfg tr level ordinal previous carry r hr))
  have hp : ∀ r ∈ previous.records,
      jobWord cfg (IdealHierarchy.words (memoTape memo)) level ordinal r.key =
        jobWord cfg (IdealHierarchy.words tape) level ordinal r.key :=
    fun r hr => hcur r (List.mem_append_left _ (List.mem_append_left _ hr))
  apply step_congr
  · exact hp
  · intro r hr
    exact hcur r (List.mem_append_left _ (List.mem_append_right _ hr))
  · intro h1 r hr
    apply hcur r
    exact List.mem_append_right _ (by simpa only [ite_eq_left h1] using hr)
  · intro hL r hr
    subst level
    exact HierarchyInvariantProof.tpReference_P sh.prep
      (jobWord cfg (IdealHierarchy.words (memoTape memo)) cfg.levels ordinal) tr.unsh
      (prepInputs previous) hp r hr
  · intro h1 hL r hr
    exact congrArg Fin.val (memo_lookup_graph _ tape _ (old_mem cfg tr level ordinal previous carry h1 hL r hr))

lemma table_evaluate (cfg : Config) (sh : Shapes) (tr : Trace) (tape : IdealKey.Tape) :
    ∀ level ordinal, evaluate tape (tableProgram cfg sh tr level ordinal) =
      table cfg sh tr (IdealHierarchy.words tape) level ordinal := by
  intro level
  induction level using Nat.strong_induction_on with
  | _ level ihLevel =>
    intro ordinal
    induction ordinal using Nat.strong_induction_on with
    | _ ordinal ihOrdinal =>
      rw [tableProgram, table_eq]
      by_cases hb : level = 0 ∨ cfg.levels < level ∨ ordinal ≤ cfg.seed level
      · simpa only [ite_eq_left hb] using evaluate_base cfg sh tr tape level
      · simp only [ite_eq_right hb]
        rw [evaluate_bind, ihOrdinal (ordinal - 1) (by omega), evaluate_bind]
        have hc : evaluate tape (if level = 1 then .done emptyOutput else
            tableProgram cfg sh tr (level - 1) (ordinal * cfg.fanout (level - 1))) =
            if level = 1 then emptyOutput else
              table cfg sh tr (IdealHierarchy.words tape) (level - 1)
                (ordinal * cfg.fanout (level - 1)) := by
          split_ifs with h1
          · rfl
          · exact ihLevel (level - 1) (by omega) _
        rw [hc, evaluate_step]

lemma base_prefix (cfg : Config) (sh : Shapes) (tr tr' : Trace) (level : Nat)
    (hi : tr.init = tr'.init) : baseProgram cfg sh tr level = baseProgram cfg sh tr' level := by
  simp only [baseProgram, base, initOutput, hi]

lemma step_prefix (cfg : Config) (sh : Shapes) (tr tr' : Trace) (level ordinal : Nat)
    (previous carry : Output) (hu : tr.unsh = tr'.unsh)
    (hunit : level = 1 → tr.units (ordinal - cfg.seed 1 - 1) =
      tr'.units (ordinal - cfg.seed 1 - 1)) :
    stepProgram cfg sh tr level ordinal previous carry = stepProgram cfg sh tr' level ordinal previous carry := by
  by_cases h1 : level = 1
  · simp only [stepProgram, stepQueries, ite_eq_left h1, hunit h1, step, prepOutput, hu]
  · simp only [stepProgram, stepQueries, ite_eq_right h1, step, prepOutput, hu]

lemma table_prefix (cfg : Config) (sh : Shapes) (tr tr' : Trace) (cut : Nat)
    (hi : tr.init = tr'.init) (hu : tr.unsh = tr'.unsh)
    (hun : ∀ i, cfg.seed 1 + i + 1 ≤ cut → tr.units i = tr'.units i) :
    ∀ level ordinal, time cfg level ordinal ≤ cut →
      tableProgram cfg sh tr level ordinal = tableProgram cfg sh tr' level ordinal := by
  intro level
  induction level using Nat.strong_induction_on with
  | _ level ihLevel =>
    intro ordinal
    induction ordinal using Nat.strong_induction_on with
    | _ ordinal ihOrdinal =>
      intro hc
      conv_lhs => rw [tableProgram]
      conv_rhs => rw [tableProgram]
      by_cases hb : level = 0 ∨ cfg.levels < level ∨ ordinal ≤ cfg.seed level
      · simpa only [ite_eq_left hb] using base_prefix cfg sh tr tr' level hi
      · simp only [ite_eq_right hb]
        have hp := ihOrdinal (ordinal - 1) (by omega)
          ((Nat.mul_le_mul_right _ (Nat.sub_le ordinal 1)).trans hc)
        have hcarry : (if level = 1 then .done emptyOutput else
            tableProgram cfg sh tr (level - 1) (ordinal * cfg.fanout (level - 1))) =
            (if level = 1 then .done emptyOutput else
            tableProgram cfg sh tr' (level - 1) (ordinal * cfg.fanout (level - 1))) := by
          split_ifs with h1
          · rfl
          · exact ihLevel (level - 1) (by omega) _ (by
              rw [AdaptiveTracePrefixProof.time_carry cfg level ordinal (by omega) (by omega)]
              exact hc)
        rw [hp, hcarry]
        congr 1
        funext previous
        congr 1
        funext carry
        apply step_prefix cfg sh tr tr' level ordinal previous carry hu
        intro h1
        subst level
        apply hun
        rw [AdaptiveTracePrefixProof.time_one] at hc
        omega

lemma base_horizon (cfg : Config) (horizon : Nat) (sh : Shapes) (tr : Trace) (level : Nat) :
    baseProgram { cfg with horizon := horizon } sh tr level = baseProgram cfg sh tr level := by
  simp only [baseProgram, familyOf, HierarchyHorizonFreeProof.familyOfAux_horizon,
    HierarchyHorizonFreeProof.base_horizon]
  rfl

lemma step_horizon (cfg : Config) (horizon : Nat) (sh : Shapes) (tr : Trace)
    (level ordinal : Nat) (previous carry : Output) :
    stepProgram { cfg with horizon := horizon } sh tr level ordinal previous carry =
      stepProgram cfg sh tr level ordinal previous carry := by
  simp only [stepProgram, stepQueries, familyOf, HierarchyHorizonFreeProof.familyOfAux_horizon,
    HierarchyHorizonFreeProof.step_horizon]
  rfl

lemma table_horizon (cfg : Config) (horizon : Nat) (sh : Shapes) (tr : Trace) :
    ∀ level ordinal, tableProgram { cfg with horizon := horizon } sh tr level ordinal =
      tableProgram cfg sh tr level ordinal := by
  intro level
  induction level using Nat.strong_induction_on with
  | _ level ihLevel =>
    intro ordinal
    induction ordinal using Nat.strong_induction_on with
    | _ ordinal ihOrdinal =>
      conv_lhs => rw [tableProgram]
      conv_rhs => rw [tableProgram]
      change (if level = 0 ∨ cfg.levels < level ∨ ordinal ≤ cfg.seed level then _ else _) = _
      by_cases hb : level = 0 ∨ cfg.levels < level ∨ ordinal ≤ cfg.seed level
      · simpa only [ite_eq_left hb] using base_horizon cfg horizon sh tr level
      · simp only [ite_eq_right hb]
        rw [ihOrdinal (ordinal - 1) (by omega)]
        have hc : (if level = 1 then .done emptyOutput else
            tableProgram { cfg with horizon := horizon } sh tr (level - 1)
              (ordinal * cfg.fanout (level - 1))) =
            (if level = 1 then .done emptyOutput else
            tableProgram cfg sh tr (level - 1) (ordinal * cfg.fanout (level - 1))) := by
          split_ifs with h1
          · rfl
          · exact ihLevel (level - 1) (by omega) _
        change bind _ (fun previous => bind
          (if level = 1 then .done emptyOutput else tableProgram { cfg with horizon := horizon }
            sh tr (level - 1) (ordinal * cfg.fanout (level - 1))) _) = _
        rw [hc]
        congr 1
        funext previous
        congr 1
        funext carry
        exact step_horizon cfg horizon sh tr level ordinal previous carry

end RebuildBound.NativeRoutingLocalTableProof

namespace RebuildBound
open Spec NativeRoutingLocalTableProof

theorem NativeRoutingLocalTableEvaluate : Spec.NativeRoutingLocalTableEvaluate_statement := table_evaluate

theorem NativeRoutingLocalTableStepReads : Spec.NativeRoutingLocalTableStepReads_statement := by
  intro cfg sh tr tape level ordinal previous carry
  exact gather_reads _ [] _ tape

theorem NativeRoutingLocalTablePrefix : Spec.NativeRoutingLocalTablePrefix_statement := table_prefix

theorem NativeRoutingLocalTableHorizon : Spec.NativeRoutingLocalTableHorizon_statement := table_horizon

end RebuildBound
