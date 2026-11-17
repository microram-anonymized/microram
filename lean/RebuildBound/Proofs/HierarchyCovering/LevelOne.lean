import RebuildBound.Proofs.HierarchyCovering.Basic

/-! # HierarchyCovering: a level-one job that does not publish stops its cycle

Along cycle `c`, `runChain`'s state before position `i` is the table after the
previous ordinal (`emptyOutput` at the first position, of digit one since
`b_1 ∣ s_1`), and its job at position `i` is the model's level-one job of
ordinal `cycleOrdinal c i`; so a level-one job of the cycle that does not
publish stops the chain. -/

namespace RebuildBound.HierarchyCoveringProof
open Model Model.DirectJob Model.Hierarchy Spec

section
variable {cfg : Config} {rows : List (SepGeom × Nat)}
  {top : TopGeom} {prep init : TPGeom} {direct : Nat → Geometry}
  (F : FactsFor cfg rows top prep init direct)
  (tr : Trace) (words : Words)
include F

/-- The table of a level-one ordinal whose job publishes is its output. -/
theorem table_one {v : Nat} {out : Output} (hv : cfg.seed 1 < v)
    (h : levelOneResult cfg (hierarchyShapesWith cfg rows top prep init direct) tr words v = .published out) :
    table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words 1 v = out := by
  have hL := F.levels_ge
  rw [table_step (by omega)]
  unfold step levelOneStep
  have h1 : (1 : Nat) ≠ cfg.levels := by omega
  simp only [h1, ite_false, ite_true]
  unfold levelOneResult levelOneInputs at h
  rw [h]

end

section
variable {cfg : Config} {rows : List (SepGeom × Nat)}
  {top : TopGeom} {prep init : TPGeom} (F : FactsFor cfg rows top prep init)
  (tr : Trace) (words : Words)
include F

/-- Position `i < b_1` of cycle `c` runs the model's level-one job. -/
theorem chain_job (c i : Nat) (hi : i < cfg.fanout 1) :
    runJob (selectedDirectGeometry (1 + i)) (jobWord cfg words 1 (cfg.cycleOrdinal c i - 1))
        (jobWord cfg words 1 (cfg.cycleOrdinal c i))
        (adopt (if i = 0 then emptyOutput
          else table cfg (hierarchyShapesWith cfg rows top prep init) tr words 1 (cfg.cycleOrdinal c i - 1))
          (tr.units (c * cfg.fanout 1 + i))) =
      levelOneResult cfg (hierarchyShapesWith cfg rows top prep init) tr words (cfg.cycleOrdinal c i) := by
  unfold levelOneResult levelOneInputs
  have hd : Config.digitOf (cfg.fanout 1) (cfg.cycleOrdinal c i) = i + 1 :=
    digit_cycle F.seed_dvd hi
  have hu : cfg.cycleOrdinal c i - cfg.seed 1 - 1 = c * cfg.fanout 1 + i := by
    unfold Config.cycleOrdinal; omega
  rw [hd, hu, Nat.add_comm 1 i]
  simp only [Nat.add_eq_right]
  rfl

theorem chain_stuck (c n k : Nat) (hn : n ≤ cfg.fanout 1) (hk : k < n)
    (hf : ∀ out, levelOneResult cfg (hierarchyShapesWith cfg rows top prep init) tr words (cfg.cycleOrdinal c k) ≠
      .published out) :
    ∀ m i, i + m = n → i ≤ k → ∀ out,
      runChain (jobWord cfg words 1 (cfg.cycleOrdinal c i - 1))
        (if i = 0 then emptyOutput
          else table cfg (hierarchyShapesWith cfg rows top prep init) tr words 1 (cfg.cycleOrdinal c i - 1))
        (selectedChainJobs (1 + i) ((List.range' i m).map fun j =>
          (jobWord cfg words 1 (cfg.cycleOrdinal c j), tr.units (c * cfg.fanout 1 + j)))) ≠
        .published out := by
  intro m
  induction m with
  | zero => intro i hi hik; omega
  | succ m ih =>
    intro i hi hik out
    rw [List.range'_succ, List.map_cons]
    simp only [selectedChainJobs, runChain]
    rw [chain_job F tr words c i (by omega)]
    rcases hres : levelOneResult cfg (hierarchyShapesWith cfg rows top prep init) tr words (cfg.cycleOrdinal c i)
      with reason | event | out'
    · simp
    · simp
    · simp only
      have hik' : i ≠ k := by
        rintro rfl; exact hf out' hres
      have ht : table cfg (hierarchyShapesWith cfg rows top prep init) tr words 1 (cfg.cycleOrdinal c i) = out' :=
        table_one F tr words (by unfold Config.cycleOrdinal; omega) hres
      have ho : cfg.cycleOrdinal c (i + 1) - 1 = cfg.cycleOrdinal c i := by
        unfold Config.cycleOrdinal; omega
      have := ih (i + 1) (by omega) (by omega) out
      rw [ho, if_neg (show i + 1 ≠ 0 by omega), ht] at this
      rw [show 1 + i + 1 = 1 + (i + 1) by omega]
      exact this

/-- A level-one potential job that does not publish stops its cycle. -/
theorem levelOne_stuck {o : Nat} (ho : JobId.ordinary 1 o ∈ cfg.potentialJobs)
    (hf : jobFails cfg (hierarchyShapesWith cfg rows top prep init) tr words (.ordinary 1 o) = true) :
    ∃ c < cfg.levelOneCycles, CycleStuck cfg tr words c := by
  have hb := F.fanout_ge 1 (by have := F.levels_ge; omega) le_rfl
  obtain ⟨-, -, h3, h4⟩ := mem_ordinary.1 ho
  set b := cfg.fanout 1 with hbdef
  set n := o - cfg.seed 1 - 1 with hn
  have hbpos : 0 < b := by omega
  have hdiv := Nat.mod_add_div n b
  have hmod := Nat.mod_lt n hbpos
  set c := n / b
  set k := n % b
  have hcb : c * b + k < cfg.ordinals 1 := by rw [Nat.mul_comm]; omega
  have hoc : o = cfg.cycleOrdinal c k := by
    unfold Config.cycleOrdinal; rw [← hbdef, Nat.mul_comm]; omega
  refine ⟨c, ?_, ?_⟩
  · unfold Config.levelOneCycles
    rw [← hbdef]
    apply (Nat.le_div_iff_mul_le hbpos).2
    rw [Nat.succ_mul]
    omega
  · rintro ⟨out, hout⟩
    have hlen : cfg.cycleLength c ≤ b := by unfold Config.cycleLength; omega
    have hklen : k < cfg.cycleLength c := by
      unfold Config.cycleLength; rw [← hbdef]; omega
    have hnp : ∀ out, levelOneResult cfg (hierarchyShapesWith cfg rows top prep init) tr words (cfg.cycleOrdinal c k) ≠
        .published out := by
      intro out' h
      rw [← hoc] at h
      simp [jobFails, h] at hf
    have hsteps : cycleStepsOn (cycleUnits cfg tr c).units (cycleNative cfg c) words =
        (List.range' 0 (cfg.cycleLength c)).map fun j =>
          (jobWord cfg words 1 (cfg.cycleOrdinal c j), tr.units (c * cfg.fanout 1 + j)) := by
      apply List.ext_getElem
      · simp [cycleStepsOn, cycleUnits]
      · intro i h1 h2
        simp [cycleStepsOn, cycleUnits, cycleNative]
    have := chain_stuck F tr words c (cfg.cycleLength c) k hlen hklen hnp (cfg.cycleLength c) 0
      (by omega) (by omega) out

    rw [hsteps] at hout
    simp only [ite_true] at this
    exact this hout

end

end RebuildBound.HierarchyCoveringProof
