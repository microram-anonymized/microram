import RebuildBound.Proofs.HierarchyCovering.LevelOne
import RebuildBound.Proofs.DirectJobPublication

/-! # HierarchyCovering: the producers of a job's input tiers

Each tier a job above level one reads is the table of a potential job within
the horizon with a smaller `key`; when that producer does not fail, its
publication is the table (the reference output) and its tier fits its
capacity (the tier-fit statements, `DirectJobPublication` at level one),
which is within the consumer's capacity (`FactsFor`). Initialization and
preparation use their separate drain capacities. -/

namespace RebuildBound.HierarchyCoveringProof
open Model Model.DirectJob Model.Hierarchy Spec

/-- Every potential job within the horizon before `j` does not fail. -/
def Below (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (j : JobId) : Prop :=
  ∀ j' ∈ cfg.potentialJobs, WithinHorizon cfg j' → key cfg j' < key cfg j →
    jobFails cfg sh tr words j' = false

theorem digit_le {b v : Nat} (hb : 0 < b) : Config.digitOf b v ≤ b := by
  unfold Config.digitOf; have := Nat.mod_lt (v - 1) hb; omega

theorem digit_pos (b v : Nat) : 1 ≤ Config.digitOf b v := by
  unfold Config.digitOf; omega

section
variable {cfg : Config} {rows : List (SepGeom × Nat)}
  {top : TopGeom} {prep init : TPGeom} {direct : Nat → Geometry}
  (F : FactsFor cfg rows top prep init direct)
  (tr : Trace) (words : Words)
include F

/-- A job of a level below the top whose time is within the horizon is
potential. -/
theorem ord_potential {ℓ v : Nat} (h1 : 1 ≤ ℓ) (h2 : ℓ < cfg.levels) (h3 : cfg.seed ℓ < v)
    (h4 : time cfg ℓ v ≤ cfg.seed 1 + cfg.ordinals 1) : JobId.ordinary ℓ v ∈ cfg.potentialJobs := by
  refine mem_ordinary.2 ⟨h1, h2, h3, le_trans ?_ (F.horizon ℓ h2 h1)⟩
  exact (Nat.le_div_iff_mul_le (F.per_pos ℓ (by omega))).2 h4

omit F in
/-- A separated producer that does not fail: its table's tier fits its row. -/
theorem sep_table (hS : SepTierFit_statement) {ℓ v : Nat} (h2 : 2 ≤ ℓ) (hL : ℓ < cfg.levels)
    (hv : cfg.seed ℓ < v) (hd : Config.digitOf (cfg.fanout ℓ) v ≠ 1)
    (hf : jobFails cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (.ordinary ℓ v) = false) :
    (Bucket.recs (table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words ℓ v).tier).length ≤
      ((hierarchyShapesWith cfg rows top prep init direct).sep ℓ (Config.digitOf (cfg.fanout ℓ) v)).tierPages *
        ((hierarchyShapesWith cfg rows top prep init direct).sep ℓ (Config.digitOf (cfg.fanout ℓ) v)).C := by
  have hℓ1 : ℓ ≠ 1 := by omega
  simp only [jobFails, hℓ1, hd, ite_false, Bool.not_eq_false'] at hf
  obtain ⟨out, ho⟩ := toBool_ok hf
  have ht : table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words ℓ v = out := by
    rw [table_step (by omega)]
    unfold step
    have hℓL : ℓ ≠ cfg.levels := by omega
    simp only [hℓL, hℓ1, hd, ite_false]
    exact (sJob_ok ho).symm
  rw [ht]
  exact hS _ _ _ _ ho

/-- A level-one producer that publishes: its table's tier has the output's
capacity. -/
theorem one_table {v : Nat} (hv : cfg.seed 1 < v)
    (hf : jobFails cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (.ordinary 1 v) = false) :
    (Bucket.recs (table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words 1 v).tier).length ≤
      (direct (Config.digitOf (cfg.fanout 1) v)).outputCapacity := by
  rcases h : levelOneResult cfg (hierarchyShapesWith cfg rows top prep init direct) tr words v with r | e | out
  · simp [jobFails, h] at hf
  · simp [jobFails, h] at hf
  · rw [table_one F tr words hv h]
    have hc := (RebuildBound.DirectJobPublication _ _ _ _ _ h).2.2.2.2.2.2.1
    exact le_trans (List.length_filterMap_le _ _) (le_of_eq hc)

omit F in
/-- A top finish that does not fail: its table's tier fits `S_tier`. -/
theorem top_table (hT : TopTierFit_statement) (hL1 : cfg.levels ≠ 1) {v : Nat}
    (hv : cfg.seed cfg.levels < v)
    (hf : jobFails cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (.topFinish v) = false) :
    (Bucket.recs (table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words cfg.levels v).tier).length ≤
      top.STier := by
  simp only [jobFails, Bool.not_eq_false'] at hf
  obtain ⟨out, ho⟩ := toBool_ok hf
  have ht : table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words cfg.levels v = out := by
    have hL0 : cfg.levels ≠ 0 := by simp [Config.levels]
    rw [table_step (by omega)]
    unfold step
    simp only [ite_true, hL1, ite_false]
    exact (topJob_ok ho).symm
  rw [ht]
  exact hT _ _ _ _ _ ho

omit F in
/-- The initialization that does not fail: the top's base table's tier fits
the drain. -/
theorem init_table (hP : TPTierFit_statement) (hI : cfg.initialized = true) {v : Nat}
    (hv : v ≤ cfg.seed cfg.levels)
    (hf : jobFails cfg (hierarchyShapesWith cfg rows top prep init direct) tr words .initialization = false) :
    (Bucket.recs (table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words cfg.levels v).tier).length ≤
      init.drainPages * init.C := by
  simp only [jobFails, Bool.not_eq_false'] at hf
  obtain ⟨out, ho⟩ := toBool_ok hf
  rw [table_base (Or.inr (Or.inr hv))]
  unfold base
  simp only [ite_true, hI]
  unfold initResult initJob at ho
  have := tpJob_ok ho
  unfold initOutput
  rw [← this]
  exact hP _ _ _ _ _ ho

omit F in
/-- A top preparation that does not fail: its output's tier fits the drain. -/
theorem prep_out (hP : TPTierFit_statement) {v : Nat}
    (hf : jobFails cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (.topPrepare v) = false) :
    (Bucket.recs (prepOutput cfg (hierarchyShapesWith cfg rows top prep init direct) tr words v
      (table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words cfg.levels (v - 1))).tier).length ≤
      prep.drainPages * prep.C := by
  simp only [jobFails, Bool.not_eq_false'] at hf
  obtain ⟨out, ho⟩ := toBool_ok hf
  have h := hP _ _ _ _ _ ho
  rw [tpJob_ok ho] at h
  exact h

/-- The separated job's A tier fits when its producers do not fail. -/
theorem sep_fit (hS : SepTierFit_statement) {ℓ v : Nat}
    (hj : JobId.ordinary ℓ v ∈ cfg.potentialJobs) (hW : WithinHorizon cfg (.ordinary ℓ v))
    (h2 : 2 ≤ ℓ) (hd : cfg.digitAt ℓ v ≠ 1)
    (hB : Below cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (.ordinary ℓ v)) :
    STiersFit ((hierarchyShapesWith cfg rows top prep init direct).sep ℓ (cfg.digitAt ℓ v))
      (sepInputsAt cfg (hierarchyShapesWith cfg rows top prep init direct) tr words ℓ v) := by
  obtain ⟨h1, hL, h3, h4⟩ := mem_ordinary.1 hj
  simp only [Config.digitAt] at hd ⊢
  have hb := F.fanout_ge ℓ hL (by omega)
  have hd2 : 2 ≤ Config.digitOf (cfg.fanout ℓ) v := by have := digit_pos (cfg.fanout ℓ) v; omega
  have hdle : Config.digitOf (cfg.fanout ℓ) v ≤ cfg.fanout ℓ := digit_le (by omega)
  have hℓL : ℓ ≠ cfg.levels := by omega
  have hℓ1 : ℓ ≠ 1 := by omega
  unfold STiersFit sepInputsAt sepInputs
  show (Bucket.recs (table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words ℓ (v - 1)).tier).length ≤ _
  by_cases hv : v - 1 ≤ cfg.seed ℓ
  · rw [table_base (Or.inr (Or.inr hv))]
    unfold base
    simp [hℓL, emptyOutput, Bucket.recs]
  have hdp : Config.digitOf (cfg.fanout ℓ) (v - 1) = Config.digitOf (cfg.fanout ℓ) v - 1 := digit_pred (by omega) hd2
  have hW' : time cfg ℓ v ≤ cfg.seed 1 + cfg.ordinals 1 := hW
  have hPpos := F.per_pos ℓ (by omega)
  have htime : time cfg ℓ (v - 1) < time cfg ℓ v := by
    rw [time_eq, time_eq]; exact Nat.mul_lt_mul_of_pos_right (by omega) hPpos
  by_cases hd3 : 3 ≤ Config.digitOf (cfg.fanout ℓ) v
  · have hp : JobId.ordinary ℓ (v - 1) ∈ cfg.potentialJobs := mem_ordinary.2 ⟨h1, hL, by omega, by omega⟩
    have hf := hB _ hp (show time cfg ℓ (v - 1) ≤ _ by omega) (by simp only [key]; omega)
    have := sep_table tr words hS h2 hL (by omega) (by rw [hdp]; omega) hf
    rw [hdp] at this
    exact le_trans this (F.rowA ℓ hL h2 _ (by omega) hd3)
  · have hdeq : Config.digitOf (cfg.fanout ℓ) v = 2 := by omega
    have hd1 : Config.digitOf (cfg.fanout ℓ) (v - 1) = 1 := by rw [hdp]; omega
    have ht : table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words ℓ (v - 1) =
        table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (ℓ - 1) ((v - 1) * cfg.fanout (ℓ - 1)) := by
      rw [table_step (by omega)]
      unfold step
      simp only [hℓL, hℓ1, hd1, ite_false, ite_true]
    rw [ht, hdeq]
    have hb' := F.fanout_ge (ℓ - 1) (by omega) (by omega)
    have hseed := F.seed_succ (ℓ - 1) (by omega) (by omega)
    have hper := F.per_succ (ℓ - 1) (by omega) (by omega)
    rw [show ℓ - 1 + 1 = ℓ by omega] at hseed hper
    have hlt : cfg.seed (ℓ - 1) < (v - 1) * cfg.fanout (ℓ - 1) := by
      rw [hseed]; exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    have hdig : Config.digitOf (cfg.fanout (ℓ - 1)) ((v - 1) * cfg.fanout (ℓ - 1)) =
        cfg.fanout (ℓ - 1) := digit_mul (by omega) (by omega)
    have htime' : time cfg (ℓ - 1) ((v - 1) * cfg.fanout (ℓ - 1)) = time cfg ℓ (v - 1) := by
      rw [time_eq, time_eq, hper, Nat.mul_assoc, Nat.mul_comm (cfg.fanout (ℓ - 1))]
    have hp := ord_potential F (ℓ := ℓ - 1) (by omega) (by omega) hlt (by omega)
    have hf := hB _ hp (show time cfg (ℓ - 1) _ ≤ _ by omega) (by simp only [key]; omega)
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      have := one_table F tr words hlt hf
      rw [hdig] at this
      exact le_trans this (F.rowOne hL)
    · have := sep_table tr words hS (ℓ := ℓ - 1) (by omega) (by omega) hlt (by rw [hdig]; omega) hf
      rw [hdig] at this
      exact le_trans this (F.rowCarry ℓ hL (by omega))

/-- The top preparation's A tier fits when its producer does not fail. -/
theorem prep_fit (hT : TopTierFit_statement) (hP : TPTierFit_statement) {v : Nat}
    (hj : JobId.topPrepare v ∈ cfg.potentialJobs) (hW : WithinHorizon cfg (.topPrepare v))
    (hB : Below cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (.topPrepare v)) :
    TPTiersFit (hierarchyShapesWith cfg rows top prep init direct).prep (prepInputsAt cfg (hierarchyShapesWith cfg rows top prep init direct) tr words v) := by
  obtain ⟨h1, h2⟩ := mem_prep.1 hj
  have hL := F.levels_ge
  unfold TPTiersFit prepInputsAt prepInputs
  show (Bucket.recs (table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words cfg.levels (v - 1)).tier).length ≤
    prep.aTierPages * prep.C
  by_cases hv : v - 1 ≤ cfg.seed cfg.levels
  · cases hI : cfg.initialized with
    | false =>
      rw [table_base (Or.inr (Or.inr hv))]
      simp [base, hI, Bucket.recs]
    | true =>
      have hf := hB _ (mem_init hI) (show 0 ≤ _ from Nat.zero_le _) (by simp only [key]; omega)
      exact le_trans (init_table tr words hP hI hv hf) F.initPrep
  · have hp : JobId.topFinish (v - 1) ∈ cfg.potentialJobs := mem_finish.2 ⟨by omega, by omega⟩
    have hf := hB _ hp hW (by simp only [key]; omega)
    exact le_trans (top_table tr words hT (by omega) (by omega) hf) F.topPrep

/-- The top finish's R and B tiers fit when their producers do not fail. -/
theorem finish_fit (hS : SepTierFit_statement) (hP : TPTierFit_statement) {v : Nat}
    (hj : JobId.topFinish v ∈ cfg.potentialJobs) (hW : WithinHorizon cfg (.topFinish v))
    (hB : Below cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (.topFinish v)) :
    TopTiersFit (hierarchyShapesWith cfg rows top prep init direct).top (finishInputsAt cfg (hierarchyShapesWith cfg rows top prep init direct) tr words v) := by
  obtain ⟨h1, h2⟩ := mem_finish.1 hj
  have hL := F.levels_ge
  have hW' : time cfg cfg.levels v ≤ cfg.seed 1 + cfg.ordinals 1 := hW
  have hPpos := F.per_pos cfg.levels (by omega)
  have htime : time cfg cfg.levels (v - 1) < time cfg cfg.levels v := by
    rw [time_eq, time_eq]; exact Nat.mul_lt_mul_of_pos_right (by omega) hPpos
  unfold TopTiersFit finishInputsAt finishInputs
  dsimp only [hierarchyShapesWith]
  constructor
  · 
    have hp : JobId.topPrepare v ∈ cfg.potentialJobs := mem_prep.2 ⟨h1, h2⟩
    have hf := hB _ hp (show time cfg cfg.levels (v - 1) ≤ _ by omega) (by simp only [key]; omega)
    exact le_trans (prep_out tr words hP hf) F.prepTop
  · unfold carryOf
    have hb := F.fanout_ge (cfg.levels - 1) (by omega) (by omega)
    have hseed := F.seed_succ (cfg.levels - 1) (by omega) (by omega)
    have hper := F.per_succ (cfg.levels - 1) (by omega) (by omega)
    rw [show cfg.levels - 1 + 1 = cfg.levels by omega] at hseed hper
    have hlt : cfg.seed (cfg.levels - 1) < v * cfg.fanout (cfg.levels - 1) := by
      rw [hseed]; exact Nat.mul_lt_mul_of_pos_right h1 (by omega)
    have hdig : Config.digitOf (cfg.fanout (cfg.levels - 1)) (v * cfg.fanout (cfg.levels - 1)) =
        cfg.fanout (cfg.levels - 1) := digit_mul (by omega) (by omega)
    have htime' : time cfg (cfg.levels - 1) (v * cfg.fanout (cfg.levels - 1)) = time cfg cfg.levels v := by
      rw [time_eq, time_eq, hper, Nat.mul_assoc, Nat.mul_comm (cfg.fanout (cfg.levels - 1))]
    have hp := ord_potential F (ℓ := cfg.levels - 1) (by omega) (by omega) hlt (by omega)
    have hf := hB _ hp (show time cfg (cfg.levels - 1) _ ≤ _ by omega) (by simp only [key]; omega)
    by_cases hL2 : cfg.levels = 2
    · have hpred : cfg.levels - 1 = 1 := by omega
      rw [hpred] at hlt hdig hf ⊢
      have ht := one_table F tr words hlt hf
      rw [hdig] at ht
      exact le_trans ht (by simpa only [hL2, ite_true] using F.topB)
    · have ht := sep_table tr words hS (ℓ := cfg.levels - 1) (by omega) (by omega) hlt (by rw [hdig]; omega) hf
      rw [hdig] at ht
      exact le_trans ht (by simpa only [hL2, ite_false] using F.topB)

end

end RebuildBound.HierarchyCoveringProof
