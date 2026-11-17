import RebuildBound.Spec.NativeMatch.Hierarchy
import RebuildBound.Proofs.ConfigurationFamilyProbability.Facts
import RebuildBound.Proofs.HierarchyCoveringFrom
import RebuildBound.Proofs.NativeMatchJobs
import RebuildBound.Proofs.DirectMaskIndex
import RebuildBound.Proofs.DirectJobPublication
import RebuildBound.Proofs.TierFit
import RebuildBound.Proofs.HierarchyCovering
import RebuildBound.Proofs.ApiStructural
import RebuildBound.Proofs.HierarchyStructural
import RebuildBound.Proofs.HierarchyInvariant.ContractsFor
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace RebuildBound.NativeMatchTierLength
open Model Model.DirectJob Spec Spec.NativeMatchJobTrace
open NativeMatchFinalDrainProof NativeMatchFillCompose

theorem sDrain_length (st : SFin) (capacity : Nat)
    (hfirst : (firstDrain st).length ≤ capacity)
    (hlast : occupied (sDrain st).1 ≤ capacity) : (sDrain st).1.length ≤ capacity := by
  dsimp only [sDrain,sDrainStep] at hlast ⊢
  simp only [List.length_map]
  apply appendFill_length_le
  · simpa only [firstDrain,List.length_map] using hfirst
  · simpa only [TierFitProof.occupied_map_map] using hlast

theorem sep_published (g : SepGeom) (word : LogicalKey → Nat) (inp : SInputs)
    (out : Output) (hok : sJob engineRule g word inp = .ok out) :
    out.tier.length ≤ g.tierPages*g.C := by
  unfold sJob sJobWith at hok
  dsimp only at hok
  split at hok
  · cases hok
  · rename_i hno
    injection hok with he
    subst out
    let run := sReferenceWith engineRule g word inp (engineOps g)
    have hfirst : (firstDrain run.fin).length ≤ g.tierPages*g.C := by
      rcases firstDrain_witness run.fin with he | he
      · change firstDrain run.fin = [] at he
        rw [he]; simp
      · have hm : (STest.drain,occupied (firstDrain run.fin)) ∈ (sDrain run.fin).2 :=
          List.mem_append_left _ he
        have h := NativeMatchSeparatedReadyProof.noFailure_entry g _ hno _
          (List.mem_append_right _ hm)
        rw [firstDrain_full] at h
        exact h
    have hlast := NativeMatchSeparatedReadyProof.noFailure_entry g _ hno _
      (List.mem_append_right _ (drain_last run.fin))
    exact sDrain_length run.fin _ hfirst hlast

end RebuildBound.NativeMatchTierLength


namespace RebuildBound.NativeMatchTierLength
open Model Model.DirectJob Spec Spec.NativeMatchJobTrace Spec.NativeMatchTopJobTrace
open NativeMatchFinalDrainProof NativeMatchTopDrainProof

theorem top_published (g : TopGeom) (unsh : Rec → Bool) (word : LogicalKey → Nat)
    (inp : TopInputs) (out : Output) (hok : topJob g unsh word inp = .ok out) :
    out.tier.length ≤ g.STier := by
  unfold topJob at hok
  dsimp only at hok
  split at hok
  · cases hok
  · rename_i hno
    injection hok with he
    subst out
    let run := topReference g unsh word inp
    have hc (n : Nat) (hn : (STest.drain,n) ∈ (sDrain (toSFin run.fin)).2) : n ≤ g.STier := by
      have he := drain_entry run.fin n hn
      have h := NativeMatchTopReadyProof.noFailure_entry g.toGeom g.caps _ hno _
        (List.mem_append_right _ he)
      simpa only [TopGeom.caps,Caps.capOf,exceeds,decide_eq_false_iff_not,not_lt] using h
    have hfirst : (firstDrain (toSFin run.fin)).length ≤ g.STier := by
      rcases firstDrain_witness (toSFin run.fin) with he | he
      · change firstDrain (toSFin run.fin) = [] at he
        rw [he]; simp
      · have h := hc _ (List.mem_append_left _ he)
        change occupied (firstDrain (toSFin run.fin)) ≤ g.STier at h
        rwa [firstDrain_full] at h
    have hlast := hc _ (drain_last (toSFin run.fin))
    have h := sDrain_length (toSFin run.fin) _ hfirst hlast
    rw [(drain_projection run.fin).1] at h
    change ((drain run.fin).1.map (fun s => s.filter (fun r => !r.tomb))).length ≤ _
    simpa only [List.length_map] using h

theorem tpDrain_full (st : TPFin) : occupied (tpDrain st).1 = (tpDrain st).1.length := by
  have hfold (chunks : List (List Rec)) (records : List Rec) (trace : List (TPTest × Nat)) :
      (chunks.foldl tpDrainStep (records.map some,trace)).1 = (records ++ chunks.flatten).map some := by
    induction chunks generalizing records trace with
    | nil => simp
    | cons chunk chunks ih =>
      rw [List.foldl_cons]
      have hs : tpDrainStep (records.map some,trace) chunk =
          ((records++chunk).map some,trace++[(.drain,(records++chunk).length)]) := by
        simp only [tpDrainStep,D4b.appendFill_full _ (D4b.free_map_some records),
          D4b.occupied_append,D4b.occupied_map_some,List.length_append,List.map_append]
      rw [hs,ih]
      simp only [List.flatten_cons,List.append_assoc]
  have he := hfold (st.leaves++[st.last]) [] []
  simp only [List.nil_append,List.map_nil] at he
  unfold tpDrain
  rw [he,D4b.occupied_map_some,List.length_map]

theorem tp_published (g : TPGeom) (unsh : Rec → Bool) (word : LogicalKey → Nat)
    (inp : TPInputs) (out : Output) (hok : tpJob engineRule g unsh word inp = .ok out) :
    out.tier.length ≤ g.drainPages*g.C := by
  have h := RebuildBound.TPTierFit g unsh word inp out hok
  rw [TierFitProof.recs_length] at h
  have he := HierarchyCoveringProof.tpJob_ok hok
  rw [he] at h ⊢
  change occupied (tpDrain (tpReference engineRule g unsh word inp).fin).1 ≤ _ at h
  rw [tpDrain_full] at h
  exact h

end RebuildBound.NativeMatchTierLength


namespace RebuildBound.NativeMatchPhysicalProducers
open Model Model.DirectJob Model.Hierarchy Spec
open HierarchyCoveringProof

def SepLengthStatement : Prop := ∀ g word inp out, sJob engineRule g word inp = .ok out → out.tier.length ≤ g.tierPages*g.C
def TopLengthStatement : Prop := ∀ g unsh word inp out, topJob g unsh word inp = .ok out → out.tier.length ≤ g.STier
def PrepLengthStatement : Prop := ∀ g unsh word inp out, tpJob engineRule g unsh word inp = .ok out → out.tier.length ≤ g.drainPages*g.C


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
theorem sep_table (hS : SepLengthStatement) {ℓ v : Nat} (h2 : 2 ≤ ℓ) (hL : ℓ < cfg.levels)
    (hv : cfg.seed ℓ < v) (hd : Config.digitOf (cfg.fanout ℓ) v ≠ 1)
    (hf : jobFails cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (.ordinary ℓ v) = false) :
    ((table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words ℓ v).tier).length ≤
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
    ((table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words 1 v).tier).length ≤
      (direct (Config.digitOf (cfg.fanout 1) v)).outputCapacity := by
  rcases h : levelOneResult cfg (hierarchyShapesWith cfg rows top prep init direct) tr words v with r | e | out
  · simp [jobFails, h] at hf
  · simp [jobFails, h] at hf
  · rw [table_one F tr words hv h]
    have hc := (RebuildBound.DirectJobPublication _ _ _ _ _ h).2.2.2.2.2.2.1
    exact le_of_eq hc

omit F in
/-- A top finish that does not fail: its table's tier fits `S_tier`. -/
theorem top_table (hT : TopLengthStatement) (hL1 : cfg.levels ≠ 1) {v : Nat}
    (hv : cfg.seed cfg.levels < v)
    (hf : jobFails cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (.topFinish v) = false) :
    ((table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words cfg.levels v).tier).length ≤
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
theorem init_table (hP : PrepLengthStatement) (hI : cfg.initialized = true) {v : Nat}
    (hv : v ≤ cfg.seed cfg.levels)
    (hf : jobFails cfg (hierarchyShapesWith cfg rows top prep init direct) tr words .initialization = false) :
    ((table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words cfg.levels v).tier).length ≤
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
theorem prep_out (hP : PrepLengthStatement) {v : Nat}
    (hf : jobFails cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (.topPrepare v) = false) :
    ((prepOutput cfg (hierarchyShapesWith cfg rows top prep init direct) tr words v
      (table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words cfg.levels (v - 1))).tier).length ≤
      prep.drainPages * prep.C := by
  simp only [jobFails, Bool.not_eq_false'] at hf
  obtain ⟨out, ho⟩ := toBool_ok hf
  have h := hP _ _ _ _ _ ho
  rw [tpJob_ok ho] at h
  exact h

/-- The separated job's A tier fits when its producers do not fail. -/
theorem sep_fit (hS : SepLengthStatement) {ℓ v : Nat}
    (hj : JobId.ordinary ℓ v ∈ cfg.potentialJobs) (hW : WithinHorizon cfg (.ordinary ℓ v))
    (h2 : 2 ≤ ℓ) (hd : cfg.digitAt ℓ v ≠ 1)
    (hB : Below cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (.ordinary ℓ v)) :
    (table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words ℓ (v-1)).tier.length ≤
      ((hierarchyShapesWith cfg rows top prep init direct).sep ℓ (cfg.digitAt ℓ v)).aTierPages *
      ((hierarchyShapesWith cfg rows top prep init direct).sep ℓ (cfg.digitAt ℓ v)).C := by
  obtain ⟨h1, hL, h3, h4⟩ := mem_ordinary.1 hj
  simp only [Config.digitAt] at hd ⊢
  have hb := F.fanout_ge ℓ hL (by omega)
  have hd2 : 2 ≤ Config.digitOf (cfg.fanout ℓ) v := by have := digit_pos (cfg.fanout ℓ) v; omega
  have hdle : Config.digitOf (cfg.fanout ℓ) v ≤ cfg.fanout ℓ := digit_le (by omega)
  have hℓL : ℓ ≠ cfg.levels := by omega
  have hℓ1 : ℓ ≠ 1 := by omega
  show ((table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words ℓ (v - 1)).tier).length ≤ _
  by_cases hv : v - 1 ≤ cfg.seed ℓ
  · rw [table_base (Or.inr (Or.inr hv))]
    unfold base
    simp [hℓL, emptyOutput]
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
theorem prep_fit (hT : TopLengthStatement) (hP : PrepLengthStatement) {v : Nat}
    (hj : JobId.topPrepare v ∈ cfg.potentialJobs) (hW : WithinHorizon cfg (.topPrepare v))
    (hB : Below cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (.topPrepare v)) :
    (table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words cfg.levels (v-1)).tier.length ≤ prep.aTierPages*prep.C := by
  obtain ⟨h1, h2⟩ := mem_prep.1 hj
  have hL := F.levels_ge
  show ((table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words cfg.levels (v - 1)).tier).length ≤
    prep.aTierPages * prep.C
  by_cases hv : v - 1 ≤ cfg.seed cfg.levels
  · cases hI : cfg.initialized with
    | false =>
      rw [table_base (Or.inr (Or.inr hv))]
      simp [base, hI]
    | true =>
      have hf := hB _ (mem_init hI) (show 0 ≤ _ from Nat.zero_le _) (by simp only [key]; omega)
      exact le_trans (init_table tr words hP hI hv hf) F.initPrep
  · have hp : JobId.topFinish (v - 1) ∈ cfg.potentialJobs := mem_finish.2 ⟨by omega, by omega⟩
    have hf := hB _ hp hW (by simp only [key]; omega)
    exact le_trans (top_table tr words hT (by omega) (by omega) hf) F.topPrep

/-- The top finish's R and B tiers fit when their producers do not fail. -/
theorem finish_fit (hS : SepLengthStatement) (hP : PrepLengthStatement) {v : Nat}
    (hj : JobId.topFinish v ∈ cfg.potentialJobs) (hW : WithinHorizon cfg (.topFinish v))
    (hB : Below cfg (hierarchyShapesWith cfg rows top prep init direct) tr words (.topFinish v)) :
    (prepOutput cfg (hierarchyShapesWith cfg rows top prep init direct) tr words v
      (table cfg (hierarchyShapesWith cfg rows top prep init direct) tr words cfg.levels (v-1))).tier.length ≤ top.SR ∧
    (carryOf cfg (hierarchyShapesWith cfg rows top prep init direct) tr words cfg.levels v).tier.length ≤ top.SB := by
  obtain ⟨h1, h2⟩ := mem_finish.1 hj
  have hL := F.levels_ge
  have hW' : time cfg cfg.levels v ≤ cfg.seed 1 + cfg.ordinals 1 := hW
  have hPpos := F.per_pos cfg.levels (by omega)
  have htime : time cfg cfg.levels (v - 1) < time cfg cfg.levels v := by
    rw [time_eq, time_eq]; exact Nat.mul_lt_mul_of_pos_right (by omega) hPpos
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

end RebuildBound.NativeMatchPhysicalProducers


namespace RebuildBound.NativeMatchPhysicalInputs
open Model Model.DirectJob Model.Hierarchy Spec HierarchyCoveringProof

/-- Capacity of the actual lower-level carry producer, before its optional
lanes are split at the consumer's physical page boundaries. -/
def incomingCapacity (cfg : Config) (sh : Shapes) (level : Nat) : Nat :=
  if level = 2 then (sh.direct (cfg.fanout 1)).outputCapacity else
    (sh.sep (level-1) (cfg.fanout (level-1))).tierPages *
      (sh.sep (level-1) (cfg.fanout (level-1))).C

theorem below_no_failure (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)
    (hno : ¬Fails cfg sh tr words) (j : JobId) : Below cfg sh tr words j := by
  intro j' hj hW _
  apply Bool.eq_false_iff.mpr
  exact fun h => hno ⟨j',hj,hW,h⟩

theorem carry_length (geo : HierarchyGeometry)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (tr : Trace) (words : Words) (hno : ¬Fails geo.cfg geo.shapes tr words)
    (level ordinal : Nat) (h2 : 2 ≤ level) (hL : level ≤ geo.cfg.levels)
    (ho : geo.cfg.seed level < ordinal)
    (hW : time geo.cfg level ordinal ≤ geo.cfg.seed 1 + geo.cfg.ordinals 1) :
    (carryOf geo.cfg geo.shapes tr words level ordinal).tier.length ≤
      incomingCapacity geo.cfg geo.shapes level := by
  have hb := F.fanout_ge (level-1) (by omega) (by omega)
  have hseed := F.seed_succ (level-1) (by omega) (by omega)
  have hper := F.per_succ (level-1) (by omega) (by omega)
  rw [show level-1+1=level by omega] at hseed hper
  have hlt : geo.cfg.seed (level-1) < ordinal*geo.cfg.fanout (level-1) := by
    rw [hseed]
    exact Nat.mul_lt_mul_of_pos_right ho (by omega)
  have hdig : Config.digitOf (geo.cfg.fanout (level-1)) (ordinal*geo.cfg.fanout (level-1)) =
      geo.cfg.fanout (level-1) := digit_mul (by omega) (by omega)
  have ht : time geo.cfg (level-1) (ordinal*geo.cfg.fanout (level-1)) = time geo.cfg level ordinal := by
    rw [time_eq,time_eq,hper,Nat.mul_assoc,Nat.mul_comm (geo.cfg.fanout (level-1))]
  have hp := HierarchyCoveringProof.ord_potential F (ℓ:=level-1) (by omega) (by omega) hlt (by omega)
  have hf : jobFails geo.cfg geo.shapes tr words (.ordinary (level-1) (ordinal*geo.cfg.fanout (level-1))) = false := by
    apply Bool.eq_false_iff.mpr
    exact fun h => hno ⟨_,hp,(show time geo.cfg (level-1) _ ≤ _ by omega),h⟩
  unfold carryOf incomingCapacity
  by_cases he : level=2
  · subst level
    simp only [ite_true]
    have h := NativeMatchPhysicalProducers.one_table F tr words hlt hf
    rw [hdig] at h
    exact h
  · simp only [he,ite_false]
    have h := NativeMatchPhysicalProducers.sep_table tr words NativeMatchTierLength.sep_published
      (ℓ:=level-1) (by omega) (by omega) hlt (by rw [hdig]; omega) hf
    rw [hdig] at h
    exact h

theorem separated_a_length (geo : HierarchyGeometry)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (tr : Trace) (words : Words) (hno : ¬Fails geo.cfg geo.shapes tr words)
    (level ordinal : Nat) (hj : JobId.ordinary level ordinal ∈ geo.cfg.potentialJobs)
    (hW : WithinHorizon geo.cfg (.ordinary level ordinal))
    (h2 : 2 ≤ level) (hd : geo.cfg.digitAt level ordinal ≠ 1) :
    (table geo.cfg geo.shapes tr words level (ordinal-1)).tier.length ≤
      (geo.shapes.sep level (geo.cfg.digitAt level ordinal)).aTierPages *
      (geo.shapes.sep level (geo.cfg.digitAt level ordinal)).C :=
  NativeMatchPhysicalProducers.sep_fit F tr words NativeMatchTierLength.sep_published hj hW h2 hd
    (below_no_failure geo.cfg geo.shapes tr words hno _)

theorem finish_lengths (geo : HierarchyGeometry)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (tr : Trace) (words : Words) (hno : ¬Fails geo.cfg geo.shapes tr words)
    (ordinal : Nat) (hj : JobId.topFinish ordinal ∈ geo.cfg.potentialJobs)
    (hW : WithinHorizon geo.cfg (.topFinish ordinal)) :
    (prepOutput geo.cfg geo.shapes tr words ordinal
      (table geo.cfg geo.shapes tr words geo.cfg.levels (ordinal-1))).tier.length ≤ geo.top.SR ∧
    (carryOf geo.cfg geo.shapes tr words geo.cfg.levels ordinal).tier.length ≤ geo.top.SB :=
  NativeMatchPhysicalProducers.finish_fit F tr words NativeMatchTierLength.sep_published
    NativeMatchTierLength.tp_published hj hW (below_no_failure geo.cfg geo.shapes tr words hno _)

end RebuildBound.NativeMatchPhysicalInputs


namespace RebuildBound.NativeMatchPhysicalInputs
open Model Model.Hierarchy Spec HierarchyCoveringProof

/-- The previous level-one table is a real earlier publication. Its fixed
output slot width, followed by the public adjacent-capacity link, gives the
physical A-tier layout needed by the later direct job. -/
theorem direct_previous_length (geo : HierarchyGeometry)
    (F : FactsFor geo.cfg geo.rows geo.top geo.prep geo.init geo.direct)
    (tr : Trace) (words : Words) (ordinal : Nat)
    (hj : JobId.ordinary 1 ordinal ∈ geo.cfg.potentialJobs)
    (hW : WithinHorizon geo.cfg (.ordinary 1 ordinal)) (hd2 : 2 ≤ geo.cfg.digitAt 1 ordinal)
    (hlink : (geo.direct (geo.cfg.digitAt 1 ordinal-1)).outputCapacity ≤
      (geo.direct (geo.cfg.digitAt 1 ordinal)).aTierCapacity)
    (hno : ¬Fails geo.cfg geo.shapes tr words) :
    (table geo.cfg geo.shapes tr words 1 (ordinal-1)).tier.length ≤
      (geo.direct (geo.cfg.digitAt 1 ordinal)).aTierCapacity := by
  obtain ⟨h1,hL,ho,hov⟩ := mem_ordinary.1 hj
  have hfan := F.fanout_ge 1 hL (by omega)
  have hpred : geo.cfg.seed 1 < ordinal-1 :=
    HierarchyInvariantProof.pred_gt (Nat.dvd_of_mod_eq_zero F.seed_dvd) ho hd2
  have hdprev : Config.digitOf (geo.cfg.fanout 1) (ordinal-1) = geo.cfg.digitAt 1 ordinal-1 :=
    HierarchyInvariantProof.digit_pred (by omega) hd2
  have hp : JobId.ordinary 1 (ordinal-1) ∈ geo.cfg.potentialJobs :=
    mem_ordinary.2 ⟨h1,hL,hpred,by omega⟩
  have htime : time geo.cfg 1 (ordinal-1) ≤ time geo.cfg 1 ordinal :=
    Nat.mul_le_mul_right _ (Nat.sub_le ordinal 1)
  have hf : jobFails geo.cfg geo.shapes tr words (.ordinary 1 (ordinal-1)) = false := by
    apply Bool.eq_false_iff.mpr
    exact fun h => hno ⟨_,hp,htime.trans hW,h⟩
  have hprev := NativeMatchPhysicalProducers.one_table F tr words hpred hf
  rw [hdprev] at hprev
  exact hprev.trans hlink

end RebuildBound.NativeMatchPhysicalInputs


namespace RebuildBound.NativeMatchDirectSuccess
open Model Model.DirectJob Spec

/-- A real successful later-digit publication supplies every local phase
success used by the physical matching adapter. No intermediate phase law is
assumed. -/
theorem later (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (out : Output) (hd : 2 ≤ g.digit) (hpub : runJob g oldWord word inp = .published out) :
    g.Valid ∧ inp.Valid g oldWord ∧
    prepareA g word inp.aMain = .ok (analyticalA g word inp.aMain).state ∧
    ∃ b, buildB g word inp = .ok b ∧
      firstFailure (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).trace = none ∧
      firstFailure (analyticalFinish g word b (analyticalA g word inp.aMain).state.main
        (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves).trace = none ∧
      out = finishOutput g
        (analyticalFinish g word b (analyticalA g word inp.aMain).state.main
          (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves).state.main
        (analyticalFinish g word b (analyticalA g word inp.aMain).state.main
          (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves).tier := by
  obtain ⟨hg,hi,_⟩ := DirectJobPublication g oldWord word inp out hpub
  have hdne : g.digit ≠ 1 := by omega
  simp only [runJob,hg,hi,not_true_eq_false,ite_false,hdne] at hpub
  cases ha : prepareA g word inp.aMain with
  | error e => simp only [ha] at hpub; cases hpub
  | ok a =>
    simp only [ha] at hpub
    cases hb : buildB g word inp with
    | error e => simp only [hb] at hpub; cases hpub
    | ok b =>
      simp only [hb] at hpub
      cases hl : distributeABounded g word (aOperational a inp.aTier b.tier) with
      | error e => simp only [hl] at hpub; cases hpub
      | ok leaves =>
        simp only [hl] at hpub
        cases hf : finishBounded g word b a.main leaves with
        | error e => simp only [hf] at hpub; cases hpub
        | ok published =>
          simp only [hf,LaneResult.published.injEq] at hpub
          subst published
          have heA := DirectJobPublicationLemmas.prepare_success g word inp.aMain a ha
          have heL := DirectJobPublicationLemmas.distribution_success g word _ leaves hl
          rw [heL,heA] at hf
          rw [heA] at hl ha
          have hdist : firstFailure (distributeA g word
              (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).trace = none := by
            unfold distributeABounded at hl
            dsimp only at hl
            split at hl
            · cases hl
            · assumption
          have hfin : firstFailure (analyticalFinish g word b (analyticalA g word inp.aMain).state.main
              (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves).trace = none := by
            rw [DirectJobFinishSimulation] at hf
            split at hf
            · cases hf
            · assumption
          exact ⟨hg,hi,congrArg Except.ok heA,b,rfl,hdist,hfin,DirectJobPublicationLemmas.finish_success g word b _ _ out hf⟩

end RebuildBound.NativeMatchDirectSuccess


namespace RebuildBound.NativeMatchDirectSuccess
open Model Model.DirectJob Spec

theorem first (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (out : Output) (hd : g.digit = 1) (hpub : runJob g oldWord word inp = .published out) :
    g.Valid ∧ inp.Valid g oldWord ∧
    ∃ b, buildB g word inp = .ok b ∧ out = finishOutput g b.bLanes (b.tier.map some) := by
  obtain ⟨hg,hi,_⟩ := DirectJobPublication g oldWord word inp out hpub
  simp only [runJob,hg,hi,not_true_eq_false,ite_false,hd,ite_true] at hpub
  cases hb : buildB g word inp with
  | error e => simp only [hb] at hpub; cases hpub
  | ok b =>
    simp only [hb,LaneResult.published.injEq] at hpub
    exact ⟨hg,hi,b,rfl,hpub.symm⟩

end RebuildBound.NativeMatchDirectSuccess

