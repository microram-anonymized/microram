import RebuildBound.Spec.AdaptiveSteps
import RebuildBound.Proofs.HierarchyLocality.Table

/-! # AdaptiveTracePrefix: tables and job outcomes depend only on a prefix of the units

Strong induction on the level and then the ordinal, through `table_eq`. The
carry step uses the identity `time (ℓ - 1) (v * fanout (ℓ - 1)) = time ℓ v`,
which holds for every configuration (no fanout facts needed).

No probability is involved, so no measure-theoretic obstacle arose.
-/

namespace RebuildBound
open Model Model.Hierarchy Spec

namespace AdaptiveTracePrefixProof

theorem foldr_mul_append (l r : List Nat) :
    (l ++ r).foldr (· * ·) 1 = l.foldr (· * ·) 1 * r.foldr (· * ·) 1 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.foldr_cons, ih, Nat.mul_assoc]

/-- The carry identity, with no facts about the fanouts. -/
theorem time_carry (cfg : Config) (ℓ v : Nat) (h2 : 2 ≤ ℓ) (hL : ℓ ≤ cfg.levels) :
    time cfg (ℓ - 1) (v * cfg.fanout (ℓ - 1)) = time cfg ℓ v := by
  have hlt : ℓ - 2 < cfg.fanouts.length := by simp [Config.levels] at hL; omega
  have htake : cfg.fanouts.take (ℓ - 1) = cfg.fanouts.take (ℓ - 2) ++ [cfg.fanouts[ℓ - 2]] := by
    have : ℓ - 1 = (ℓ - 2) + 1 := by omega
    rw [this, List.take_add_one, List.getElem?_eq_getElem hlt]; rfl
  have hfan : cfg.fanout (ℓ - 1) = cfg.fanouts[ℓ - 2] := by
    simp [Config.fanout, List.getD, show ℓ - 1 - 1 = ℓ - 2 by omega, List.getElem?_eq_getElem hlt]
  unfold time
  rw [htake, foldr_mul_append, hfan, show ℓ - 1 - 1 = ℓ - 2 by omega]
  simp [Nat.mul_comm, Nat.mul_left_comm]

theorem time_one (cfg : Config) (v : Nat) : time cfg 1 v = v := by simp [time]

/-- The table part. -/
theorem table_prefix (cfg : Config) (sh : Shapes) (tr tr' : Trace) (words : Words) (K : Nat)
    (hi : tr.init = tr'.init) (hu : tr.unsh = tr'.unsh)
    (hun : ∀ i, cfg.seed 1 + i + 1 ≤ K → tr.units i = tr'.units i) :
    ∀ ℓ v, time cfg ℓ v ≤ K → table cfg sh tr words ℓ v = table cfg sh tr' words ℓ v := by
  have hbase : ∀ ℓ, base cfg sh tr words ℓ = base cfg sh tr' words ℓ := by
    intro ℓ; unfold base initOutput; rw [hi]
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ihℓ =>
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ihv =>
      intro hK
      rw [HierarchyLocalityProof.table_eq cfg sh tr words ℓ v,
        HierarchyLocalityProof.table_eq cfg sh tr' words ℓ v]
      split_ifs with h1 hl1
      · exact hbase ℓ
      · subst hl1
        have hprev : table cfg sh tr words 1 (v - 1) = table cfg sh tr' words 1 (v - 1) :=
          ihv (v - 1) (by omega) (le_trans (Nat.mul_le_mul_right _ (Nat.sub_le v 1)) hK)
        rw [hprev]
        unfold step prepOutput
        rw [hu]
        rw [time_one] at hK
        rw [hun (v - cfg.seed 1 - 1) (by omega)]
      · have hprev : table cfg sh tr words ℓ (v - 1) = table cfg sh tr' words ℓ (v - 1) :=
          ihv (v - 1) (by omega) (le_trans (Nat.mul_le_mul_right _ (Nat.sub_le v 1)) hK)
        have hc : table cfg sh tr words (ℓ - 1) (v * cfg.fanout (ℓ - 1)) =
            table cfg sh tr' words (ℓ - 1) (v * cfg.fanout (ℓ - 1)) :=
          ihℓ (ℓ - 1) (by omega) _ (by rw [time_carry cfg ℓ v (by omega) (by omega)]; exact hK)
        rw [hprev, hc]
        unfold step prepOutput
        rw [hu]
        simp only [hl1, ite_false]

/-- The job part. -/
theorem jobs_prefix (cfg : Config) (sh : Shapes) (tr tr' : Trace) (words : Words) (K : Nat)
    (hi : tr.init = tr'.init) (hu : tr.unsh = tr'.unsh)
    (hun : ∀ i, cfg.seed 1 + i + 1 ≤ K → tr.units i = tr'.units i) :
    ∀ j ∈ cfg.potentialJobs, jobTime cfg j ≤ K →
      jobFails cfg sh tr words j = jobFails cfg sh tr' words j ∧
        (jobTiersFit cfg sh tr words j ↔ jobTiersFit cfg sh tr' words j) := by
  have ht := table_prefix cfg sh tr tr' words K hi hu hun
  intro j hj hK
  cases j with
  | ordinary ℓ o =>
    simp only [jobTime] at hK
    have hmem : 1 ≤ ℓ ∧ ℓ < cfg.levels ∧ cfg.seed ℓ < o := by
      simp [Config.potentialJobs, Config.ordinaryLevels] at hj
      obtain ⟨a, ha, i, _, h1, h2⟩ := hj
      subst h1 h2
      omega
    have hprev : table cfg sh tr words ℓ (o - 1) = table cfg sh tr' words ℓ (o - 1) :=
      ht ℓ (o - 1) (le_trans (Nat.mul_le_mul_right _ (Nat.sub_le o 1)) hK)
    by_cases hl1 : ℓ = 1
    · subst hl1
      rw [time_one] at hK
      have hu1 := hun (o - cfg.seed 1 - 1) (by omega)
      simp only [jobFails, jobTiersFit, levelOneResult, levelOneInputs, hprev, hu1]
      simp
    · have hc : carryOf cfg sh tr words ℓ o = carryOf cfg sh tr' words ℓ o :=
        ht (ℓ - 1) _ (by rw [time_carry cfg ℓ o (by omega) (by omega)]; exact hK)
      simp only [jobFails, jobTiersFit, sepResult, sepInputsAt, hprev, hc, hl1, ite_false, false_or]
      simp
  | topPrepare o =>
    simp only [jobTime] at hK
    have hprev := ht cfg.levels (o - 1) hK
    simp only [jobFails, jobTiersFit, prepResult, prepInputsAt, hprev, hu]
    simp
  | topFinish o =>
    simp only [jobTime] at hK
    have hprev := ht cfg.levels (o - 1) (le_trans (Nat.mul_le_mul_right _ (Nat.sub_le o 1)) hK)
    have hc : carryOf cfg sh tr words cfg.levels o = carryOf cfg sh tr' words cfg.levels o := by
      by_cases hL : 2 ≤ cfg.levels
      · exact ht (cfg.levels - 1) _ (by rw [time_carry cfg cfg.levels o hL le_rfl]; exact hK)
      · have : cfg.levels - 1 = 0 := by omega
        unfold carryOf; rw [this]
        rw [HierarchyLocalityProof.table_eq cfg sh tr words 0,
          HierarchyLocalityProof.table_eq cfg sh tr' words 0]
        have h0 : (0 = cfg.levels) = False := by simp [Config.levels]
        simp [base, h0]
    simp only [jobFails, jobTiersFit, finishResult, finishInputsAt, prepOutput, hprev, hc, hu]
    simp
  | initialization =>
    simp only [jobFails, jobTiersFit, initResult, hi]; simp

end AdaptiveTracePrefixProof

open AdaptiveTracePrefixProof in
theorem TracePrefix : TracePrefix_statement := fun cfg sh tr tr' words K hi hu hun =>
  ⟨table_prefix cfg sh tr tr' words K hi hu hun, jobs_prefix cfg sh tr tr' words K hi hu hun⟩

end RebuildBound
