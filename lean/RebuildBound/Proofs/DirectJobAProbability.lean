import RebuildBound.Spec.DirectJobAProbability
import RebuildBound.Proofs.DirectJobANumerics
import RebuildBound.Proofs.DirectJobABounds
import RebuildBound.Proofs.DirectJobProbability
import RebuildBound.Proofs.DirectJobSelected
import RebuildBound.Proofs.SelJob

open scoped ENNReal NNReal
namespace RebuildBound
open Model Model.DirectJob Spec

theorem DirectJobSelectedAProbability : DirectJobSelectedAProbability_statement := by
  intro d hlo hhi L D hL hW hD direct hmatch
  let s := selectedDirectSep d
  let g := selectedDirectGeometry d
  have hg := DirectJobSelectedGeometry.1 d (by omega) hhi
  obtain ⟨hs, hIK, _, _, _⟩ := DirectJobSelectedGeometry.2 d hlo hhi
  have hc := DirectJobSelectedAAdapter d hlo hhi
  have hd : 2 ≤ g.digit := by
    change 2 ≤ (selectedDirectGeometry d).digit
    simp [selectedDirectGeometry, show d ≠ 1 by omega]
    exact hlo
  have hC : s.C = 64 := rfl
  have hcut : s.stashPages * s.C < 256 := by change 64 < 256; norm_num
  have ha := DirectJobAWitnessProbability g s hg hd hc hs L 32 D 256 hL
    (by norm_num) (by rw [hC]; norm_num) hIK hcut direct hmatch
  have hprob : L.prob (fun hist word =>
      (direct hist word).aTier.length ≤ g.aTierCapacity ∧
      (aRouteWitness g word (direct hist word) ∨ aRangeWitness g word (direct hist word))) ≤
      L.prob (fun hist word => STiersFit s (L.inputs hist word) ∧
        (aRouteWitness g word (direct hist word) ∨ aRangeWitness g word (direct hist word))) := by
    apply SG1Proof.prob_mono L
    intro hist hw h
    refine ⟨?_, h.2⟩
    change (L.inputs hist (L.wordFn hw)).aTier.length ≤ s.aTierPages * s.C
    rw [← (hmatch hist hw).2, ← hc.tier]
    exact h.1
  have hA : L.KA.card ≤ 32 * ((s.d - 1) * s.U) := by
    exact_mod_cast hL.aLoad
  have hsep : L.prob (fun hist word =>
      (direct hist word).aTier.length ≤ g.aTierCapacity ∧
      (aRouteWitness g word (direct hist word) ∨ aRangeWitness g word (direct hist word))) ≤
      sepBound s L.W 32 D L.KA.card (32 * s.N) 256 256 :=
    (hprob.trans ha).trans le_self_add
  have hmono := SelJobAux.sepBound_mono s 64 32 256 256 hs.1 hD hA
    (le_refl (32 * s.N))
  rw [hW] at hsep
  have hn := DirectJobSelectedANumerics d hlo hhi
  simpa only [selectedDirectABudget, ite_eq_right (show d ≠ 1 by omega)] using
    (hsep.trans hmono).trans hn

private theorem budget_ne_top (d : Nat) :
    selectedDirectBound selectedDirectABudget d ≠ ⊤ := by
  unfold selectedDirectBound selectedDirectABudget
  split_ifs <;> simp

private theorem direct_sum_ne_top (cfg : Config) (xs : List Nat) :
    (xs.map fun i => (cfg.ordinaryCount 1 (i + 1) : ℝ≥0∞) *
      selectedDirectBound selectedDirectABudget (i + 1)).sum ≠ ⊤ := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top _) (budget_ne_top _), ih⟩

private theorem budget_real (d : Nat) :
    (selectedDirectBound selectedDirectABudget d).toReal =
      1 / (2 : ℝ) ^ 117 + (if d = 1 then 0 else 1 / (2 : ℝ) ^ 102) + 1 / (2 : ℝ) ^ 111 := by
  unfold selectedDirectBound selectedDirectABudget
  split_ifs <;> norm_num [ENNReal.toReal_add]

private theorem direct_sum_real (cfg : Config) (xs : List Nat) :
    ((xs.map fun i => (cfg.ordinaryCount 1 (i + 1) : ℝ≥0∞) *
      selectedDirectBound selectedDirectABudget (i + 1)).sum).toReal =
    (xs.map fun i => (cfg.ordinaryCount 1 (i + 1) : ℝ) *
      (1 / (2 : ℝ) ^ 117 + (if i + 1 = 1 then 0 else 1 / (2 : ℝ) ^ 102) +
        1 / (2 : ℝ) ^ 111)).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (budget_ne_top _))
      (direct_sum_ne_top cfg xs), ih, ENNReal.toReal_mul, ENNReal.toReal_natCast, budget_real]

private theorem lifetime_ne_top (cfg : Config) : selectedDirectLifetimeBudget cfg ≠ ⊤ :=
  ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top 258) ENNReal.ofReal_ne_top⟩,
    direct_sum_ne_top cfg _⟩

private theorem lifetime_real (cfg : Config) :
    (selectedDirectLifetimeBudget cfg).toReal =
    129 / (100 * (2 : ℝ) ^ 70) + 258 * (1 / (2 : ℝ) ^ 115) +
    ((List.range (cfg.fanout 1)).map fun i => (cfg.ordinaryCount 1 (i + 1) : ℝ) *
      (1 / (2 : ℝ) ^ 117 + (if i + 1 = 1 then 0 else 1 / (2 : ℝ) ^ 102) +
        1 / (2 : ℝ) ^ 111)).sum := by
  unfold selectedDirectLifetimeBudget
  have h258 : (258 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [ENNReal.toReal_add
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top h258 ENNReal.ofReal_ne_top⟩)
    (direct_sum_ne_top cfg _),
    ENNReal.toReal_add ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top h258 ENNReal.ofReal_ne_top),
    direct_sum_real, ENNReal.toReal_mul]
  norm_num

private theorem uniform_count (d : Nat) (hlo : 1 ≤ d) (hhi : d ≤ 8) :
    uniformConfig.ordinaryCount 1 d = if d = 1 then 1048577 else 1048576 := by
  interval_cases d <;> decide +kernel

private theorem half_count (d : Nat) (hlo : 1 ≤ d) (hhi : d ≤ 4) :
    halfFanoutConfig.ordinaryCount 1 d = if d = 1 then 2097153 else 2097152 := by
  interval_cases d <;> decide +kernel

theorem DirectJobSelectedLifetimeNumerics : DirectJobSelectedLifetimeNumerics_statement := by
  constructor <;>
    rw [ENNReal.le_ofReal_iff_toReal_le (lifetime_ne_top _) (by positivity), lifetime_real]
  · change _ + _ + (([0,1,2,3,4,5,6,7] : List Nat).map _).sum ≤ _
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    norm_num [uniform_count]
  · change _ + _ + (([0,1,2,3] : List Nat).map _).sum ≤ _
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    norm_num [half_count]

end RebuildBound
