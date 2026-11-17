import RebuildBound.Spec.DirectJobOldWordDensity
import RebuildBound.Proofs.WordHomeFibers

open scoped ENNReal NNReal
namespace RebuildBound
open Model Spec

private theorem old_eq (d : Nat) (hl : 2 ≤ d) (hu : d ≤ 8) (t : Nat) :
    (selectedDirectSep d).oldHome t = (selectedDirectSep (d-1)).homeOf t := by
  interval_cases d <;> rfl

private theorem density_eq (d : Nat) (hl : 2 ≤ d) (hu : d ≤ 8) (n : Nat) :
    ((selectedDirectSep d).oldDensity 64 n : ℝ≥0∞) /
      ((((selectedDirectSep d).d - 1) * (selectedDirectSep d).U : Nat) : ℝ≥0∞)^n =
    (((2^(64-(selectedDirectSep (d-1)).k) + (selectedDirectSep (d-1)).r - 1) /
      (selectedDirectSep (d-1)).r : Nat) : ℝ≥0∞)^n / (2^64 : ℝ≥0∞)^n := by
  have hh : (selectedDirectSep d).oldDensity 64 n /
      ((((selectedDirectSep d).d - 1) * (selectedDirectSep d).U : Nat) : ℝ≥0)^n =
      (((2^(64-(selectedDirectSep (d-1)).k) + (selectedDirectSep (d-1)).r - 1) /
      (selectedDirectSep (d-1)).r : Nat) : ℝ≥0)^n / (2^64 : ℝ≥0)^n := by
    interval_cases d <;>
      norm_num [selectedDirectSep, SepGeom.oldDensity, SepGeom.d, SepGeom.U,
        SepGeom.k, val2, val2Aux]
    all_goals simp only [← div_pow, ← inv_pow]
    all_goals (congr 1; norm_num)
  have hpos : (0 : ℝ≥0) < ((((selectedDirectSep d).d - 1) * (selectedDirectSep d).U : Nat) : ℝ≥0) := by
    interval_cases d <;> norm_num [selectedDirectSep, SepGeom.d, SepGeom.U, val2, val2Aux]
  simpa only [ENNReal.coe_div (ne_of_gt (pow_pos hpos n)),
    ENNReal.coe_div (ne_of_gt (pow_pos (by norm_num : (0 : ℝ≥0) < 2^64) n)),
    ENNReal.coe_pow, ENNReal.coe_natCast, ENNReal.coe_ofNat] using
    congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hh

theorem selected_oldDensity_mono (d : Nat) (hl : 2 ≤ d) (hu : d ≤ 8)
    (n n' : Nat) (hn : n ≤ n') :
    (selectedDirectSep d).oldDensity 64 n ≤ (selectedDirectSep d).oldDensity 64 n' := by
  interval_cases d <;>
    norm_num [selectedDirectSep, SepGeom.oldDensity, SepGeom.d, val2, val2Aux] <;>
    apply pow_le_pow_right₀ _ hn <;> norm_num [one_le_div]

theorem DirectJobOldWordDensity : DirectJobOldWordDensity_statement := by
  classical
  intro d hl hu keys target
  let g := selectedDirectSep (d-1)
  have hr : 0 < g.r := by
    dsimp [g]; interval_cases d <;> decide
  have hk : g.k ≤ 64 := by
    dsimp [g]; interval_cases d <;> decide
  have hb := WordHomeFibers g 64 keys hr hk (fun x => (target x : Nat))
  have he : (Finset.univ.filter (fun h : keys → Fin (2^64) =>
      ∀ x, (selectedDirectSep d).oldHome (h x) = (target x : Nat))).card ≤
      ((2^(64-g.k)+g.r-1)/g.r)^keys.card := by
    simpa only [old_eq d hl hu] using hb
  rw [density_eq d hl hu]
  have hs : (∑ h : keys → Fin (2^64),
      if ∀ x, (selectedDirectSep d).oldHome (h x) = (target x : Nat) then (1 : ℝ≥0∞) else 0) =
      ((Finset.univ.filter (fun h : keys → Fin (2^64) =>
        ∀ x, (selectedDirectSep d).oldHome (h x) = (target x : Nat))).card : ℝ≥0∞) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hs, Fintype.card_pi, Fintype.card_fin]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe, Nat.cast_pow]
  rw [mul_comm, ← div_eq_mul_inv]
  apply ENNReal.div_le_div_right
  exact_mod_cast he
end RebuildBound
