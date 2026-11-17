import RebuildBound.Spec.Hierarchy
import RebuildBound.Proofs.WordHomeFibers
import RebuildBound.Proofs.SG1.Dens

/-!
# OldWordDensity: the old-home density of independent uniform 64-bit words

Generalises `DirectJobOldWordDensity` to every `SepGeom` with `d - 1 ≥ 1` and
`K + val2 (d - 1) ≤ 64`: the previous digit's map is the home map of the
geometry `g'` with `e = val2 (d - 1)`, `r = (d - 1) / 2^e`, so
`WordHomeFibers` bounds the count of words with the given old homes.
-/

open scoped ENNReal NNReal
namespace RebuildBound
open Model Spec

namespace OldWordDensityProof

/-- The previous digit's geometry. -/
def prevGeom (g : SepGeom) : SepGeom :=
  { g with e := val2 (g.d - 1), r := (g.d - 1) / 2 ^ val2 (g.d - 1) }

theorem old_eq (g : SepGeom) (t : Nat) : g.oldHome t = (prevGeom g).homeOf t := rfl

theorem prev_r_mul (g : SepGeom) :
    (prevGeom g).r * 2 ^ val2 (g.d - 1) = g.d - 1 :=
  Nat.div_mul_cancel (SG1Proof.val2_dvd _)

theorem prev_r_pos (g : SepGeom) (hD : 1 ≤ g.d - 1) : 0 < (prevGeom g).r := by
  have h := prev_r_mul g
  rcases Nat.eq_zero_or_pos (prevGeom g).r with h0 | h0
  · rw [h0] at h; omega
  · exact h0

theorem density_eq (g : SepGeom) (hD : 1 ≤ g.d - 1) (hk : g.K + val2 (g.d - 1) ≤ 64)
    (n : Nat) :
    (g.oldDensity 64 n : ℝ≥0∞) / (((g.d - 1) * g.U : Nat) : ℝ≥0∞) ^ n =
    (((2 ^ (64 - (prevGeom g).k) + (prevGeom g).r - 1) / (prevGeom g).r : Nat) : ℝ≥0∞) ^ n /
      (2 ^ 64 : ℝ≥0∞) ^ n := by
  set r := (prevGeom g).r with hr
  set k := (prevGeom g).k with hkdef
  have hkk : k = g.K + val2 (g.d - 1) := rfl
  set c := (2 ^ (64 - k) + r - 1) / r with hc
  have hrpos : 0 < r := prev_r_pos g hD
  have hden : (g.d - 1) * g.U = r * 2 ^ k := by
    rw [← prev_r_mul g, hkk, SepGeom.U, pow_add]; ring
  have hold : g.oldDensity 64 n = (((r * c : Nat) : ℝ≥0) / 2 ^ (64 - k)) ^ n := by
    simp only [SepGeom.oldDensity, hk, ↓reduceIte]; rfl
  have h2 : (2 : ℝ≥0) ^ (64 - k) * 2 ^ k = 2 ^ 64 := by
    rw [← pow_add, Nat.sub_add_cancel (hkk ▸ hk)]
  have hh : g.oldDensity 64 n / (((g.d - 1) * g.U : Nat) : ℝ≥0) ^ n =
      ((c : Nat) : ℝ≥0) ^ n / (2 ^ 64 : ℝ≥0) ^ n := by
    rw [hold, hden, ← div_pow, ← div_pow]
    congr 1
    have hr0 : (r : ℝ≥0) ≠ 0 := by exact_mod_cast hrpos.ne'
    rw [← h2]
    push_cast
    field_simp
  have hpos : (0 : ℝ≥0) < (((g.d - 1) * g.U : Nat) : ℝ≥0) := by
    rw [hden]; positivity
  simpa only [ENNReal.coe_div (ne_of_gt (pow_pos hpos n)),
    ENNReal.coe_div (ne_of_gt (pow_pos (by norm_num : (0 : ℝ≥0) < 2^64) n)),
    ENNReal.coe_pow, ENNReal.coe_natCast, ENNReal.coe_ofNat] using
    congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hh

end OldWordDensityProof

open OldWordDensityProof in
theorem OldWordDensity : OldWordDensity_statement := by
  classical
  intro g keys target hD hk
  let g' := prevGeom g
  have hr : 0 < g'.r := prev_r_pos g hD
  have hk' : g'.k ≤ 64 := hk
  have hb := WordHomeFibers g' 64 keys hr hk' (fun x => (target x : Nat))
  have he : (Finset.univ.filter (fun h : keys → Fin (2^64) =>
      ∀ x, g.oldHome (h x) = (target x : Nat))).card ≤
      ((2^(64-g'.k)+g'.r-1)/g'.r)^keys.card := by
    simp only [old_eq g]
    convert hb using 2
    ext h; simp [g']
  rw [density_eq g hD hk]
  have hs : (∑ h : keys → Fin (2^64),
      if ∀ x, g.oldHome (h x) = (target x : Nat) then (1 : ℝ≥0∞) else 0) =
      ((Finset.univ.filter (fun h : keys → Fin (2^64) =>
        ∀ x, g.oldHome (h x) = (target x : Nat))).card : ℝ≥0∞) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hs, Fintype.card_pi, Fintype.card_fin]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe, Nat.cast_pow]
  rw [mul_comm, ← div_eq_mul_inv]
  apply ENNReal.div_le_div_right
  exact_mod_cast he

end RebuildBound
