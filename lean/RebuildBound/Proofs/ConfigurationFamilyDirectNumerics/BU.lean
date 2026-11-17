import RebuildBound.Proofs.ConfigurationFamilyDirectNumerics.Check

/-! Share each checked complete-excess bound and full-shape density adapter
across every family occurrence. The final dyadic budgets round upward. -/

open scoped ENNReal
namespace RebuildBound
open Model Spec Spec.ConfigurationFamily ConfigurationFamilyDirectNumericsProof

namespace ConfigurationFamilyDirectNumericsProof

theorem density_le (g : SepGeom)
    (hsize : 32 * g.N < 2 ^ 64)
    (hc : SelRest.dens 64 (g.r * ((2 ^ (64 - g.k) + g.r - 1) / g.r))
      (64 - g.k) (32 * g.N) ≤ 2 * 2 ^ 64) :
    g.curDensity 64 (32 * g.N) ≤ 2 := by
  have hpow := SelRest.dens_le 64 (g.r * ((2 ^ (64 - g.k) + g.r - 1) / g.r))
    (64 - g.k) (32 * g.N) hsize
  have hreal : (SelRest.dens 64 (g.r * ((2 ^ (64 - g.k) + g.r - 1) / g.r))
      (64 - g.k) (32 * g.N) : ℝ) ≤ 2 * 2 ^ 64 := by exact_mod_cast hc
  exact hpow.trans ((div_le_iff₀ (by positivity)).2 hreal)

theorem shape_bounds (x : DirectJob.Geometry × SepGeom) (hx : x ∈ directShapes) :
    Phi 256 x.1.U 64 32 x.1.bCapacity ≤ 1 / (2 : ℝ) ^ 117 ∧
    x.2.curDensity 64 (32 * x.2.N) *
      Phi 256 x.1.outputHomes 64 32 x.1.outputCapacity ≤ 1 / (2 : ℝ) ^ 111 := by
  obtain ⟨hB, hU, hBC, hUC⟩ := dimensions x hx
  obtain ⟨_, hsize, hd⟩ := densityCheck x hx
  constructor
  · rw [hBC]
    exact NumericalPhi.single_le 256 x.1.U 64 64 117 (producerCheck _ hB)
  · rw [hUC]
    have hphi := NumericalPhi.single_le 256 x.1.outputHomes 64 64 112 (outputCheck _ hU)
    calc x.2.curDensity 64 (32 * x.2.N) * Phi 256 x.1.outputHomes 64 32 64
        ≤ 2 * (1 / (2 : ℝ) ^ 112) := mul_le_mul (density_le x.2 hsize hd) hphi
          (G3Proof.Phi_nonneg _ _ _ (by norm_num) _) (by norm_num)
      _ = 1 / (2 : ℝ) ^ 111 := by norm_num

end ConfigurationFamilyDirectNumericsProof

theorem ConfigurationFamilyDirectBUNumerics : ConfigurationFamilyDirectBUNumerics_statement := by
  intro m hm d hd hdn
  have hmem := coverage m hm d (List.mem_range'.2 ⟨d - 1, by omega, by omega⟩)
  have h := shape_bounds _ hmem
  exact ⟨ENNReal.ofReal_le_ofReal h.1, ENNReal.ofReal_le_ofReal h.2⟩

end RebuildBound
