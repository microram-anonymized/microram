import RebuildBound.Proofs.G1.MGF
import RebuildBound.Proofs.StageAvg

/-!
# G1: the stage terms

For `j < k + 1`, the count vector `X_{j,v}` of A's complete population at its
raw destinations after the stage that reads bit `j` has the subset MGF
envelope with factor `D` and load `λ`; P3 then bounds the raw stage excess.
-/

open scoped ENNReal NNReal

namespace RebuildBound.G1Proof

open RebuildBound.Model RebuildBound.Spec

variable {g : Geom} (L : JobLaw g)

/-- The stage-`j` count vector: A's records at raw destination `v`. -/
def stageX (j : ℕ) (hist : L.Hist) (h : L.Key → Fin (2 ^ L.W)) (v : Fin g.homes) : ℕ :=
  (L.inputs hist (L.wordFn h)).aAll.countP fun r =>
    rawDest g (L.wOld hist) (L.wordFn h) j r.key == (v : ℕ)

variable {TA TB : ℕ} {lam D : ℝ≥0}

theorem stage_pow (hL : InputLaw L lam D) (j : ℕ) (hist : L.Hist)
    (h : L.Key → Fin (2 ^ L.W)) (J : Finset (Fin g.homes)) (z : ℝ) :
    z ^ (∑ v ∈ J, stageX L j hist h v) =
      ∏ x ∈ L.KA, (if rd g.U j (L.wOld hist x % g.U) (L.wordFn h x) ∈ J.map Fin.valEmbedding
        then z else 1) := by
  have hv := hL.shape hist h
  unfold stageX
  rw [pow_countP_sum z J _ _ hv.aNodup]
  have hk : ((L.inputs hist (L.wordFn h)).aAll.map Rec.key).toFinset = L.KA := hL.aKeys hist
  rw [hk]
  rfl

theorem stage_hist (hL : InputLaw L lam D) (j : ℕ) (hist : L.Hist)
    (J : Finset (Fin g.homes)) (z : ℝ) (hz : 1 ≤ z) :
    (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h, ENNReal.ofReal (z ^ ∑ v ∈ J, stageX L j hist h v) =
    ENNReal.ofReal (∏ x ∈ L.KA,
      stagePsi L.W g.U j (J.map Fin.valEmbedding) z (L.wOld hist x % g.U)) := by
  rw [Finset.sum_congr rfl fun h _ => by rw [stage_pow L hL j hist h J z]]
  rw [avg_wordFn_prod L L.KA Finset.subset_union_left
    (fun x a => if rd g.U j (L.wOld hist x % g.U) a ∈ J.map Fin.valEmbedding then z else 1)
    (by intro x a; split_ifs <;> linarith)]
  rfl

/-- The old-home average of the per-key average: the column sums of the raw
destination map are at most `2^W`. -/
theorem stagePsi_avg (W U j : ℕ) (hj : j + 1 ≤ W) (hU : 0 < U) (J' : Finset ℕ) (z : ℝ)
    (hz : 1 ≤ z) :
    (U : ℝ)⁻¹ * ∑ o : Fin U, stagePsi W U j J' z o ≤ 1 + (z - 1) * J'.card / U := by
  have hW : (0 : ℝ) < ((2 ^ W : ℕ) : ℝ) := by positivity
  have hU' : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  set N : ℕ → ℕ := fun o => ∑ a ∈ Finset.range (2 ^ W), if rd U j o a ∈ J' then 1 else 0
  have e : ∀ o, stagePsi W U j J' z o = 1 + (z - 1) * (N o : ℝ) / ((2 ^ W : ℕ) : ℝ) :=
    fun o => avg_ite (2 ^ W) (by positivity) (fun a => rd U j o a ∈ J') z
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun o => 1 + (z - 1) * (N o : ℝ) / ((2 ^ W : ℕ) : ℝ)) U]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    ← Finset.sum_div, ← Finset.mul_sum]
  have hS : ((∑ o ∈ Finset.range U, N o : ℕ) : ℝ) ≤ (J'.card : ℝ) * ((2 ^ W : ℕ) : ℝ) := by
    exact_mod_cast stage_count U W j hj J'
  have h1 : (z - 1) * (∑ o ∈ Finset.range U, (N o : ℝ)) / ((2 ^ W : ℕ) : ℝ) ≤
      (z - 1) * J'.card := by
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [div_le_iff₀ hW]
    push_cast at hS ⊢
    exact hS
  rw [mul_add, inv_mul_cancel₀ hU'.ne']
  calc 1 + (U : ℝ)⁻¹ * ((z - 1) * (∑ o ∈ Finset.range U, (N o : ℝ)) / ((2 ^ W : ℕ) : ℝ))
      ≤ 1 + (U : ℝ)⁻¹ * ((z - 1) * J'.card) := by gcongr
    _ = 1 + (z - 1) * J'.card / U := by ring

/-- **The stage-`j` MGF envelope.** -/
theorem stage_mgf (hL : InputLaw L lam D) (j : ℕ) (hj : j < g.stages)
    (J : Finset (Fin g.homes)) (z : ℝ) (hz : 1 ≤ z) :
    ∑ hist, L.weight hist * ((Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h, ENNReal.ofReal (z ^ ∑ v ∈ J, stageX L j hist h v)) ≤
    ENNReal.ofReal (D * Real.exp (lam * J.card * (z - 1))) := by
  have hU := U_pos g
  have hU' : (0 : ℝ) < (g.U : ℝ) := by exact_mod_cast hU
  have hjW : j + 1 ≤ L.W := by have := hL.wide; unfold Geom.stages at hj; omega
  rw [Finset.sum_congr rfl fun hist _ => by rw [stage_hist L hL j hist J z hz]]
  refine le_trans (density_bound L hL _ (stagePsi_nonneg _ _ _ _ z hz)) ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ D.2
  have hload : (L.KA.card : ℝ) ≤ lam * g.U := by
    have := NNReal.coe_le_coe.mpr hL.aLoad
    push_cast at this
    exact this
  have hc : 0 ≤ (z - 1) * J.card := mul_nonneg (by linarith) (by positivity)
  calc ((g.U : ℝ)⁻¹ * ∑ o : Fin g.U, stagePsi L.W g.U j (J.map Fin.valEmbedding) z o) ^ L.KA.card
      ≤ (1 + (z - 1) * J.card / g.U) ^ L.KA.card := by
        apply pow_le_pow_left₀
        · exact mul_nonneg (by positivity)
            (Finset.sum_nonneg fun o _ => stagePsi_nonneg _ _ _ _ z hz _)
        · have := stagePsi_avg L.W g.U j hjW hU (J.map Fin.valEmbedding) z hz
          rwa [Finset.card_map] at this
    _ ≤ Real.exp (lam * ((z - 1) * J.card)) := pow_le_exp _ _ _ _ hU' hc hload
    _ = Real.exp (lam * J.card * (z - 1)) := by ring_nf

/-- **The stage term.** -/
theorem stage_term (h3 : P3_statement) (hL : InputLaw L lam D) (hlam : 0 < lam)
    (hC : (lam : ℝ) ≤ g.C) (j : ℕ) (hj : j < g.stages) (S : ℕ) :
    L.prob (fun hist w => S < rawStageExcess g (L.wOld hist) w (L.inputs hist w) j) ≤
      ENNReal.ofReal (Bsub g.homes g.C lam S D) := by
  refine FiniteLawProof.prob_le_Bsub_of L.prob_eq h3 hL.weight_sum g.C S lam D
    (by exact_mod_cast hlam) hC D.2 (stageX L j) (fun J z hz => stage_mgf L hL j hj J z hz) _ ?_
  intro hist h hS
  refine lt_of_lt_of_eq hS ?_
  unfold rawStageExcess
  rw [list_sum_range, Finset.sum_range]
  rfl

end RebuildBound.G1Proof
