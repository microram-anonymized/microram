import RebuildBound.Proofs.SJob
import RebuildBound.Spec.Subtotal

/-! SelJob: SJob at the selected parameters, plus monotonicity of `sepBound`. -/

open scoped ENNReal NNReal

namespace RebuildBound.SelJobAux
open RebuildBound.Spec RebuildBound.Model

lemma Bsub_mono (n C : ℕ) {lam : ℝ} (h : 0 ≤ lam) (S : ℕ) {D D' : ℝ} (hD : D ≤ D') (_h0 : 0 ≤ D) :
    Bsub n C lam S D ≤ Bsub n C lam S D' := by
  unfold Bsub
  have hs : 0 ≤ ∑ j ∈ Finset.Icc 1 n, (n.choose j : ℝ) * Real.exp (lam * j * (subsetZ C lam S j - 1)) /
      subsetZ C lam S j ^ (C * j + S + 1) := by
    refine Finset.sum_nonneg fun j _ => ?_
    have : 0 ≤ subsetZ C lam S j := by unfold subsetZ; positivity
    positivity
  exact min_le_min le_rfl (mul_le_mul_of_nonneg_right hD hs)

lemma witness_mono (N C : ℕ) {lam : ℝ} (h : 0 ≤ lam) (S K : ℕ) {D D' : ℝ} (hD : D ≤ D')
    (h0 : 0 ≤ D) : witness N C lam S K D ≤ witness N C lam S K D' := by
  unfold witness
  exact min_le_min (Bsub_mono N C h S hD h0)
    (mul_le_mul_of_nonneg_right hD (G3Proof.Phi_nonneg K N C h S))

lemma base_ge (g : SepGeom) (W : ℕ) (hr : 1 ≤ g.r) :
    1 ≤ (((g.r * ((2 ^ (W - g.k) + g.r - 1) / g.r) : ℕ) : ℝ) / (2 ^ (W - g.k) : ℝ)) := by
  have hM : (0 : ℝ) < 2 ^ (W - g.k) := by positivity
  rw [one_le_div hM]
  have hr0 : 0 < g.r := hr
  have h1 := Nat.div_add_mod (2 ^ (W - g.k) + g.r - 1) g.r
  have h2 := Nat.mod_lt (2 ^ (W - g.k) + g.r - 1) hr0
  have : 2 ^ (W - g.k) ≤ g.r * ((2 ^ (W - g.k) + g.r - 1) / g.r) := by
    generalize g.r * ((2 ^ (W - g.k) + g.r - 1) / g.r) = x at h1
    generalize (2 ^ (W - g.k) + g.r - 1) % g.r = t at h1 h2
    omega
  exact_mod_cast this

lemma curDensity_mono (g : SepGeom) (W : ℕ) (hr : 1 ≤ g.r) {n n' : ℕ} (h : n ≤ n') :
    g.curDensity W n ≤ g.curDensity W n' :=
  pow_le_pow_right₀ (base_ge g W hr) h

lemma curDensity_nonneg (g : SepGeom) (W n : ℕ) : 0 ≤ g.curDensity W n := by
  unfold SepGeom.curDensity; positivity

lemma sepBound_mono (g : SepGeom) (W : ℕ) (lam : ℝ≥0) {D D' : ℝ≥0} {nA nA' nU nU' : ℕ}
    (K1 K2 : ℕ) (hr : 1 ≤ g.r) (hD : D ≤ D') (hA : nA ≤ nA') (hU : nU ≤ nU') :
    sepBound g W lam D nA nU K1 K2 ≤ sepBound g W lam D' nA' nU' K1 K2 := by
  unfold sepBound
  have hl : (0 : ℝ) ≤ lam := lam.2
  have hD' : (D : ℝ) ≤ D' := by exact_mod_cast hD
  gcongr
  · exact witness_mono _ _ hl _ _ hD' D.2
  · split_ifs
    · gcongr; exact witness_mono _ _ hl _ _ (curDensity_mono g W hr hA) (curDensity_nonneg g W nA)
    · exact le_rfl
  · exact witness_mono _ _ hl _ _ (curDensity_mono g W hr hU) (curDensity_nonneg g W nU)

lemma rows_ok : ∀ g ∈ (uniformSeparated ++ halfFanoutSeparated).map Prod.fst,
    g.Valid ∧ g.I < g.K ∧ g.C = 64 ∧ g.stashPages * g.C < 256 ∧
      min (g.stashPages * g.C) (g.tierPages * g.C) < 256 := by
  unfold uniformSeparated halfFanoutSeparated
  decide +kernel

end RebuildBound.SelJobAux

open RebuildBound.Spec RebuildBound.Model RebuildBound.SelJobAux in
/-- The separated analytic bound at any geometry satisfying its cutoff conditions. -/
theorem RebuildBound.selJobFor (g : SepGeom) (L : SJobLaw g) (D : ℝ≥0) (rule : CapRule)
    (hv : g.Valid) (hI : g.I < g.K) (hC : g.C = 64)
    (hs : g.stashPages * g.C < 256)
    (hm : min (g.stashPages * g.C) (g.tierPages * g.C) < 256)
    (hL : SInputLaw L 32 D) (hrule : rule.Valid) (hW : L.W = 64)
    (hD : D ≤ g.oldDensity 64 (32 * ((g.d - 1) * g.U))) :
    L.prob (fun hist w => STiersFit g (L.inputs hist w) ∧
      (sJob rule g w (L.inputs hist w)).toBool = false) ≤ selSepBound g := by
  have hlam : (0 : ℝ≥0) < 32 := by norm_num
  have hC' : ((32 : ℝ≥0) : ℝ) ≤ g.C := by rw [hC]; norm_num
  have hSJ := RebuildBound.SJob g L 32 D rule 256 256 hv hL hrule hlam hC' hI hs hm
  refine hSJ.trans ?_
  unfold RebuildBound.Spec.selSepBound
  rw [hW]
  have hA : L.KA.card ≤ 32 * ((g.d - 1) * g.U) := by
    have := hL.aLoad
    exact_mod_cast this
  have hB : L.KB.card ≤ 32 * g.U := by
    have := hL.bLoad
    exact_mod_cast this
  have hu : (L.KA ∪ L.KB).card ≤ 32 * g.N := by
    refine (Finset.card_union_le _ _).trans ?_
    have hN : g.N = g.d * g.U := by
      simp [SepGeom.N, SepGeom.d, SepGeom.U, SepGeom.k, pow_add]; ring
    have hd : 1 ≤ g.d := by have := hv.2.1; omega
    rw [hN]
    calc L.KA.card + L.KB.card ≤ 32 * ((g.d - 1) * g.U) + 32 * g.U := by omega
      _ = 32 * (g.d * g.U) := by
        obtain ⟨m, hm⟩ : ∃ m, g.d = m + 1 := ⟨g.d - 1, by omega⟩
        rw [hm]; simp; ring
  exact sepBound_mono g 64 32 256 256 hv.1 hD hA hu

theorem RebuildBound.SelJob : RebuildBound.Spec.SelJob_statement := by
  intro g hg L D rule hL hrule hW hD
  obtain ⟨hv, hI, hC, hs, hm⟩ := RebuildBound.SelJobAux.rows_ok g hg
  exact RebuildBound.selJobFor g L D rule hv hI hC hs hm hL hrule hW hD
