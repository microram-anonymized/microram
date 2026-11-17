import RebuildBound.Proofs.SG1.Count

/-!
# SG1: the subset MGF envelopes

* stage `j`: the raw destinations of the complete A population, factor `D`;
* current homes of a key set `K ⊆ KA ∪ KB` with `|K| ≤ λ N`, factor
  `curDensity W |K|` (the radix stash, the insertion stash and the output tier).
-/

open scoped ENNReal NNReal

namespace RebuildBound.SG1Proof

open RebuildBound.Model RebuildBound.Spec

variable {g : SepGeom} (L : SJobLaw g)

theorem M_pos (hg : g.Valid) : 0 < (g.d - 1) * g.U := by
  have := hg.2.1
  have := U_pos g
  exact Nat.mul_pos (by omega) this

/-! ### Stage `j` -/

/-- The stage-`j` count vector: A's records at raw destination `v`. -/
def stageX (j : ℕ) (hist : L.Hist) (h : L.Key → Fin (2 ^ L.W)) (v : Fin g.N) : ℕ :=
  (L.inputs hist (L.wordFn h)).aAll.countP fun r =>
    sRawDest g (L.wOld hist) (L.wordFn h) j r.key == (v : ℕ)

variable {lam D : ℝ≥0}

theorem stage_pow (hL : SInputLaw L lam D) (j : ℕ) (hist : L.Hist)
    (h : L.Key → Fin (2 ^ L.W)) (J : Finset (Fin g.N)) (z : ℝ) :
    z ^ (∑ v ∈ J, stageX L j hist h v) =
      ∏ x ∈ L.KA, (if G1Proof.rd g.U j (g.oldHome (L.wOld hist x)) (L.wordFn h x) ∈
        J.map Fin.valEmbedding then z else 1) := by
  have hv := hL.shape hist h
  unfold stageX
  rw [G1Proof.pow_countP_sum z J _ _ hv.aNodup]
  have hk : (((L.inputs hist (L.wordFn h)).aAll).map Rec.key).toFinset = L.KA := hL.aKeys hist
  rw [hk]
  rfl

theorem stage_hist (hL : SInputLaw L lam D) (j : ℕ) (hist : L.Hist)
    (J : Finset (Fin g.N)) (z : ℝ) (hz : 1 ≤ z) :
    (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h, ENNReal.ofReal (z ^ ∑ v ∈ J, stageX L j hist h v) =
    ENNReal.ofReal (∏ x ∈ L.KA,
      G1Proof.stagePsi L.W g.U j (J.map Fin.valEmbedding) z (g.oldHome (L.wOld hist x))) := by
  rw [Finset.sum_congr rfl fun h _ => by rw [stage_pow L hL j hist h J z]]
  rw [avg_wordFn_prod L L.KA Finset.subset_union_left
    (fun x a => if G1Proof.rd g.U j (g.oldHome (L.wOld hist x)) a ∈ J.map Fin.valEmbedding
      then z else 1)
    (by intro x a; split_ifs <;> linarith)]
  rfl

theorem stagePsi_avg' (W U M j : ℕ) (hj : j + 1 ≤ W) (hM : 0 < M) (J' : Finset ℕ) (z : ℝ)
    (hz : 1 ≤ z) :
    (M : ℝ)⁻¹ * ∑ o : Fin M, G1Proof.stagePsi W U j J' z o ≤ 1 + (z - 1) * J'.card / M := by
  have hW : (0 : ℝ) < ((2 ^ W : ℕ) : ℝ) := by positivity
  have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  set N : ℕ → ℕ := fun o => ∑ a ∈ Finset.range (2 ^ W), if G1Proof.rd U j o a ∈ J' then 1 else 0
  have e : ∀ o, G1Proof.stagePsi W U j J' z o = 1 + (z - 1) * (N o : ℝ) / ((2 ^ W : ℕ) : ℝ) :=
    fun o => G1Proof.avg_ite (2 ^ W) (by positivity) (fun a => G1Proof.rd U j o a ∈ J') z
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun o => 1 + (z - 1) * (N o : ℝ) / ((2 ^ W : ℕ) : ℝ)) M]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    ← Finset.sum_div, ← Finset.mul_sum]
  have hS : ((∑ o ∈ Finset.range M, N o : ℕ) : ℝ) ≤ (J'.card : ℝ) * ((2 ^ W : ℕ) : ℝ) := by
    exact_mod_cast stage_count' U M W j hj J'
  have h1 : (z - 1) * (∑ o ∈ Finset.range M, (N o : ℝ)) / ((2 ^ W : ℕ) : ℝ) ≤
      (z - 1) * J'.card := by
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [div_le_iff₀ hW]
    push_cast at hS ⊢
    exact hS
  rw [mul_add, inv_mul_cancel₀ hM'.ne']
  calc 1 + (M : ℝ)⁻¹ * ((z - 1) * (∑ o ∈ Finset.range M, (N o : ℝ)) / ((2 ^ W : ℕ) : ℝ))
      ≤ 1 + (M : ℝ)⁻¹ * ((z - 1) * J'.card) := by gcongr
    _ = 1 + (z - 1) * J'.card / M := by ring

/-- **The stage-`j` MGF envelope.** -/
theorem stage_mgf (hg : g.Valid) (hL : SInputLaw L lam D) (j : ℕ) (hj : j < g.k)
    (J : Finset (Fin g.N)) (z : ℝ) (hz : 1 ≤ z) :
    ∑ hist, L.weight hist * ((Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h, ENNReal.ofReal (z ^ ∑ v ∈ J, stageX L j hist h v)) ≤
    ENNReal.ofReal (D * Real.exp (lam * J.card * (z - 1))) := by
  classical
  have hM := M_pos hg
  have hM' : (0 : ℝ) < (((g.d - 1) * g.U : ℕ) : ℝ) := by exact_mod_cast hM
  have hjW : j + 1 ≤ L.W := by have := hL.wide; omega
  rw [Finset.sum_congr rfl fun hist _ => by rw [stage_hist L hL j hist J z hz]]
  let oh : L.Hist → (L.KA → Fin ((g.d - 1) * g.U)) :=
    fun hist x => ⟨g.oldHome (L.wOld hist x), oldHome_lt g hg.2.1 _⟩
  let ψ : Fin ((g.d - 1) * g.U) → ℝ :=
    fun o => G1Proof.stagePsi L.W g.U j (J.map Fin.valEmbedding) z o
  have hψ : ∀ o, 0 ≤ ψ o := fun o => G1Proof.stagePsi_nonneg _ _ _ _ z hz _
  have e : ∀ hist, ∏ x ∈ L.KA,
      G1Proof.stagePsi L.W g.U j (J.map Fin.valEmbedding) z (g.oldHome (L.wOld hist x)) =
      ∏ x : L.KA, ψ (oh hist x) := by
    intro hist
    exact (Finset.prod_coe_sort L.KA (fun x =>
      G1Proof.stagePsi L.W g.U j (J.map Fin.valEmbedding) z (g.oldHome (L.wOld hist x)))).symm
  simp_rw [e]
  refine le_trans (density_bound_M L (D := D) L.KA _ hM oh ?_ ψ hψ) ?_
  · intro o
    have hd := hL.density o
    convert hd using 2
    ext hist
    simp [oh, funext_iff, Fin.ext_iff]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ D.2
  have hload : (L.KA.card : ℝ) ≤ lam * (((g.d - 1) * g.U : ℕ) : ℝ) := by
    exact_mod_cast hL.aLoad
  have hc : 0 ≤ (z - 1) * J.card := mul_nonneg (by linarith) (by positivity)
  calc ((((g.d - 1) * g.U : ℕ) : ℝ)⁻¹ * ∑ o : Fin ((g.d - 1) * g.U), ψ o) ^ L.KA.card
      ≤ (1 + (z - 1) * J.card / (((g.d - 1) * g.U : ℕ) : ℝ)) ^ L.KA.card := by
        apply pow_le_pow_left₀
        · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun o _ => hψ o)
        · have := stagePsi_avg' L.W g.U _ j hjW hM (J.map Fin.valEmbedding) z hz
          rwa [Finset.card_map] at this
    _ ≤ Real.exp (lam * ((z - 1) * J.card)) := G1Proof.pow_le_exp _ _ _ _ hM' hc hload
    _ = Real.exp (lam * J.card * (z - 1)) := by ring_nf

/-! ### Current homes -/

/-- The base of `curDensity`. -/
noncomputable def cbase (g : SepGeom) (W : ℕ) : ℝ :=
  ((g.r * qOf g W : ℕ) : ℝ) / (2 ^ (W - g.k) : ℝ)

theorem curDensity_eq (g : SepGeom) (W n : ℕ) : g.curDensity W n = cbase g W ^ n := rfl

theorem one_le_cbase (g : SepGeom) (hr : 0 < g.r) (W : ℕ) : 1 ≤ cbase g W := by
  unfold cbase
  have h := le_r_mul_qOf g W hr
  have h' : ((2 ^ (W - g.k) : ℕ) : ℝ) ≤ ((g.r * qOf g W : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h' ⊢
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- The per-key average of `z^[home ∈ J]`. -/
noncomputable def homePsi (g : SepGeom) (W : ℕ) (J' : Finset ℕ) (z : ℝ) : ℝ :=
  ((2 ^ W : ℕ) : ℝ)⁻¹ * ∑ a : Fin (2 ^ W), (if g.homeOf a ∈ J' then z else 1)

theorem homePsi_nonneg (g : SepGeom) (W : ℕ) (J' : Finset ℕ) (z : ℝ) (hz : 1 ≤ z) :
    0 ≤ homePsi g W J' z := by
  unfold homePsi
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => ?_)
  split_ifs <;> linarith

theorem homePsi_le (g : SepGeom) (hr : 0 < g.r) (W : ℕ) (hW : g.k ≤ W) (J' : Finset ℕ) (z : ℝ)
    (hz : 1 ≤ z) :
    homePsi g W J' z ≤ 1 + (z - 1) * J'.card * cbase g W / (g.N : ℝ) := by
  unfold homePsi
  rw [G1Proof.avg_ite (2 ^ W) (by positivity) (fun a => g.homeOf a ∈ J') z]
  set cnt := ∑ a ∈ Finset.range (2 ^ W), if g.homeOf a ∈ J' then 1 else 0 with hcnt
  have hle : cnt ≤ J'.card * qOf g W := by
    calc cnt = ∑ a ∈ Finset.range (2 ^ W), ∑ v ∈ J', (if g.homeOf a = v then 1 else 0 : ℕ) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_ite_eq]
      _ = ∑ v ∈ J', ∑ a ∈ Finset.range (2 ^ W), (if g.homeOf a = v then 1 else 0 : ℕ) :=
          Finset.sum_comm
      _ ≤ ∑ v ∈ J', qOf g W := by
          gcongr with v _
          exact home_count_one g hr W hW v
      _ = J'.card * qOf g W := by rw [Finset.sum_const, smul_eq_mul]
  have hW' : 2 ^ W = 2 ^ g.k * 2 ^ (W - g.k) := by
    rw [← pow_add]; congr 1; omega
  have hPpos : (0 : ℝ) < (2 : ℝ) ^ g.k := by positivity
  have hTpos : (0 : ℝ) < (2 : ℝ) ^ (W - g.k) := by positivity
  have hrpos : (0 : ℝ) < (g.r : ℝ) := by exact_mod_cast hr
  have hWr : ((2 ^ W : ℕ) : ℝ) = (2 : ℝ) ^ g.k * (2 : ℝ) ^ (W - g.k) := by
    rw [hW']; push_cast; ring
  have hNr : (g.N : ℝ) = (g.r : ℝ) * (2 : ℝ) ^ g.k := by
    unfold SepGeom.N; push_cast; ring
  have key : (J'.card : ℝ) * (qOf g W : ℝ) / ((2 ^ W : ℕ) : ℝ) =
      J'.card * cbase g W / (g.N : ℝ) := by
    unfold cbase
    rw [hWr, hNr]
    push_cast
    field_simp
  have hcnt' : (cnt : ℝ) ≤ (J'.card : ℝ) * (qOf g W : ℝ) := by exact_mod_cast hle
  have hz' : 0 ≤ z - 1 := by linarith
  calc 1 + (z - 1) * (cnt : ℝ) / ((2 ^ W : ℕ) : ℝ)
      ≤ 1 + (z - 1) * ((J'.card : ℝ) * (qOf g W : ℝ)) / ((2 ^ W : ℕ) : ℝ) := by
        gcongr
    _ = 1 + (z - 1) * ((J'.card : ℝ) * (qOf g W : ℝ) / ((2 ^ W : ℕ) : ℝ)) := by ring
    _ = 1 + (z - 1) * J'.card * cbase g W / (g.N : ℝ) := by
        rw [key]; ring

/-- **The current-home MGF envelope** for a key set `K ⊆ KA ∪ KB` with at most `λ N` keys and a
count vector that is a product over its keys. -/
theorem home_mgf (hg : g.Valid) (hL : SInputLaw L lam D) (K : Finset Model.LogicalKey) (hK : K ⊆ L.KA ∪ L.KB)
    (hcard : (K.card : ℝ) ≤ lam * (g.N : ℝ))
    (X : L.Hist → (L.Key → Fin (2 ^ L.W)) → Fin g.N → ℕ)
    (hX : ∀ hist h (J : Finset (Fin g.N)) (z : ℝ), z ^ (∑ v ∈ J, X hist h v) =
      ∏ x ∈ K, (if g.homeOf (L.wordFn h x) ∈ J.map Fin.valEmbedding then z else 1))
    (J : Finset (Fin g.N)) (z : ℝ) (hz : 1 ≤ z) :
    ∑ hist, L.weight hist * ((Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h, ENNReal.ofReal (z ^ ∑ v ∈ J, X hist h v)) ≤
    ENNReal.ofReal (g.curDensity L.W K.card * Real.exp (lam * J.card * (z - 1))) := by
  have hr : 0 < g.r := hg.1
  have hkW : g.k ≤ L.W := hL.wide.le
  have hNpos : (0 : ℝ) < (g.N : ℝ) := by
    have : 0 < g.N := by unfold SepGeom.N; positivity
    exact_mod_cast this
  have h1 : ∀ hist : L.Hist, (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h, ENNReal.ofReal (z ^ ∑ v ∈ J, X hist h v) =
      ENNReal.ofReal (homePsi g L.W (J.map Fin.valEmbedding) z ^ K.card) := by
    intro hist
    rw [Finset.sum_congr rfl fun h _ => by rw [hX hist h J z]]
    rw [avg_wordFn_prod L K hK
      (fun _ a => if g.homeOf a ∈ J.map Fin.valEmbedding then z else 1)
      (by intro x a; split_ifs <;> linarith), Finset.prod_const]
    rfl
  rw [Finset.sum_congr rfl fun hist _ => by rw [h1 hist], ← Finset.sum_mul,
    hL.weight_sum, one_mul]
  apply ENNReal.ofReal_le_ofReal
  have hc : 0 ≤ (z - 1) * J.card := mul_nonneg (by linarith) (by positivity)
  have hb := one_le_cbase g hr L.W
  have hps := homePsi_le g hr L.W hkW (J.map Fin.valEmbedding) z hz
  rw [Finset.card_map] at hps
  rw [curDensity_eq, mul_comm]
  have hn : 0 ≤ (z - 1) * J.card / (g.N : ℝ) := by positivity
  calc homePsi g L.W (J.map Fin.valEmbedding) z ^ K.card
      ≤ (cbase g L.W * (1 + (z - 1) * J.card / (g.N : ℝ))) ^ K.card := by
        apply pow_le_pow_left₀ (homePsi_nonneg _ _ _ z hz)
        refine hps.trans ?_
        have : (z - 1) * (J.card : ℝ) * cbase g L.W / (g.N : ℝ) =
            cbase g L.W * ((z - 1) * J.card / (g.N : ℝ)) := by ring
        rw [this]
        nlinarith
    _ = cbase g L.W ^ K.card * (1 + (z - 1) * J.card / (g.N : ℝ)) ^ K.card := mul_pow _ _ _
    _ ≤ cbase g L.W ^ K.card * Real.exp (lam * ((z - 1) * J.card)) := by
        gcongr
        exact G1Proof.pow_le_exp _ _ _ _ hNpos hc hcard
    _ = _ := by ring_nf

end RebuildBound.SG1Proof
