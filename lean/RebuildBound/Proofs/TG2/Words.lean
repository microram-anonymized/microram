import RebuildBound.Proofs.TG2.Range
import RebuildBound.Spec.P12

/-!
# TG2 helpers: the words and the starting buckets

* `tavg_words`: the uniform average over the `W`-bit words on `KA` of a function of
  A's low `b` bits `h` and class bits `c` is
  `wordAvg (fun h => classAvg q (fun c => ·))` with `q_a = qMass W b 2 a`, which is
  `half` when `b < W` (`qMass_half`).
* `tdensity_bound`, `tavg_nodes`: the starting-bucket density factor `D` and the
  transport of the uniform average over buckets `Fin T` to starting nodes uniform
  on all `T = 2 · 2^b` nodes.
* `TCtx` from the contracts `TPLaw` (`tctx_of_TPLaw`).
-/

open scoped ENNReal NNReal unitInterval

namespace RebuildBound.TG2

open RebuildBound.Model RebuildBound.Spec RebuildBound.G2 RebuildBound.SG2

/-! ### Classes -/

theorem card_mod2 (m a : ℕ) (ha : a < 2) :
    ((Finset.range (2 * m)).filter (fun h => h % 2 = a)).card = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.card_filter] at ih ⊢
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : (2 * m + 1) % 2 = 1 := by omega
    rw [h1, h2]
    interval_cases a <;> simp

theorem qMass_half {W b : ℕ} (hb : b < W) (a : Fin 2) : qMass W b 2 a = half := by
  apply Subtype.ext
  show (qCount W b 2 a : ℝ) / 2 ^ (W - b) = 1 / 2
  have hW : 2 ^ (W - b) = 2 * 2 ^ (W - b - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hc : qCount W b 2 a = 2 ^ (W - b - 1) := by
    unfold qCount
    rw [hW, card_mod2 _ _ a.isLt]
  rw [hc]
  have : ((2 ^ (W - b) : ℕ) : ℝ) = 2 * 2 ^ (W - b - 1) := by exact_mod_cast hW
  push_cast
  rw [show (2 : ℝ) ^ (W - b) = 2 * 2 ^ (W - b - 1) by exact_mod_cast hW]
  field_simp

/-- **The average over the words** of a function of A's low bits and classes. -/
theorem tavg_words (KA : Finset Model.LogicalKey) {W b : ℕ} (hb : b ≤ W)
    (F : ({x // x ∈ KA} → Bits b) → ({x // x ∈ KA} → Fin 2) → ℝ≥0∞) :
    (Fintype.card ({x // x ∈ KA} → Fin (2 ^ W)) : ℝ≥0∞)⁻¹ *
        ∑ t : {x // x ∈ KA} → Fin (2 ^ W),
          F (fun x => (lowCls b 2 (by norm_num) W (t x)).1)
            (fun x => (lowCls b 2 (by norm_num) W (t x)).2) =
      wordAvg (fun h => classAvg (fun a : Fin 2 => qMass W b 2 a) (fun c => F h c)) := by
  have hr : 0 < 2 := by norm_num
  rw [sum_pi_map (lowCls b 2 hr W) (fun b' => F (fun x => (b' x).1) (fun x => (b' x).2))]
  rw [sum_arrow_prod]
  have hfib : ∀ (h : {x // x ∈ KA} → Bits b) (c : {x // x ∈ KA} → Fin 2),
      (∏ x, ((Finset.univ.filter (fun t => lowCls b 2 hr W t = (h x, c x))).card : ℝ≥0∞)) =
        ∏ x, (qCount W b 2 (c x) : ℝ≥0∞) := by
    intro h c
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [card_class_fiber hr hb]
  simp only [hfib]
  unfold wordAvg classAvg
  set n := Fintype.card {x // x ∈ KA}
  have hcA : (Fintype.card ({x // x ∈ KA} → Fin (2 ^ W)) : ℝ≥0∞) =
      ((2 : ℝ≥0∞) ^ b) ^ n * ((2 : ℝ≥0∞) ^ (W - b)) ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_pow, ← mul_pow, ← pow_add,
      Nat.add_sub_cancel' hb]
    simp [n]
  have hcB : (Fintype.card ({x // x ∈ KA} → Bits b) : ℝ≥0∞) = ((2 : ℝ≥0∞) ^ b) ^ n := by
    simp [n]
  have hq : ∀ c : {x // x ∈ KA} → Fin 2,
      (∏ x, ENNReal.ofReal ((qMass W b 2 (c x) : I) : ℝ)) =
        (∏ x, (qCount W b 2 (c x) : ℝ≥0∞)) * (((2 : ℝ≥0∞) ^ (W - b)) ^ n)⁻¹ := by
    intro c
    rw [Finset.prod_congr rfl (fun x _ => ofReal_qMass W b 2 (c x))]
    simp only [div_eq_mul_inv]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← ENNReal.inv_pow]
  simp only [hq]
  rw [hcA, hcB, ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp)), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-! ### Contexts from the contracts -/

theorem tctx_of_TPLaw {g : TPGeom} {L : TPJobLaw g} {lam D : ℝ≥0} (hL : TPLaw L lam D)
    (hist : L.Hist) :
    TCtx g (L.pos hist) L.KA (L.aIn hist).aMain (L.aIn hist).aTier := by
  have hs := hL.shape hist
  refine ⟨hs.aLen, hs.aLanes, hs.aNodup, hs.aHome, hL.aKeys hist, ?_⟩
  intro x hx
  rw [← hL.aKeys hist, List.mem_toFinset, List.mem_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  rcases List.mem_append.1 hr with h1 | h1
  · obtain ⟨B, hB, hrB⟩ := mem_flat.1 h1
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hB
    have hi' : i < g.T := hs.aLen ▸ hi
    have := hs.aHome i hi' r (by rw [List.getD_eq_getElem _ _ hi]; exact hrB)
    rw [this]; exact hi'
  · exact hs.tierHome r h1

/-! ### Old homes and starting nodes -/

/-- A's starting buckets of a history, as an element of `Fin T`. -/
def toh {g : TPGeom} (L : TPJobLaw g) (hpos : ∀ hist : L.Hist, ∀ x ∈ L.KA, L.pos hist x < g.T)
    (hist : L.Hist) : {x // x ∈ L.KA} → Fin g.T :=
  fun x => ⟨L.pos hist x.val, hpos hist x.val x.prop⟩

theorem tdensity_bound {g : TPGeom} {L : TPJobLaw g} {lam D : ℝ≥0} (hL : TPLaw L lam D)
    (hpos : ∀ hist : L.Hist, ∀ x ∈ L.KA, L.pos hist x < g.T)
    (G : ({x // x ∈ L.KA} → Fin g.T) → ℝ≥0∞) :
    ∑ hist, L.weight hist * G (toh L hpos hist) ≤
      (D : ℝ≥0∞) * ((Fintype.card ({x // x ∈ L.KA} → Fin g.T) : ℝ≥0∞)⁻¹ * ∑ o, G o) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (toh L hpos)
    (fun hist => L.weight hist * G (toh L hpos hist))]
  have hcard : (Fintype.card ({x // x ∈ L.KA} → Fin g.T) : ℝ≥0∞) =
      ((g.T : ℕ) : ℝ≥0∞) ^ L.KA.card := by
    simp
  rw [hcard, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o _
  have hfilt : ∀ hist ∈ Finset.univ.filter (fun hist => toh L hpos hist = o),
      L.weight hist * G (toh L hpos hist) = L.weight hist * G o := by
    intro hist hh
    rw [(Finset.mem_filter.1 hh).2]
  rw [Finset.sum_congr rfl hfilt, ← Finset.sum_mul]
  have hden := hL.density o
  have hset : (Finset.univ.filter (fun hist => toh L hpos hist = o)) =
      Finset.univ.filter (fun hist => ∀ x : L.KA, L.pos hist x = o x) := by
    ext hist
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, toh, funext_iff, Fin.ext_iff]
  rw [hset]
  calc (∑ hist ∈ Finset.univ.filter (fun hist => ∀ x : L.KA, L.pos hist x = o x),
        L.weight hist) * G o ≤
        ((D : ℝ≥0∞) / ((g.T : ℕ) : ℝ≥0∞) ^ L.KA.card) * G o := by
        gcongr
    _ = _ := by rw [div_eq_mul_inv]; ring

theorem allNodes_card (b : ℕ) : (Finset.univ : Finset (RNode 2 b)).card = 2 ^ (b + 1) := by
  rw [Finset.card_univ]
  simp [RNode, Bits, pow_succ, mul_comm]

/-- Starting buckets as elements of the set of all nodes. -/
noncomputable def tstartEquiv (b n : ℕ) (hn : n = 2 ^ (b + 1)) :
    Fin n ≃ (Finset.univ : Finset (RNode 2 b)) :=
  Equiv.ofBijective (fun i => ⟨tnode b i, Finset.mem_univ _⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun i j h => ?_, ?_⟩
    · exact Fin.ext (tnode_inj b (hn ▸ i.isLt) (hn ▸ j.isLt) (congrArg Subtype.val h))
    · rw [Fintype.card_coe, allNodes_card]; simp [hn])

theorem tavg_nodes (b n : ℕ) (hn : n = 2 ^ (b + 1)) {K : Type} [Fintype K] [DecidableEq K]
    (G : (K → RNode 2 b) → ℝ≥0∞) :
    (Fintype.card (K → Fin n) : ℝ≥0∞)⁻¹ *
        ∑ o : K → Fin n, G (fun x => tnode b (o x)) =
      uniformAvg (fun o : K → (Finset.univ : Finset (RNode 2 b)) =>
        G (fun x => (o x : RNode 2 b))) := by
  unfold uniformAvg
  set e := Equiv.arrowCongr (Equiv.refl K) (tstartEquiv b n hn)
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun o => rfl)

end RebuildBound.TG2
