import RebuildBound.Proofs.G1.MGF

/-!
# G1: the insertion and output-tier term

The complete union's home counts `X_v = homeCount (winners) v`: the winners are
one record per key of `KA ∪ KB`, each key's home `w mod 2U` is uniform and
independent across keys, and `|KA ∪ KB| ≤ 2 λ U`; so the subset MGF envelope
holds with factor `1` and P3 bounds the home excess.
-/

open scoped ENNReal NNReal

namespace RebuildBound.G1Proof

open RebuildBound.Model RebuildBound.Spec

variable {g : Geom} (L : JobLaw g)

/-- The winners are distinct by key, with key set `A ∪ B`. -/
theorem winners_keys (inp : Inputs) (ha : (inp.aAll.map Rec.key).Nodup)
    (hb : (inp.bAll.map Rec.key).Nodup) :
    (inp.winners.map Rec.key).Nodup ∧
      (inp.winners.map Rec.key).toFinset =
        (inp.aAll.map Rec.key).toFinset ∪ (inp.bAll.map Rec.key).toFinset := by
  unfold Inputs.winners
  constructor
  · rw [List.map_append, List.nodup_append]
    refine ⟨hb, ((List.filter_sublist).map _).nodup ha, ?_⟩
    intro a ha' b hb' hab
    subst hab
    simp only [List.mem_map, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hb'
    obtain ⟨r, ⟨_, hc⟩, rfl⟩ := hb'
    exact hc (List.mem_map.mp ha')
  · ext x
    simp only [List.map_append, List.toFinset_append, Finset.mem_union, List.mem_toFinset,
      List.mem_map, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not]
    constructor
    · rintro (h | ⟨r, ⟨hr, _⟩, rfl⟩)
      · exact Or.inr h
      · exact Or.inl ⟨r, hr, rfl⟩
    · rintro (⟨r, hr, rfl⟩ | h)
      · by_cases hb' : r.key ∈ inp.bAll.map Rec.key
        · exact Or.inl (List.mem_map.mp hb')
        · exact Or.inr ⟨r, ⟨hr, fun h => hb' (List.mem_map.mpr h)⟩, rfl⟩
      · exact Or.inl h

/-- The home count vector of the complete union. -/
def homeX (hist : L.Hist) (h : L.Key → Fin (2 ^ L.W)) (v : Fin g.homes) : ℕ :=
  homeCount g (L.wordFn h) (L.inputs hist (L.wordFn h)).winners v

variable {TA TB : ℕ} {lam D : ℝ≥0}

theorem home_pow (hL : InputLaw L lam D) (hist : L.Hist)
    (h : L.Key → Fin (2 ^ L.W)) (J : Finset (Fin g.homes)) (z : ℝ) :
    z ^ (∑ v ∈ J, homeX L hist h v) =
      ∏ x ∈ L.KA ∪ L.KB, (if L.wordFn h x % g.homes ∈ J.map Fin.valEmbedding then z else 1) := by
  have hv := hL.shape hist h
  obtain ⟨hnd, hk⟩ := winners_keys _ hv.aNodup hv.bNodup
  unfold homeX homeCount home
  rw [pow_countP_sum z J (fun x => L.wordFn h x % g.homes) _ hnd, hk]
  have ha : ((L.inputs hist (L.wordFn h)).aAll.map Rec.key).toFinset = L.KA := hL.aKeys hist
  have hb : ((L.inputs hist (L.wordFn h)).bAll.map Rec.key).toFinset = L.KB := hL.bKeys hist h
  rw [ha, hb]

/-- The per-key average of `z^[home ∈ J]`. -/
noncomputable def homePsi (W n : ℕ) (J' : Finset ℕ) (z : ℝ) : ℝ :=
  ((2 ^ W : ℕ) : ℝ)⁻¹ * ∑ a : Fin (2 ^ W), (if (a : ℕ) % n ∈ J' then z else 1)

theorem homePsi_nonneg (W n : ℕ) (J' : Finset ℕ) (z : ℝ) (hz : 1 ≤ z) :
    0 ≤ homePsi W n J' z := by
  unfold homePsi
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => ?_)
  split_ifs <;> linarith

theorem homePsi_le (W k : ℕ) (hk : k + 1 ≤ W) (J' : Finset ℕ) (z : ℝ) (hz : 1 ≤ z) :
    homePsi W (2 ^ (k + 1)) J' z ≤ 1 + (z - 1) * J'.card / ((2 ^ (k + 1) : ℕ) : ℝ) := by
  have hm : 0 < 2 ^ (k + 1) := by positivity
  have hW : 2 ^ W = 2 ^ (k + 1) * 2 ^ (W - (k + 1)) := by
    rw [← pow_add]; congr 1; omega
  have hWr : (0 : ℝ) < ((2 ^ W : ℕ) : ℝ) := by positivity
  have hmr : (0 : ℝ) < ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hm
  unfold homePsi
  rw [avg_ite (2 ^ W) (by positivity) (fun a => a % 2 ^ (k + 1) ∈ J') z]
  set N := ∑ a ∈ Finset.range (2 ^ W), if a % 2 ^ (k + 1) ∈ J' then 1 else 0
  have hN : N * 2 ^ (k + 1) ≤ J'.card * 2 ^ W := by
    have := home_count (2 ^ (k + 1)) (2 ^ (W - (k + 1))) hm J'
    rw [← hW] at this
    calc N * 2 ^ (k + 1) ≤ J'.card * 2 ^ (W - (k + 1)) * 2 ^ (k + 1) := by gcongr
      _ = J'.card * 2 ^ W := by rw [hW]; ring
  have hN' : (N : ℝ) / ((2 ^ W : ℕ) : ℝ) ≤ J'.card / ((2 ^ (k + 1) : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hWr hmr]
    exact_mod_cast hN
  rw [mul_div_assoc, mul_div_assoc]
  gcongr

theorem home_hist (hL : InputLaw L lam D) (hist : L.Hist)
    (J : Finset (Fin g.homes)) (z : ℝ) (hz : 1 ≤ z) :
    (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h, ENNReal.ofReal (z ^ ∑ v ∈ J, homeX L hist h v) =
    ENNReal.ofReal (homePsi L.W g.homes (J.map Fin.valEmbedding) z ^ (L.KA ∪ L.KB).card) := by
  rw [Finset.sum_congr rfl fun h _ => by rw [home_pow L hL hist h J z]]
  rw [avg_wordFn_prod L (L.KA ∪ L.KB) subset_rfl
    (fun _ a => if a % g.homes ∈ J.map Fin.valEmbedding then z else 1)
    (by intro x a; split_ifs <;> linarith), Finset.prod_const]
  rfl

/-- **The home MGF envelope** (factor `1`). -/
theorem home_mgf (hL : InputLaw L lam D) (J : Finset (Fin g.homes)) (z : ℝ) (hz : 1 ≤ z) :
    ∑ hist, L.weight hist * ((Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h, ENNReal.ofReal (z ^ ∑ v ∈ J, homeX L hist h v)) ≤
    ENNReal.ofReal (1 * Real.exp (lam * J.card * (z - 1))) := by
  have hkW : g.k + 1 ≤ L.W := hL.wide
  rw [Finset.sum_congr rfl fun hist _ => by rw [home_hist L hL hist J z hz], ← Finset.sum_mul,
    hL.weight_sum, one_mul, one_mul]
  apply ENNReal.ofReal_le_ofReal
  have hU : 0 < g.U := U_pos g
  have hH : (0 : ℝ) < ((2 ^ (g.k + 1) : ℕ) : ℝ) := by positivity
  have hload : ((L.KA ∪ L.KB).card : ℝ) ≤ lam * ((2 ^ (g.k + 1) : ℕ) : ℝ) := by
    have ha := NNReal.coe_le_coe.mpr hL.aLoad
    have hb := NNReal.coe_le_coe.mpr hL.bLoad
    push_cast at ha hb
    have hc : ((L.KA ∪ L.KB).card : ℝ) ≤ L.KA.card + L.KB.card := by
      exact_mod_cast Finset.card_union_le _ _
    have hh : ((2 ^ (g.k + 1) : ℕ) : ℝ) = 2 * (g.U : ℝ) := by
      unfold Geom.U; push_cast; ring
    rw [hh]
    linarith
  have hc : 0 ≤ (z - 1) * J.card := mul_nonneg (by linarith) (by positivity)
  calc homePsi L.W g.homes (J.map Fin.valEmbedding) z ^ (L.KA ∪ L.KB).card
      ≤ (1 + (z - 1) * J.card / ((2 ^ (g.k + 1) : ℕ) : ℝ)) ^ (L.KA ∪ L.KB).card := by
        apply pow_le_pow_left₀ (homePsi_nonneg _ _ _ z hz)
        have := homePsi_le L.W g.k hkW (J.map Fin.valEmbedding) z hz
        rwa [Finset.card_map] at this
    _ ≤ Real.exp (lam * ((z - 1) * J.card)) := pow_le_exp _ _ _ _ hH hc hload
    _ = Real.exp (lam * J.card * (z - 1)) := by ring_nf

/-- **The insertion and output-tier term.** -/
theorem home_term (h3 : P3_statement) (hL : InputLaw L lam D) (hlam : 0 < lam)
    (hC : (lam : ℝ) ≤ g.C) (S : ℕ) :
    L.prob (fun hist w => S < homeExcess g w (L.inputs hist w)) ≤
      ENNReal.ofReal (Bsub g.homes g.C lam S 1) := by
  refine FiniteLawProof.prob_le_Bsub_of L.prob_eq h3 hL.weight_sum g.C S lam 1
    (by exact_mod_cast hlam) hC zero_le_one (homeX L) (fun J z hz => home_mgf L hL J z hz) _ ?_
  intro hist h hS
  refine lt_of_lt_of_eq hS ?_
  unfold homeExcess
  rw [list_sum_range, Finset.sum_range]
  rfl

end RebuildBound.G1Proof
