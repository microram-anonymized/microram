import RebuildBound.Proofs.SG1.Mgf

/-!
# SG1: the probability terms (P3 applied to the three count vectors)
-/

open scoped ENNReal NNReal

namespace RebuildBound.SG1Proof

open RebuildBound.Model RebuildBound.Spec

variable {g : SepGeom} (L : SJobLaw g) {lam D : ℝ≥0}

/-- **The stage term.** -/
theorem stage_term (h3 : P3_statement) (hg : g.Valid) (hL : SInputLaw L lam D) (hlam : 0 < lam)
    (hC : (lam : ℝ) ≤ g.C) (j : ℕ) (hj : j < g.k) (S : ℕ) :
    L.prob (fun hist w => S < sRawStageExcess g (L.wOld hist) w (L.inputs hist w) j) ≤
      ENNReal.ofReal (Bsub g.N g.C lam S D) := by
  refine FiniteLawProof.prob_le_Bsub_of L.prob_eq h3 hL.weight_sum g.C S lam D
    (by exact_mod_cast hlam) hC D.2
    (stageX L j) (fun J z hz => stage_mgf L hg hL j hj J z hz) _ ?_
  intro hist h hS
  refine lt_of_lt_of_eq hS ?_
  unfold sRawStageExcess
  rw [G1Proof.list_sum_range, Finset.sum_range]
  rfl

/-- The home count vector of A's complete population. -/
def aHomeX (hist : L.Hist) (h : L.Key → Fin (2 ^ L.W)) (v : Fin g.N) : ℕ :=
  sHomeCount g (L.wordFn h) (L.inputs hist (L.wordFn h)).aAll v

theorem KA_card_le (hL : SInputLaw L lam D) : (L.KA.card : ℝ) ≤ lam * (g.N : ℝ) := by
  have hA : (L.KA.card : ℝ) ≤ lam * (((g.d - 1) * g.U : ℕ) : ℝ) := by exact_mod_cast hL.aLoad
  have hle : (((g.d - 1) * g.U : ℕ) : ℝ) ≤ (g.N : ℝ) := by
    rw [N_eq]; exact_mod_cast Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  exact hA.trans (mul_le_mul_of_nonneg_left hle lam.2)

/-- **The radix term.** -/
theorem radix_term (h3 : P3_statement) (hg : g.Valid) (hL : SInputLaw L lam D) (hlam : 0 < lam)
    (hC : (lam : ℝ) ≤ g.C) (S : ℕ) :
    L.prob (fun hist w => S < sAHomeExcess g w (L.inputs hist w)) ≤
      ENNReal.ofReal (Bsub g.N g.C lam S (g.curDensity L.W L.KA.card)) := by
  have hD : 0 ≤ g.curDensity L.W L.KA.card := by
    rw [curDensity_eq]; exact pow_nonneg (zero_le_one.trans (one_le_cbase g hg.1 _)) _
  refine FiniteLawProof.prob_le_Bsub_of L.prob_eq h3 hL.weight_sum g.C S lam _
    (by exact_mod_cast hlam) hC hD
    (aHomeX L) (fun J z hz => home_mgf L hg hL L.KA Finset.subset_union_left
      (KA_card_le L hL) (aHomeX L) ?_ J z hz) _ ?_
  · intro hist h J z
    have hv := hL.shape hist h
    unfold aHomeX sHomeCount sHome
    rw [G1Proof.pow_countP_sum z J (fun key => g.homeOf (L.wordFn h key)) _ hv.aNodup]
    have hk : (((L.inputs hist (L.wordFn h)).aAll).map Rec.key).toFinset = L.KA :=
      hL.aKeys hist
    rw [hk]
  · intro hist h hS
    refine lt_of_lt_of_eq hS ?_
    unfold sAHomeExcess sExcess
    rw [G1Proof.list_sum_range, Finset.sum_range]
    rfl

/-- The winners are distinct by key, with key set `A ∪ B`. -/
theorem winners_keys (inp : SInputs) (ha : (inp.aAll.map Rec.key).Nodup)
    (hb : (inp.bAll.map Rec.key).Nodup) :
    (inp.winners.map Rec.key).Nodup ∧
      (inp.winners.map Rec.key).toFinset =
        (inp.aAll.map Rec.key).toFinset ∪ (inp.bAll.map Rec.key).toFinset := by
  unfold SInputs.winners
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
def uHomeX (hist : L.Hist) (h : L.Key → Fin (2 ^ L.W)) (v : Fin g.N) : ℕ :=
  sHomeCount g (L.wordFn h) (L.inputs hist (L.wordFn h)).winners v

theorem KAB_card_le (hL : SInputLaw L lam D) (hg : g.Valid) :
    ((L.KA ∪ L.KB).card : ℝ) ≤ lam * (g.N : ℝ) := by
  have ha : (L.KA.card : ℝ) ≤ lam * (((g.d - 1) * g.U : ℕ) : ℝ) := by exact_mod_cast hL.aLoad
  have hb : (L.KB.card : ℝ) ≤ lam * (g.U : ℝ) := by exact_mod_cast hL.bLoad
  have hc : ((L.KA ∪ L.KB).card : ℝ) ≤ L.KA.card + L.KB.card := by
    exact_mod_cast Finset.card_union_le _ _
  have hd : 1 ≤ g.d := by have := hg.2.1; omega
  have hh : (g.N : ℝ) = (((g.d - 1) * g.U : ℕ) : ℝ) + (g.U : ℝ) := by
    rw [N_eq]
    have : g.d * g.U = (g.d - 1) * g.U + g.U := by
      obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hd
      rw [he]; simp [Nat.add_mul]; ring
    exact_mod_cast this
  rw [hh]
  linarith

/-- **The insertion and output-tier term.** -/
theorem union_term (h3 : P3_statement) (hg : g.Valid) (hL : SInputLaw L lam D) (hlam : 0 < lam)
    (hC : (lam : ℝ) ≤ g.C) (S : ℕ) :
    L.prob (fun hist w => S < sHomeExcess g w (L.inputs hist w)) ≤
      ENNReal.ofReal (Bsub g.N g.C lam S (g.curDensity L.W (L.KA ∪ L.KB).card)) := by
  have hD : 0 ≤ g.curDensity L.W (L.KA ∪ L.KB).card := by
    rw [curDensity_eq]; exact pow_nonneg (zero_le_one.trans (one_le_cbase g hg.1 _)) _
  refine FiniteLawProof.prob_le_Bsub_of L.prob_eq h3 hL.weight_sum g.C S lam _
    (by exact_mod_cast hlam) hC hD
    (uHomeX L) (fun J z hz => home_mgf L hg hL (L.KA ∪ L.KB) subset_rfl
      (KAB_card_le L hL hg) (uHomeX L) ?_ J z hz) _ ?_
  · intro hist h J z
    have hv := hL.shape hist h
    obtain ⟨hnd, hk⟩ := winners_keys _ hv.aNodup hv.bNodup
    unfold uHomeX sHomeCount sHome
    rw [G1Proof.pow_countP_sum z J (fun key => g.homeOf (L.wordFn h key)) _ hnd, hk]
    have ha : ((L.inputs hist (L.wordFn h)).aAll.map Rec.key).toFinset = L.KA := hL.aKeys hist
    have hb : ((L.inputs hist (L.wordFn h)).bAll.map Rec.key).toFinset = L.KB := hL.bKeys hist h
    rw [ha, hb]
  · intro hist h hS
    refine lt_of_lt_of_eq hS ?_
    unfold sHomeExcess sExcess
    rw [G1Proof.list_sum_range, Finset.sum_range]
    rfl

end RebuildBound.SG1Proof
