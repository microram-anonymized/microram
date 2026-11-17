import RebuildBound.Proofs.G3.Point
import RebuildBound.Spec.TopT
import RebuildBound.Proofs.P7fin
import RebuildBound.Proofs.P8a

/-!
# G3: the top finish's first-failure bound, from T4top

`G3_of`: T4top gives, on a failure with the tiers fitting, a range event or a merge/tier
event; both are stop-loss events of the home counts of fixed key sets (A's keys, and the
live set's keys), whose words are independent and uniform. P8a replaces the home counts
by Poisson counts and P7 bounds the stop-loss.

No obstacle: the measure-based API plus P11d's `bridge` sufficed.
-/

open scoped ENNReal NNReal

namespace RebuildBound.G3Proof

open RebuildBound.Model RebuildBound.Spec

theorem Phi_nonneg (K n C : ℕ) {lam : ℝ} (hl : 0 ≤ lam) (S : ℕ) : 0 ≤ Phi K n C lam S := by
  unfold Phi
  refine add_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (by positivity)
    (seriesCoeff_nonneg n C hl k)) ?_
  positivity

/-- P8a then P7 for the home counts of a fixed key set. -/
theorem avg_bound {g : TopGeom} (L : TopJobLaw g) {m : ℕ} (hm : m ≤ L.W) (K : Finset Model.LogicalKey)
    (hK : K ⊆ L.KA ∪ L.KB) (lam : ℝ≥0) (hload : (K.card : ℝ≥0) ≤ lam * 2 ^ m)
    (J : Finset (Fin (2 ^ m))) (C S K' : ℕ) (hS : S < K') :
    (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h : L.Key → Fin (2 ^ L.W), restrictedStopLoss J C S (cntK m K (L.wordFn h)) ≤
    ENNReal.ofReal (Phi K' J.card C lam S) := by
  unfold cntK
  rw [avg_cnt L hm K hK (restrictedStopLoss J C S)]
  have h8 := RebuildBound.P8a J C S (1 / 2 ^ m) lam
    (List.replicate K.card (fun _ : Fin (2 ^ m) => (1 / 2 ^ m : ℝ≥0))) ?_ ?_ ?_
  · rw [List.map_replicate] at h8
    exact le_trans h8 (RebuildBound.P7 J C S K' lam hS)
  · intro p hp
    rw [List.eq_of_mem_replicate hp]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat]
    field_simp
  · intro p hp v
    rw [List.eq_of_mem_replicate hp]
  · simp only [List.length_replicate]
    calc (K.card : ℝ≥0) * (1 / 2 ^ m) ≤ lam * 2 ^ m * (1 / 2 ^ m) := by gcongr
      _ = lam := by field_simp

/-- Coarse range `r` as a set of homes. -/
def Jr (m I r : ℕ) (hle : (r + 1) * 2 ^ I ≤ 2 ^ m) : Finset (Fin (2 ^ m)) :=
  (Finset.univ : Finset (Fin (2 ^ I))).map
    ⟨fun i => ⟨r * 2 ^ I + i.1, by
        have := i.2
        have h2 : (r + 1) * 2 ^ I = r * 2 ^ I + 2 ^ I := by ring
        omega⟩,
      fun a b h => by simpa [Fin.ext_iff] using h⟩

theorem card_Jr (m I r : ℕ) (hle : (r + 1) * 2 ^ I ≤ 2 ^ m) : (Jr m I r hle).card = 2 ^ I := by
  simp [Jr]

theorem rangeExcessA_eq (g : TopGeom) (w : Model.LogicalKey → ℕ) (inp : TopInputs) (KA : Finset Model.LogicalKey) (r : ℕ)
    (hle : (r + 1) * 2 ^ g.I ≤ 2 ^ (g.k + g.e))
    (hc : ∀ v, topCount g w inp.aAll v =
      (KA.filter fun x => w x % 2 ^ (g.k + g.e) = v).card) :
    rangeExcessA g w inp r =
      ∑ v ∈ Jr (g.k + g.e) g.I r hle, (cntK (g.k + g.e) KA w v - g.C) := by
  unfold rangeExcessA Jr
  rw [G1Proof.list_sum_range, Finset.sum_range, Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [cntK]
  rw [hc]
  rfl

theorem topExcess_eq (g : TopGeom) (w : Model.LogicalKey → ℕ) (inp : TopInputs) (KL : Finset Model.LogicalKey)
    (hc : ∀ v, topCount g w inp.live v =
      (KL.filter fun x => w x % 2 ^ (g.k + g.e) = v).card) :
    topExcess g w inp = ∑ v ∈ (Finset.univ : Finset (Fin (2 ^ (g.k + g.e)))),
      (cntK (g.k + g.e) KL w v - g.C) := by
  unfold topExcess
  rw [G1Proof.list_sum_range]
  have hT : g.T = 2 ^ (g.k + g.e) := rfl
  rw [hT, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [cntK]
  rw [hc]

end RebuildBound.G3Proof

open RebuildBound.Model RebuildBound.Spec RebuildBound.G3Proof in
theorem RebuildBound.G3_of (h4 : RebuildBound.Spec.T4top_statement) :
    RebuildBound.Spec.G3_statement := by
  intro g L unsh lam K1 K2 hL hv hC hK2
  have hw := hL.weight_sum
  have hm : g.k + g.e ≤ L.W := hL.wide
  have hT : g.T = 2 ^ (g.k + g.e) := rfl
  let KL : Finset Model.LogicalKey := (liveSet L.RA L.RB).image Rec.key
  have hKAsub : L.KA ⊆ L.KA ∪ L.KB := Finset.subset_union_left
  have hKLsub : KL ⊆ L.KA ∪ L.KB := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    simp only [liveSet, Finset.mem_filter, Finset.mem_union] at hr
    rcases hr.1 with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h.1)
  have hloadA : (L.KA.card : ℝ≥0) ≤ lam * 2 ^ (g.k + g.e) := by
    have h1 : L.KA.card ≤ L.RA.card := Finset.card_image_le
    have := hL.aLoad
    rw [hT] at this
    push_cast at this
    exact le_trans (by exact_mod_cast h1) this
  have hloadL : (KL.card : ℝ≥0) ≤ lam * 2 ^ (g.k + g.e) := by
    have h1 : KL.card ≤ (liveSet L.RA L.RB).card := Finset.card_image_le
    have := hL.wLoad
    rw [hT] at this
    push_cast at this
    exact le_trans (by exact_mod_cast h1) this
  -- the counts at every outcome
  have hcA : ∀ hist h v, topCount g (L.wordFn h) (L.inputs hist (L.wordFn h)).aAll v =
      (L.KA.filter fun x => L.wordFn h x % 2 ^ (g.k + g.e) = v).card := by
    intro hist h v
    rw [topCount_eq g _ _ (hL.shape hist h).aNodup, map_key_toFinset, hL.aRecs hist h]
    rfl
  have hcL : ∀ hist h v, topCount g (L.wordFn h) (L.inputs hist (L.wordFn h)).live v =
      (KL.filter fun x => L.wordFn h x % 2 ^ (g.k + g.e) = v).card := by
    intro hist h v
    rw [topCount_eq g _ _ (live_keys _ (hL.shape hist h).aNodup (hL.shape hist h).bNodup),
      map_key_toFinset, live_toFinset _ _ _ (hL.aRecs hist h) (hL.bRecs hist h)]
  -- the range events
  have hrange : ∀ r < g.ranges,
      L.prob (fun hist w => g.C < rangeExcessA g w (L.inputs hist w) r) ≤
        ENNReal.ofReal (Phi K1 (2 ^ g.I) g.C lam g.C) := by
    intro r hr
    have hle : (r + 1) * 2 ^ g.I ≤ 2 ^ (g.k + g.e) := by
      have : (r + 1) * 2 ^ g.I ≤ 2 ^ g.rho * 2 ^ g.I :=
        Nat.mul_le_mul_right _ (by unfold TopGeom.ranges at hr; omega)
      rw [← pow_add, hv.2.1] at this
      exact this
    refine le_trans (FiniteLawProof.prob_le_avg_of L.prob_eq hw _
      (fun h => restrictedStopLoss (Jr (g.k + g.e) g.I r hle) g.C g.C
        (cntK (g.k + g.e) L.KA (L.wordFn h))) ?_) ?_
    · intro hist h hE
      rw [rangeExcessA_eq g _ _ L.KA r hle (hcA hist h)] at hE
      unfold restrictedStopLoss
      exact Nat.one_le_cast.mpr (by omega)
    · have := avg_bound L hm L.KA hKAsub lam hloadA (Jr (g.k + g.e) g.I r hle) g.C g.C K1 hC
      rwa [card_Jr] at this
  -- the merge/tier event
  have hfin : L.prob (fun hist w => min g.SMerge g.STier < topExcess g w (L.inputs hist w)) ≤
      ENNReal.ofReal (Phi K2 g.T g.C lam (min g.SMerge g.STier)) := by
    refine le_trans (FiniteLawProof.prob_le_avg_of L.prob_eq hw _
      (fun h => restrictedStopLoss (Finset.univ : Finset (Fin (2 ^ (g.k + g.e)))) g.C
        (min g.SMerge g.STier) (cntK (g.k + g.e) KL (L.wordFn h))) ?_) ?_
    · intro hist h hE
      rw [topExcess_eq g _ _ KL (hcL hist h)] at hE
      unfold restrictedStopLoss
      exact Nat.one_le_cast.mpr (by omega)
    · have := avg_bound L hm KL hKLsub lam hloadL Finset.univ g.C (min g.SMerge g.STier) K2 hK2
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact this
  -- first failure
  have hpt : ∀ hist hh, topFailEvent L unsh hist (L.wordFn hh) →
      ((g.C < g.SR ∧ ∃ r < g.ranges, g.C < rangeExcessA g (L.wordFn hh) (L.inputs hist (L.wordFn hh)) r) ∨
        min g.SMerge g.STier < topExcess g (L.wordFn hh) (L.inputs hist (L.wordFn hh))) := by
    intro hist hh ⟨hfit, hfail⟩
    cases hj : topJob g unsh (L.wordFn hh) (L.inputs hist (L.wordFn hh)) with
    | ok o => rw [hj] at hfail; simp [Except.toBool] at hfail
    | error t =>
      have := h4 g unsh _ _ t hv (hL.shape hist hh) hfit hj
      cases t with
      | dfs a b => exact Or.inl this
      | stash b => exact Or.inr this
      | insertion => exact Or.inr this
      | drain => exact Or.inr this
  have h1 := FiniteLawProof.prob_mono_of L.prob_eq (E := topFailEvent L unsh)
    (F := fun hist w => (g.C < g.SR ∧ ∃ r < g.ranges, g.C < rangeExcessA g w (L.inputs hist w) r) ∨
        min g.SMerge g.STier < topExcess g w (L.inputs hist w)) hpt
  refine le_trans h1 (le_trans (FiniteLawProof.prob_or_of L.prob_eq _ _) ?_)
  have hP1 := Phi_nonneg K1 (2 ^ g.I) g.C (lam := (lam : ℝ)) lam.2 g.C
  have hP2 := Phi_nonneg K2 g.T g.C (lam := (lam : ℝ)) lam.2 (min g.SMerge g.STier)
  unfold topFinishBound
  by_cases hSR : g.C < g.SR
  · rw [if_pos hSR, ENNReal.ofReal_add (by positivity) hP2, ENNReal.ofReal_mul (by positivity)]
    gcongr
    · refine le_trans (FiniteLawProof.prob_mono_of L.prob_eq
        (E := fun hist w => g.C < g.SR ∧ ∃ r < g.ranges,
        g.C < rangeExcessA g w (L.inputs hist w) r)
        (F := fun hist w => ∃ r < g.ranges, g.C < rangeExcessA g w (L.inputs hist w) r)
        (fun _ _ h => h.2)) ?_
      refine le_trans (FiniteLawProof.prob_exists_lt_of L.prob_eq g.ranges _) ?_
      refine le_trans (Finset.sum_le_sum fun r hr => hrange r (Finset.mem_range.mp hr)) ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have : ENNReal.ofReal ((2 : ℝ) ^ g.rho) = (g.ranges : ℝ≥0∞) := by
        unfold TopGeom.ranges
        rw [ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [this]
  · rw [if_neg hSR, zero_add]
    have h0 : L.prob (fun hist w => g.C < g.SR ∧ ∃ r < g.ranges,
        g.C < rangeExcessA g w (L.inputs hist w) r) ≤ 0 := by
      rw [← FiniteLawProof.prob_false_of L.prob_eq]
      exact FiniteLawProof.prob_mono_of L.prob_eq fun _ _ h => absurd h.1 hSR
    calc _ ≤ 0 + L.prob (fun hist w => min g.SMerge g.STier < topExcess g w (L.inputs hist w)) := by
          gcongr
      _ ≤ _ := by rw [zero_add]; exact hfin

