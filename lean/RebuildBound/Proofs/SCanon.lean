import RebuildBound.Spec.Model.SepCanonical
import RebuildBound.Proofs.Canon

/-!
# SCanon: the canonical law meets `SInputLaw` at every population size

`RebuildBound.SCanonical : SCanonical_statement`. Reuses the `placeBy` lemmas of
`Canon.lean`. New points: A's main has `n = (d - 1) U` buckets and the
previous digit's `oldHome` is the identity on `[0, n)`; B's tier is the list of
`bTierPages` pages whose first is `placeBy`'s tier and the others are empty.
`val2_dvd` is reproved here (a copy also lives in package SG1).
-/

namespace RebuildBound.SCanonProof

open RebuildBound.Model RebuildBound.CanonLemmas
open scoped ENNReal NNReal

theorem val2Aux_dvd : ∀ (fuel n : ℕ), 2 ^ (val2Aux fuel n) ∣ n
  | 0, n => by simp [val2Aux]
  | fuel + 1, n => by
    unfold val2Aux
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      obtain ⟨c, hc⟩ := val2Aux_dvd fuel (n / 2)
      refine ⟨c, ?_⟩
      have : n = 2 * (n / 2) := by omega
      rw [pow_succ]
      calc n = 2 * (n / 2) := this
        _ = 2 * (2 ^ val2Aux fuel (n / 2) * c) := by rw [← hc]
        _ = _ := by ring
    · simp

theorem val2_dvd (n : ℕ) : 2 ^ val2 n ∣ n := val2Aux_dvd n n

/-- The previous digit's map is the identity below `(d - 1) U`. -/
theorem oldHome_self (g : SepGeom) (_hd : 2 ≤ g.d) {t : ℕ} (ht : t < (g.d - 1) * g.U) :
    g.oldHome t = t := by
  unfold SepGeom.oldHome digitHome
  simp only
  obtain ⟨m, hm⟩ := val2_dvd (g.d - 1)
  generalize val2 (g.d - 1) = e at hm ⊢
  have hdm : (g.d - 1) / 2 ^ e = m := by
    rw [hm, Nat.mul_div_cancel_left _ (by positivity)]
  rw [hdm]
  have h3 : (g.d - 1) * g.U = 2 ^ (g.K + e) * m := by
    unfold SepGeom.U
    rw [pow_add, hm]; ring
  rw [h3] at ht
  set P := 2 ^ (g.K + e) with hP
  have hPpos : 0 < P := by positivity
  have h4 : t / P < m := (Nat.div_lt_iff_lt_mul hPpos).2 (by rw [mul_comm]; exact ht)
  rw [Nat.mod_eq_of_lt h4]
  exact Nat.mod_add_div t P

theorem canonOldS_lt {n : ℕ} (hn : 0 < n) (KA : Finset Model.LogicalKey) (o : KA → Fin n) (x : Model.LogicalKey) :
    canonOldS KA o x < n := by
  unfold canonOldS
  split_ifs
  · exact (o _).2
  · exact hn

theorem canonOldS_mem {n : ℕ} (KA : Finset Model.LogicalKey) (o : KA → Fin n) (x : KA) :
    canonOldS KA o x = o x := by
  simp [canonOldS, x.2]

theorem oldHome_canon (g : SepGeom) (hd : 2 ≤ g.d) (KA : Finset Model.LogicalKey)
    (o : KA → Fin ((g.d - 1) * g.U)) (x : KA) : g.oldHome (canonOldS KA o x) = o x := by
  rw [canonOldS_mem, oldHome_self g hd (o x).2]

end RebuildBound.SCanonProof

open RebuildBound.Model RebuildBound.CanonLemmas RebuildBound.SCanonProof in
open scoped ENNReal NNReal in
theorem RebuildBound.SCanonical : RebuildBound.Model.SCanonical_statement := by
  intro g KA KB W lam hV hB hW hA hBl
  have hd : 2 ≤ g.d := hV.2.1
  have hU : 0 < g.U := Nat.two_pow_pos _
  have hn : 0 < (g.d - 1) * g.U := Nat.mul_pos (by omega) hU
  have hnpow : ((((g.d - 1) * g.U : ℕ) : ℝ≥0∞) ^ KA.card) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hn.ne')
  have hntop : ((((g.d - 1) * g.U : ℕ) : ℝ≥0∞) ^ KA.card) ≠ ∞ :=
    ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  refine ⟨?_, ?_, ?_, ?_, hW, hA, hBl, ?_⟩
  · show ∑ _o : KA → Fin ((g.d - 1) * g.U),
      ((((g.d - 1) * g.U : ℕ) : ℝ≥0∞) ^ KA.card)⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
    exact ENNReal.mul_inv_cancel hnpow hntop
  · intro o h
    have hfl : ∀ m : ℕ, ∀ l : List Rec, (l :: List.replicate m ([] : List Rec)).flatten = l := by
      intro m l; simp
    refine
      { aLen := length_fst _ _ _ _ _
        aLanes := lanes _ _ _ _ _
        bLen := length_fst _ _ _ _ _
        bLanes := lanes _ _ _ _ _
        bPages := ?_
        aNodup := ?_
        bNodup := ?_
        aHome := ?_
        bHome := ?_ }
    · show (_ :: List.replicate (g.bTierPages - 1) ([] : List Rec)).length = g.bTierPages
      simp; omega
    · exact (keys_perm g.C _ (canonOldS KA o) 0 (KA.sort (· ≤ ·)) hn).nodup_iff.2
        (Finset.sort_nodup _ _)
    · show ((_ ++ (_ :: List.replicate (g.bTierPages - 1) ([] : List Rec)).flatten).map Rec.key).Nodup
      rw [hfl]
      exact (keys_perm g.C g.U (SJobLaw.wordFn (canonicalSepLaw g KA KB W) h) 1 (KB.sort (· ≤ ·)) hU).nodup_iff.2
        (Finset.sort_nodup _ _)
    · intro i hi x hx
      have h1 := home g.C _ (canonOldS KA o) 0 (KA.sort (· ≤ ·)) hi x hx
      rw [Nat.mod_eq_of_lt (canonOldS_lt hn KA o _)] at h1
      show g.oldHome (canonOldS KA o x.key) = i
      rw [h1]; exact oldHome_self g hd (h1 ▸ hi)
    · intro i hi x hx
      exact home g.C g.U _ 1 (KB.sort (· ≤ ·)) hi x hx
  · intro o
    exact (List.toFinset_eq_of_perm _ _
      (keys_perm g.C _ (canonOldS KA o) 0 (KA.sort (· ≤ ·)) hn)).trans (Finset.sort_toFinset _ _)
  · intro o h
    have hfl : ∀ m : ℕ, ∀ l : List Rec, (l :: List.replicate m ([] : List Rec)).flatten = l := by
      intro m l; simp
    show ((_ ++ (_ :: List.replicate (g.bTierPages - 1) ([] : List Rec)).flatten).map Rec.key).toFinset = KB
    rw [hfl]
    exact (List.toFinset_eq_of_perm _ _
      (keys_perm g.C g.U _ 1 (KB.sort (· ≤ ·)) hU)).trans (Finset.sort_toFinset _ _)
  · intro o
    refine (Finset.sum_eq_single_of_mem o ?_ ?_).trans_le ?_
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x => oldHome_canon g hd KA o x⟩
    · intro b hb hne
      refine absurd ?_ hne
      funext x
      have h3 := (Finset.mem_filter.1 hb).2 x
      have h2 := oldHome_canon g hd KA b x
      exact Fin.ext ((congrArg Fin.val (Fin.ext (h2.symm.trans h3))))
    show ((((g.d - 1) * g.U : ℕ) : ℝ≥0∞) ^ KA.card)⁻¹ ≤
      ((1 : ℝ≥0) : ℝ≥0∞) / (((g.d - 1) * g.U : ℕ) : ℝ≥0∞) ^ KA.card
    simp
