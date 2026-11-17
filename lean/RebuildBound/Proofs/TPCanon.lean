import RebuildBound.Spec.Model.TopPrepCanonical
import RebuildBound.Proofs.Canon

/-!
# TPCanon: non-vacuity of `TPLaw` and `InitLaw`

`TPCanonical`: the canonical law (uniform old homes, `placeBy`) meets `TPLaw`
with `D = 1`; reuses the `placeBy` lemmas of `Canon.lean`.
`ICanonical`: `InitLaw` has no shape field, so it is the definitional unfolding
of the one-point law.
-/

namespace RebuildBound.TPCanonProof

open RebuildBound.Model RebuildBound.CanonLemmas
open scoped ENNReal NNReal

theorem canonOldS_lt' {n : ℕ} (hn : 0 < n) (KA : Finset Model.LogicalKey) (o : KA → Fin n) (x : Model.LogicalKey) :
    canonOldS KA o x < n := by
  unfold canonOldS
  split_ifs
  · exact (o _).2
  · exact hn

theorem canonOldS_mem' {n : ℕ} (KA : Finset Model.LogicalKey) (o : KA → Fin n) (x : KA) :
    canonOldS KA o x = o x := by
  simp [canonOldS, x.2]

end RebuildBound.TPCanonProof

open RebuildBound.Model RebuildBound.CanonLemmas RebuildBound.TPCanonProof in
open scoped ENNReal NNReal in
theorem RebuildBound.TPCanonical : RebuildBound.Model.TPCanonical_statement := by
  intro g KA W lam hW hA
  have hn : 0 < g.T := Nat.two_pow_pos _
  have hnpow : (((g.T : ℕ) : ℝ≥0∞) ^ KA.card) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hn.ne')
  have hntop : (((g.T : ℕ) : ℝ≥0∞) ^ KA.card) ≠ ∞ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  refine ⟨?_, ?_, ?_, hW, hA, ?_⟩
  · show ∑ _o : KA → Fin g.T, (((g.T : ℕ) : ℝ≥0∞) ^ KA.card)⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
    exact ENNReal.mul_inv_cancel hnpow hntop
  · intro o
    refine
      { aLen := length_fst _ _ _ _ _
        aLanes := lanes _ _ _ _ _
        aNodup := ?_
        aHome := ?_
        tierHome := ?_ }
    · exact (keys_perm g.C g.T (canonOldS KA o) 0 (KA.sort (· ≤ ·)) hn).nodup_iff.2
        (Finset.sort_nodup _ _)
    · intro i hi r hr
      have h1 := home g.C g.T (canonOldS KA o) 0 (KA.sort (· ≤ ·)) hi r hr
      rw [Nat.mod_eq_of_lt (canonOldS_lt' hn KA o _)] at h1
      exact h1
    · intro r _
      exact canonOldS_lt' hn KA o _
  · intro o
    exact (List.toFinset_eq_of_perm _ _
      (keys_perm g.C g.T (canonOldS KA o) 0 (KA.sort (· ≤ ·)) hn)).trans (Finset.sort_toFinset _ _)
  · intro o
    refine (Finset.sum_eq_single_of_mem o ?_ ?_).trans_le ?_
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x => canonOldS_mem' KA o x⟩
    · intro b hb hne
      refine absurd ?_ hne
      funext x
      have h3 := (Finset.mem_filter.1 hb).2 x
      have h2 := canonOldS_mem' KA b x
      exact Fin.ext (h2.symm.trans h3)
    show (((g.T : ℕ) : ℝ≥0∞) ^ KA.card)⁻¹ ≤ ((1 : ℝ≥0) : ℝ≥0∞) / ((g.T : ℕ) : ℝ≥0∞) ^ KA.card
    simp

open RebuildBound.Model in
open scoped ENNReal in
theorem RebuildBound.ICanonical : RebuildBound.Model.ICanonical_statement := by
  intro g input W hW hnd hlen
  refine ⟨?_, fun _ => rfl, hnd, rfl, hlen, hW⟩
  show ∑ _h : Unit, (1 : ℝ≥0∞) = 1
  simp
