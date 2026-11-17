import RebuildBound.Proofs.SG1p.Main

/-!
# SG1p: the separated job's first failure, every term `min(B_sub, D Φ_K)`

`RebuildBound.SG1p_of : ST4a → ST4b → ST6 → SEngine → SG1p_statement`.

**Proof.** The failure inventory, the union bound and the old-home density grouping are the
SG1 package's lemmas (`SG1Proof.fail_cases`, `prob_or`, `prob_exists_lt`). Each of the four
terms has two bounds. The first is `B_sub` (P3, `SG1Proof`'s stage and home terms). The
second (`SG1pProof.gen_bound`) is the integer bound
`P(S < X) ≤ E (X - S)₊`, the density step on the old homes (the destination of a key is a
fixed map of (old home, word), so under the uniform law the counts are a sum of independent
unit vectors), P8a to independent `Po(λ)` counts and P7 for `Φ_K`. The current-home law has
masses at most `cbase / N`, so it is compared with the uniform law at cost `cbase^|K| =
curDensity` (`conv_compare`). `P(E) ≤ min a b` and `ENNReal.ofReal_min` give the witness.

**Probability obstacles.** None: `SJobLaw.prob` is a finite
`ℝ≥0∞` sum; the measure API (`convList`, `unitLaw`, `poissonVec`) is used through P11d's
`bridge` and P8a, P7.
-/

open scoped ENNReal NNReal

open RebuildBound.Model RebuildBound.Spec in
/-- **SG1p, conditional on ST4a, ST4b, ST6 and SEngine.** -/
theorem RebuildBound.SG1p_of (h4a : RebuildBound.Spec.ST4a_statement)
    (h4b : RebuildBound.Spec.ST4b_statement) (h6 : RebuildBound.Spec.ST6_statement)
    (he : RebuildBound.Spec.SEngine_statement) : RebuildBound.Spec.SG1p_statement := by
  have h3 := RebuildBound.P3
  intro g L lam D rule aRange K1 K2 hg hL hrule hlam hlamC hK1 hK2 hrange
  set S := g.stashPages * g.C with hS
  have hwit : ∀ (E : L.Hist → (Model.LogicalKey → ℕ) → Prop) (S' K' : ℕ) (D' : ℝ) (hD' : 0 ≤ D'),
      L.prob E ≤ ENNReal.ofReal (Bsub g.N g.C lam S' D') →
      L.prob E ≤ ENNReal.ofReal (D' * Phi K' g.N g.C lam S') →
      L.prob E ≤ ENNReal.ofReal (witness g.N g.C lam S' K' D') := by
    intro E S' K' D' _ h1 h2
    unfold witness
    rw [ENNReal.ofReal_min]
    exact le_min h1 h2
  have hcur : ∀ n, 0 ≤ g.curDensity L.W n := fun n => by
    rw [SG1Proof.curDensity_eq]
    exact pow_nonneg (zero_le_one.trans (SG1Proof.one_le_cbase g hg.1 _)) _
  calc L.prob (fun hist w =>
        STiersFit g (L.inputs hist w) ∧ (sJob rule g w (L.inputs hist w)).toBool = false)
      ≤ L.prob (fun hist w =>
          (((∃ j < g.k, S < sRawStageExcess g (L.wOld hist) w (L.inputs hist w) j) ∨
              (1 < g.r ∧ S < sAHomeExcess g w (L.inputs hist w))) ∨
            sRangeEvent g L rule hist w) ∨
          min S (g.tierPages * g.C) < sHomeExcess g w (L.inputs hist w)) :=
        SG1Proof.prob_mono L fun hist h hf =>
          SG1Proof.fail_cases h4a h4b h6 he rule g (L.wOld hist) (L.wordFn h) _ hrule hg
            (hL.shape hist h) hf.1 hf.2
    _ ≤ ((L.prob (fun hist w =>
            ∃ j < g.k, S < sRawStageExcess g (L.wOld hist) w (L.inputs hist w) j) +
          L.prob (fun hist w => 1 < g.r ∧ S < sAHomeExcess g w (L.inputs hist w))) +
          L.prob (sRangeEvent g L rule)) +
          L.prob (fun hist w => min S (g.tierPages * g.C) < sHomeExcess g w (L.inputs hist w)) := by
        refine le_trans (SG1Proof.prob_or L _ _) ?_
        gcongr
        refine le_trans (SG1Proof.prob_or L _ _) ?_
        gcongr
        exact SG1Proof.prob_or L _ _
    _ ≤ _ := by
        gcongr
        · refine le_trans (SG1Proof.prob_exists_lt L _ _) ?_
          calc _ ≤ ∑ j ∈ Finset.range g.k, ENNReal.ofReal (witness g.N g.C lam S K1 D) :=
                Finset.sum_le_sum fun j hj =>
                  hwit _ S K1 D D.2
                    (SG1Proof.stage_term L h3 hg hL hlam hlamC j (Finset.mem_range.mp hj) S)
                    (SG1pProof.stage_termP L hg hL j (Finset.mem_range.mp hj) S K1 hK1)
            _ = _ := by simp
        · by_cases hr : 1 < g.r
          · rw [if_pos hr]
            refine le_trans (SG1Proof.prob_mono (F := fun hist w => S < sAHomeExcess g w (L.inputs hist w))
              L fun hist h hf => hf.2) ?_
            exact hwit _ S K1 _ (hcur _) (SG1Proof.radix_term L h3 hg hL hlam hlamC S)
              (SG1pProof.radix_termP L hg hL S K1 hK1)
          · rw [if_neg hr]
            refine le_of_eq_of_le ?_ le_rfl
            unfold SJobLaw.prob
            simp [hr]
        · exact hwit _ _ K2 _ (hcur _) (SG1Proof.union_term L h3 hg hL hlam hlamC _)
            (SG1pProof.union_termP L hg hL _ K2 hK2)
