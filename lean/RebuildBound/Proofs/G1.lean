import RebuildBound.Spec.T
import RebuildBound.Proofs.G1.Trace
import RebuildBound.Proofs.G1.Stage
import RebuildBound.Proofs.G1.Home

/-!
# G1: the pilot theorem at d = 2, conditional on T4a, T4b and P3

`RebuildBound.G1_of : T4a → T4b → P3 → G1_statement`; package G1fin assembles
`RebuildBound.G1` from it and the proofs of T4a, T4b and P3.

**Proof.** On every outcome (history, merge words) a failing job has a first
failing test `t` of the reference trace (`fail_some`). By T4a and T4b (the
structural contract comes from `InputLaw.shape`, and the tier capacities
from the first-failure event's `TiersFit`):
* `t = .stash j`: `j < k + 1` (`reference_stash_lt`: the route's trace records
  only the stages of the model's schedule) and `S j < rawStageExcess j`;
* `t = .dfs d c`: the coarse-range event `rangeEvent`;
* `t = .insertion` or `.drain`: `min S_ins S_out < homeExcess`.
Monotonicity and subadditivity of `JobLaw.prob` (`FiniteLawProof.prob_*_of`) give the
union bound. The stage terms (`G1/Stage.lean`) and the home term
(`G1/Home.lean`) follow from P3 applied to the pushforward of the job law under
the respective count vectors, whose subset MGF envelopes are computed exactly
as finite products over independent uniform word coordinates (`G1/MGF.lean`,
`G1/Count.lean`); the range term is the hypothesis `aRange`.

**Probability obstacles.** The job law
`JobLaw.prob` is by definition a finite `ℝ≥0∞` sum, and the MGF computations
are finite sums and products over the word coordinates `L.Key → Fin 2^W`, done
in `ℝ` and `ℝ≥0∞`. The only measure is the one P3 consumes: the pushforward
`Σ_hist weight • (card⁻¹ • Σ_h dirac (X hist h))` on `Fin n → ℕ`
(`FiniteLawProof.pushLaw`), a finite combination of Dirac measures.
-/

open scoped ENNReal NNReal

namespace RebuildBound.G1Proof

open RebuildBound.Model RebuildBound.Spec

/-- The failure inventory on one outcome (T4a, T4b). -/
theorem fail_cases (h4a : T4a_statement) (h4b : T4b_statement) {g : Geom} (L : JobLaw g)
    {TA TB : ℕ} {lam D : ℝ≥0} (hL : InputLaw L lam D) (rule : CapRule)
    (hrule : rule.Valid) (caps : Caps) (S : ℕ → ℕ) (Lf Si So : ℕ)
    (hstash : ∀ j < g.stages, caps.stash j = some (S j)) (hleaf : caps.leaf = some Lf)
    (hins : caps.ins = some Si) (hout : caps.out = some So)
    (hpool : TA + sumUpTo S g.stages ≤ g.poolSlots)
    (hist : L.Hist) (h : L.Key → Fin (2 ^ L.W))
    (hfit : TiersFit TA TB (L.inputs hist (L.wordFn h)))
    (hfail : (job rule g caps (L.wordFn h) (L.inputs hist (L.wordFn h))).toBool = false) :
    ((∃ j < g.stages,
        S j < rawStageExcess g (L.wOld hist) (L.wordFn h) (L.inputs hist (L.wordFn h)) j) ∨
      rangeEvent g L rule TA S Lf hist (L.wordFn h)) ∨
      min Si So < homeExcess g (L.wordFn h) (L.inputs hist (L.wordFn h)) := by
  have hv := (hL.shape hist h).valid hfit
  obtain ⟨t, ht⟩ := fail_some rule g caps _ _ hfail
  have ha := h4a rule g caps TA TB (L.wOld hist) (L.wordFn h) (L.inputs hist (L.wordFn h))
    hrule hv
  have hb := h4b rule g caps TA TB (L.wOld hist) (L.wordFn h) (L.inputs hist (L.wordFn h))
    hrule hv
  cases t with
  | stash j =>
    obtain ⟨e, he, het⟩ := firstFailure_mem g caps _ _ ht
    have hj := reference_stash_lt rule g _ _ e he j het
    exact Or.inl (Or.inl ⟨j, hj, ha.1 j (S j) (hstash j hj) ht⟩)
  | dfs d c =>
    exact Or.inl (Or.inr (ha.2 d c Lf S hleaf hstash hpool ht))
  | insertion =>
    exact Or.inr (lt_of_le_of_lt (min_le_left _ _) (hb.1 Si hins ht))
  | drain =>
    exact Or.inr (lt_of_le_of_lt (min_le_right _ _) (hb.2 So hout ht))

end RebuildBound.G1Proof

open RebuildBound.Model RebuildBound.Spec in
/-- **G1, conditional on T4a, T4b and P3.** -/
theorem RebuildBound.G1_of (h4a : RebuildBound.Spec.T4a_statement)
    (h4b : RebuildBound.Spec.T4b_statement) (h3 : RebuildBound.Spec.P3_statement) :
    RebuildBound.Spec.G1_statement := by
  intro g L TA TB lam D rule caps S Lf Si So aRange hL hrule hlam hlamC hstash hleaf hins hout
    hpool hrange
  calc L.prob (fun hist w =>
        TiersFit TA TB (L.inputs hist w) ∧ (job rule g caps w (L.inputs hist w)).toBool = false)
      ≤ L.prob (fun hist w =>
          ((∃ j < g.stages, S j < rawStageExcess g (L.wOld hist) w (L.inputs hist w) j) ∨
            rangeEvent g L rule TA S Lf hist w) ∨
          min Si So < homeExcess g w (L.inputs hist w)) :=
        FiniteLawProof.prob_mono_of L.prob_eq fun hist h hf =>
          G1Proof.fail_cases h4a h4b L hL rule hrule caps S Lf Si So hstash hleaf hins hout
            hpool hist h hf.1 hf.2
    _ ≤ (L.prob (fun hist w =>
            ∃ j < g.stages, S j < rawStageExcess g (L.wOld hist) w (L.inputs hist w) j) +
          L.prob (rangeEvent g L rule TA S Lf)) +
          L.prob (fun hist w => min Si So < homeExcess g w (L.inputs hist w)) := by
        refine le_trans (FiniteLawProof.prob_or_of L.prob_eq _ _) ?_
        gcongr
        exact FiniteLawProof.prob_or_of L.prob_eq _ _
    _ ≤ _ := by
        gcongr
        · refine le_trans (FiniteLawProof.prob_exists_lt_of L.prob_eq _ _) ?_
          exact Finset.sum_le_sum fun j hj =>
            G1Proof.stage_term L h3 hL hlam hlamC j (Finset.mem_range.mp hj) (S j)
        · exact G1Proof.home_term L h3 hL hlam hlamC _
