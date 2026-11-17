import RebuildBound.Spec.AdaptiveStepsJobs
import RebuildBound.Proofs.DirectJobABounds
import RebuildBound.Proofs.SelJob
import RebuildBound.Proofs.WordLocalS

/-! # AdaptiveSepA: the A witnesses on one law.

* The A witnesses (`sharedARouteWitness`, `sharedARangeWitness`) read only A's
  main and old tier, and the two words only at A's keys (`route_congr`,
  `range_congr`); B never enters.
* On any `SJobLaw` with `SInputLaw`, the route witness or the completed-A
  range event has probability at most `sepABound` with `nA = |KA|`
  (`aBound`): the stage and radix terms (`stage_term`/`stage_termP`,
  `radix_term`/`radix_termP`, P3) and SG2, as in the proof of
  `DirectJobAWitnessProbability`.
* `sepABound` is monotone in the density and the population
  (`sepABound_mono`). -/

open scoped ENNReal NNReal

namespace RebuildBound.AdaptiveSepAProof
open Model Model.DirectJob Spec

/-! ### Word locality of the A witnesses -/

theorem mem_recs_of_some {B : Bucket} {r : Rec} (h : some r ∈ B) : r ∈ B.recs := by
  simpa [Bucket.recs] using h

theorem aAll_eq {inp inp' : SInputs} (hm : inp.aMain = inp'.aMain) (ht : inp.aTier = inp'.aTier) :
    inp.aAll = inp'.aAll := by
  simp only [SInputs.aAll, hm, ht]

theorem rawStage_congr (s : SepGeom) (wo wo' w w' : LogicalKey → Nat) (inp inp' : SInputs)
    (hm : inp.aMain = inp'.aMain) (ht : inp.aTier = inp'.aTier)
    (hwo : ∀ x ∈ inp.aAll, wo x.key = wo' x.key) (hw : ∀ x ∈ inp.aAll, w x.key = w' x.key)
    (j : Nat) : sRawStageExcess s wo w inp j = sRawStageExcess s wo' w' inp' j := by
  unfold sRawStageExcess
  rw [← aAll_eq hm ht]
  congr 1
  apply List.map_congr_left
  intro v _
  congr 1
  apply List.countP_congr
  intro x hx
  simp only [sRawDest, hwo x hx, hw x hx]

theorem aHome_congr (s : SepGeom) (w w' : LogicalKey → Nat) (inp inp' : SInputs)
    (hm : inp.aMain = inp'.aMain) (ht : inp.aTier = inp'.aTier)
    (hw : ∀ x ∈ inp.aAll, w x.key = w' x.key) :
    sAHomeExcess s w inp = sAHomeExcess s w' inp' := by
  unfold sAHomeExcess sExcess sHomeCount
  rw [← aAll_eq hm ht]
  congr 1
  apply List.map_congr_left
  intro v _
  congr 1
  apply List.countP_congr
  intro x hx
  rw [WordLocalS.sHome_congr s w w' x (hw x hx)]

theorem ref_route (rule : CapRule) (g : SepGeom) (w : LogicalKey → Nat) (inp : SInputs)
    (ops : List (Nat × Nat)) :
    (sReferenceWith rule g w inp ops).route = sRouteWith rule g w inp.aMain ops := rfl

theorem refCoarse_congr (s : SepGeom) (w w' : LogicalKey → Nat) (inp inp' : SInputs)
    (hm : inp.aMain = inp'.aMain) (ht : inp.aTier = inp'.aTier)
    (hw : ∀ x ∈ inp.aAll, w x.key = w' x.key) (ops : List (Nat × Nat)) (P v : Nat) :
    sRefCoarse s w (sReferenceWith engineRule s w inp ops) inp P v =
      sRefCoarse s w' (sReferenceWith engineRule s w' inp' ops) inp' P v := by
  have hA : WordLocalS.MP (WordLocalS.Agr w w') inp.aMain := fun B hB r hr =>
    hw r (List.mem_append_left _ (List.mem_flatMap.2 ⟨B, hB, mem_recs_of_some hr⟩))
  obtain ⟨h1, h2⟩ := WordLocalS.sRouteWith_wl s w w' inp.aMain ops hA
  unfold sRefCoarse sEarlyList sLateSheds
  rw [ref_route, ref_route, ← hm, ← ht, ← h1]
  apply List.countP_congr
  intro x hx
  have hx' : WordLocalS.Agr w w' x := by
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 (List.mem_of_mem_take hx) with hx | hx
      · exact hw x (List.mem_append_right _ hx)
      · obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
        exact h2.2.1 l (List.mem_of_mem_take hl) x hxl
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
        exact h2.2.1 l (List.mem_of_mem_drop hl) x hxl
      · exact h2.2.2 x hx
  rw [WordLocalS.sRange_congr s w w' x hx']

theorem route_congr (s : SepGeom) (wo wo' w w' : LogicalKey → Nat) (inp inp' : SInputs)
    (hm : inp.aMain = inp'.aMain) (ht : inp.aTier = inp'.aTier)
    (hwo : ∀ x ∈ inp.aAll, wo x.key = wo' x.key) (hw : ∀ x ∈ inp.aAll, w x.key = w' x.key) :
    sharedARouteWitness s wo w inp ↔ sharedARouteWitness s wo' w' inp' := by
  unfold sharedARouteWitness
  simp only [rawStage_congr s wo wo' w w' inp inp' hm ht hwo hw,
    aHome_congr s w w' inp inp' hm ht hw]

theorem range_congr (s : SepGeom) (w w' : LogicalKey → Nat) (inp inp' : SInputs)
    (hm : inp.aMain = inp'.aMain) (ht : inp.aTier = inp'.aTier)
    (hw : ∀ x ∈ inp.aAll, w x.key = w' x.key) :
    sharedARangeWitness s w inp ↔ sharedARangeWitness s w' inp' := by
  unfold sharedARangeWitness
  simp only [refCoarse_congr s w w' inp inp' hm ht hw]

/-! ### The A part on one law -/

/-- The A terms of `sepBound` bound the route witness or the completed-A range
event on any law (the A half of `DirectJobAWitnessProbability`'s proof). -/
theorem aBound (s : SepGeom) (L : SJobLaw s) (lam D : ℝ≥0) (cutoff : Nat) (hs : s.Valid)
    (hL : SInputLaw L lam D) (hlam : 0 < lam) (hC : (lam : ℝ) ≤ s.C) (hIK : s.I < s.K)
    (hcut : s.stashPages * s.C < cutoff) :
    L.prob (fun hist w => sharedARouteWitness s (L.wOld hist) w (L.inputs hist w) ∨
      sRangeEvent s L engineRule hist w) ≤ sepABound s L.W lam D L.KA.card cutoff := by
  set S := s.stashPages * s.C with hS
  have hwit : ∀ (E : L.Hist → (LogicalKey → Nat) → Prop) (density : ℝ),
      L.prob E ≤ ENNReal.ofReal (Bsub s.N s.C lam S density) →
      L.prob E ≤ ENNReal.ofReal (density * Phi cutoff s.N s.C lam S) →
      L.prob E ≤ ENNReal.ofReal (witness s.N s.C lam S cutoff density) := by
    intro E density h1 h2
    unfold witness
    rw [ENNReal.ofReal_min]
    exact le_min h1 h2
  calc
    L.prob (fun hist w => sharedARouteWitness s (L.wOld hist) w (L.inputs hist w) ∨
        sRangeEvent s L engineRule hist w)
      ≤ (L.prob (fun hist word =>
          ∃ j < s.k, S < sRawStageExcess s (L.wOld hist) word (L.inputs hist word) j) +
        L.prob (fun hist word => 1 < s.r ∧ S < sAHomeExcess s word (L.inputs hist word))) +
        L.prob (sRangeEvent s L engineRule) := by
          refine le_trans (SG1Proof.prob_or L _ _) ?_
          gcongr
          exact SG1Proof.prob_or L _ _
    _ ≤ _ := by
      unfold sepABound
      gcongr
      · refine le_trans (SG1Proof.prob_exists_lt L _ _) ?_
        calc _ ≤ ∑ j ∈ Finset.range s.k,
            ENNReal.ofReal (witness s.N s.C lam S cutoff D) :=
          Finset.sum_le_sum fun j hj =>
            hwit _ D (SG1Proof.stage_term L P3 hs hL hlam hC j (Finset.mem_range.mp hj) S)
              (SG1pProof.stage_termP L hs hL j (Finset.mem_range.mp hj) S cutoff hcut)
          _ = _ := by simp [S]
      · by_cases hr : 1 < s.r
        · rw [ite_eq_left hr]
          refine le_trans (SG1Proof.prob_mono L (F := fun hist word =>
            S < sAHomeExcess s word (L.inputs hist word)) (fun _ _ hf => hf.2)) ?_
          exact hwit _ _ (SG1Proof.radix_term L P3 hs hL hlam hC S)
            (SG1pProof.radix_termP L hs hL S cutoff hcut)
        · rw [ite_eq_right hr]
          apply le_of_eq
          unfold SJobLaw.prob
          simp [hr]
      · exact SG2 s L lam D engineRule hs hL D1Lemmas.engine_valid hIK

/-- `sepABound` is monotone in the old-home density and A's population. -/
theorem sepABound_mono (g : SepGeom) (W : ℕ) (lam : ℝ≥0) {D D' : ℝ≥0} {nA nA' : ℕ} (K1 : ℕ)
    (hr : 1 ≤ g.r) (hD : D ≤ D') (hA : nA ≤ nA') :
    sepABound g W lam D nA K1 ≤ sepABound g W lam D' nA' K1 := by
  unfold sepABound
  have hl : (0 : ℝ) ≤ lam := lam.2
  have hD' : (D : ℝ) ≤ D' := by exact_mod_cast hD
  gcongr
  · exact SelJobAux.witness_mono _ _ hl _ _ hD' D.2
  · split_ifs
    · gcongr
      exact SelJobAux.witness_mono _ _ hl _ _ (SelJobAux.curDensity_mono g W hr hA)
        (SelJobAux.curDensity_nonneg g W nA)
    · exact le_rfl

end RebuildBound.AdaptiveSepAProof
