import RebuildBound.Proofs.FiniteCoupling.Prob
import RebuildBound.Proofs.TG2.Words

/-!
# TG2 helpers: one leaf, one old history

`thist_bound`: for a fixed old history (a context `TCtx` of A) and one leaf
`(a, u)`, the average over the `W`-bit words of `(reference coarse count - C)₊` is at
most `tGf`, P13ab's right side at the starting nodes of A. The union bound over
leaves is `prob_le_cover_of`.
-/

open scoped ENNReal NNReal unitInterval

namespace RebuildBound.TG2

open RebuildBound.Model RebuildBound.Spec RebuildBound.G2 RebuildBound.SG2

/-- The per-range test of a starting-node vector (P13ab's right side). -/
noncomputable def tGf {K : Type} [Fintype K] [DecidableEq K] {r b : ℕ} (C P lo : ℕ) (R : Bits b)
    (q : unitInterval) (pos : K → RNode r b) : ℝ≥0∞ :=
  wordAvg (fun h : K → Bits b => rFirstArrivalTest0 C P C lo R q (rrawArrivals pos h (lo + 1)))

/-- One range, one old history: P13ab. -/
theorem thist_bound {rule : CapRule} (hv : rule.Valid) {g : TPGeom} (hk : 1 ≤ g.k)
    (hIk : g.I + 1 < g.k) {unsh : Rec → Bool} {L : TPJobLaw g} (hW : g.k ≤ L.W)
    {p : Model.LogicalKey → ℕ} (inp : TPInputs) (hC : TCtx g p L.KA inp.aMain inp.aTier)
    (h5r : TP5_route_statement) (h5s : TP5_step_statement) (hab : P13ab_statement)
    {a u : ℕ} (ha : a < 2) (hu : u < 2 ^ (g.k - 1 - g.I)) :
    (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
        ∑ hW : L.Key → Fin (2 ^ L.W),
          ((tpRefCoarse g unsh (L.wordFn hW)
            (tpReferenceWith rule g unsh (L.wordFn hW) inp g.canonicalOps) inp g.earlyCap
            (a * 2 ^ (g.k - 1 - g.I) + u) - g.C : ℕ) : ℝ≥0∞) ≤
      tGf g.C g.earlyCap g.I (natToBits (g.k - 1) (u * 2 ^ g.I)) half
        (tPos (g.k - 1) p L.KA) := by
  have hIb : g.I ≤ g.k - 1 := by omega
  have hIb' : g.I < g.k - 1 := by omega
  set P := g.earlyCap
  set R : Bits (g.k - 1) := natToBits (g.k - 1) (u * 2 ^ g.I)
  set ρ := tRoute rule g unsh L.KA inp.aMain
  set early := tearlyK rule g unsh L.KA inp.aMain inp.aTier P
  set F : ({x // x ∈ L.KA} → Bits (g.k - 1)) → ({x // x ∈ L.KA} → Fin 2) → ℝ≥0∞ :=
    fun h c => ((rRangeCount0 ρ g.I early R ⟨a, ha⟩ h c - g.C : ℕ) : ℝ≥0∞)
  have hb : g.k - 1 < L.W := by omega
  calc (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
        ∑ hW : L.Key → Fin (2 ^ L.W),
          ((tpRefCoarse g unsh (L.wordFn hW)
            (tpReferenceWith rule g unsh (L.wordFn hW) inp g.canonicalOps) inp g.earlyCap
            (a * 2 ^ (g.k - 1 - g.I) + u) - g.C : ℕ) : ℝ≥0∞) ≤
      (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
        ∑ hW : L.Key → Fin (2 ^ L.W),
          F (fun x => (lowCls (g.k - 1) 2 (by norm_num) L.W (hW x)).1)
            (fun x => (lowCls (g.k - 1) 2 (by norm_num) L.W (hW x)).2) := by
        refine mul_le_mul_right (Finset.sum_le_sum fun hW _ => ?_) _
        have hw : ∀ x : {x // x ∈ L.KA},
            natToBits (g.k - 1) (L.wordFn hW x.val) =
              (lowCls (g.k - 1) 2 (by norm_num) L.W (hW x)).1 ∧
            L.wordFn hW x.val / 2 ^ (g.k - 1) % 2 =
              ((lowCls (g.k - 1) 2 (by norm_num) L.W (hW x)).2 : ℕ) := by
          intro x
          have : L.wordFn hW x.val = (hW x : ℕ) := by
            simp [TPJobLaw.wordFn, x.prop]
          rw [this]
          exact ⟨rfl, rfl⟩
        refine Nat.cast_le.2 (Nat.sub_le_sub_right (le_of_eq ?_) _)
        exact trefCoarse_eq hv hC hk h5r hIb _ _ _ hw ha hu P
    _ = wordAvg (fun h => classAvg (fun a : Fin 2 => qMass L.W (g.k - 1) 2 a) (fun c => F h c)) :=
        tavg_words L.KA (le_of_lt hb) F
    _ = wordAvg (fun h => classAvg (fun _ : Fin 2 => half) (fun c => F h c)) := by
        simp only [qMass_half hb]
    _ ≤ _ := by
        have hval := tRoute_valid hv hk hC (unsh := unsh) h5s
        have hdis := fun h => tearlyK_disjoint hv hC (unsh := unsh) P hIb h
        have hbl := fun h h' hag => tearlyK_blind hv hC (unsh := unsh) h5r P hIb h h' hag
        have hs : ∑ a : Fin 2, (((fun _ : Fin 2 => half) a : unitInterval) : ℝ) = 1 := by
          simp [half]
        exact hab g.C (tPos (g.k - 1) p L.KA) _ hval g.I hIb' _ P g.C R (fun _ => half)
          ⟨a, ha⟩ hs hdis (fun h => tearlyK_card P h) hbl

end RebuildBound.TG2
