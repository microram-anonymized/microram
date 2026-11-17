import RebuildBound.Proofs.TG1.Prob
import RebuildBound.Proofs.P8a
import RebuildBound.Proofs.P7fin

/-!
# TG1: the stash term of a preparation (density, push-forward, P8a, P7)
-/

open scoped ENNReal NNReal
open MeasureTheory

namespace RebuildBound.TG1Proof

open RebuildBound.Model RebuildBound.Spec RebuildBound.G3Proof

/-- P8a then P7 for `n` independent uniform homes on `Fin (2^m)`. -/
theorem conv_bound (m n C S K' : ℕ) (lam : ℝ≥0) (hS : S < K') (hload : (n : ℝ≥0) ≤ lam * 2 ^ m) :
    ∫⁻ y, restrictedStopLoss (Finset.univ : Finset (Fin (2 ^ m))) C S y
      ∂(convList (List.replicate n (unitLaw (fun _ : Fin (2 ^ m) => (1 / 2 ^ m : ℝ≥0))))) ≤
      ENNReal.ofReal (Phi K' (2 ^ m) C lam S) := by
  have h8 := RebuildBound.P8a (Finset.univ : Finset (Fin (2 ^ m))) C S (1 / 2 ^ m) lam
    (List.replicate n (fun _ : Fin (2 ^ m) => (1 / 2 ^ m : ℝ≥0))) ?_ ?_ ?_
  · rw [List.map_replicate] at h8
    have h7 := RebuildBound.P7 (Finset.univ : Finset (Fin (2 ^ m))) C S K' lam hS
    rw [Finset.card_univ, Fintype.card_fin] at h7
    exact le_trans h8 h7
  · intro p hp
    rw [List.eq_of_mem_replicate hp]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat]
    field_simp
  · intro p hp v
    rw [List.eq_of_mem_replicate hp]
  · simp only [List.length_replicate]
    calc (n : ℝ≥0) * (1 / 2 ^ m) ≤ lam * 2 ^ m * (1 / 2 ^ m) := by gcongr
      _ = lam := by field_simp

variable {g : TPGeom} (L : TPJobLaw g)

theorem T_pos : 0 < g.T := by unfold TPGeom.T; positivity

/-- A's starting buckets as an element of `Fin T` (meaningful when `pos < T`). -/
def oF (hist : L.Hist) : L.Key → Fin g.T :=
  fun y => ⟨L.pos hist y % g.T, Nat.mod_lt _ T_pos⟩

variable {L} {lam D : ℝ≥0}

theorem density_bound (hL : TPLaw L lam D) (hpos : ∀ hist, ∀ x ∈ L.KA, L.pos hist x < g.T)
    (G : (L.Key → Fin g.T) → ℝ≥0∞) :
    ∑ hist, L.weight hist * G (oF L hist) ≤
      (D : ℝ≥0∞) * ((Fintype.card (L.Key → Fin g.T) : ℝ≥0∞)⁻¹ * ∑ o, G o) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (oF L) (fun hist => L.weight hist * G (oF L hist))]
  have hcard : (Fintype.card (L.Key → Fin g.T) : ℝ≥0∞) = (g.T : ℝ≥0∞) ^ L.KA.card := by
    simp
  rw [hcard, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o _
  have hfilt : ∀ hist ∈ Finset.univ.filter (fun hist => oF L hist = o),
      L.weight hist * G (oF L hist) = L.weight hist * G o := by
    intro hist hh
    rw [(Finset.mem_filter.1 hh).2]
  rw [Finset.sum_congr rfl hfilt, ← Finset.sum_mul]
  have hden := hL.density o
  have hset : (Finset.univ.filter (fun hist => oF L hist = o)) =
      Finset.univ.filter (fun hist => ∀ x : L.KA, L.pos hist x = o x) := by
    ext hist
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, oF, funext_iff, Fin.ext_iff]
    refine forall_congr' fun x => ?_
    rw [Nat.mod_eq_of_lt (hpos hist x.1 x.2)]
  rw [hset]
  calc (∑ hist ∈ Finset.univ.filter (fun hist => ∀ x : L.KA, L.pos hist x = o x),
        L.weight hist) * G o ≤ ((D : ℝ≥0∞) / (g.T : ℝ≥0∞) ^ L.KA.card) * G o := by
        gcongr
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- The push-forward of uniform starts and uniform words to uniform destinations. -/
theorem push_dst {j : ℕ} (hj : j < g.k) (hW : g.k ≤ L.W) (F : (Fin g.T → ℕ) → ℝ≥0∞) :
    (Fintype.card (L.Key → Fin g.T) : ℝ≥0∞)⁻¹ *
      ∑ o : L.Key → Fin g.T, ((Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
        ∑ h : L.Key → Fin (2 ^ L.W), F (∑ y, unitVec (dst g L.W j hj (o y) (h y)))) =
    (Fintype.card (L.Key → Fin g.T) : ℝ≥0∞)⁻¹ *
      ∑ e : L.Key → Fin g.T, F (∑ y, unitVec (e y)) := by
  classical
  have : Nonempty (Fin g.T) := ⟨⟨0, T_pos⟩⟩
  rw [avg_pair (G := fun o h => F (∑ y, unitVec (dst g L.W j hj (o y) (h y))))]
  have := RebuildBound.G2.avg_comp
    (fun q : L.Key → Fin g.T × Fin (2 ^ L.W) => fun y => dst g L.W j hj (q y).1 (q y).2)
    ((2 ^ L.W) ^ Fintype.card L.Key) (by positivity) ?_ (fun e => F (∑ y, unitVec (e y)))
  · exact this
  · intro e
    have : Finset.univ.filter (fun q : L.Key → Fin g.T × Fin (2 ^ L.W) =>
        (fun y => dst g L.W j hj (q y).1 (q y).2) = e) =
        Fintype.piFinset (fun y => Finset.univ.filter
          (fun p : Fin g.T × Fin (2 ^ L.W) => dst g L.W j hj p.1 p.2 = e y)) := by
      ext q
      simp [funext_iff]
    rw [this, Fintype.card_piFinset]
    simp only [fiber_dst hj hW]
    rw [Finset.prod_const, Finset.card_univ]

theorem dHome_self (k : ℕ) (a : Fin (2 ^ k)) : RebuildBound.G3Proof.dHome k k a = a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

/-- The average over uniform destination vectors is the integral against `n` uniform homes. -/
theorem avg_eq_integral (F : (Fin (2 ^ g.k) → ℕ) → ℝ≥0∞) :
    (Fintype.card (L.Key → Fin (2 ^ g.k)) : ℝ≥0∞)⁻¹ *
      ∑ e : L.Key → Fin (2 ^ g.k), F (∑ y, unitVec (e y)) =
    ∫⁻ y, F y ∂(convList (List.replicate L.KA.card
        (unitLaw (fun _ : Fin (2 ^ g.k) => (1 / 2 ^ g.k : ℝ≥0))))) := by
  have hb := bridgeG (m := g.k) (W := g.k) le_rfl (ι := L.Key) F
  have hc : Fintype.card L.Key = L.KA.card := Fintype.card_coe _
  rw [hc] at hb
  rw [hb]
  simp only [dHome_self]
  rw [Fintype.card_fun, Fintype.card_fin, hc, Nat.cast_pow]

theorem stash_term (hL : TPLaw L lam D) (hpos : ∀ hist, ∀ x ∈ L.KA, L.pos hist x < g.T)
    {j : ℕ} (hj : j < g.k) (C S K' : ℕ) (hS : S < K')
    (E : L.Hist → (Model.LogicalKey → ℕ) → Prop)
    (hE : ∀ hist h, E hist (L.wordFn h) → 1 ≤ restrictedStopLoss (Finset.univ : Finset (Fin g.T))
      C S (∑ y, unitVec (dst g L.W j hj (oF L hist y) (h y)))) :
    L.prob E ≤ (D : ℝ≥0∞) * ENNReal.ofReal (Phi K' g.T C lam S) := by
  classical
  have hW : g.k ≤ L.W := hL.wide
  let F : (Fin g.T → ℕ) → ℝ≥0∞ := restrictedStopLoss (Finset.univ : Finset (Fin g.T)) C S
  have h1 := FiniteLawProof.prob_le_sum_of L.prob_eq E
    (fun hist h => F (∑ y, unitVec (dst g L.W j hj (oF L hist y) (h y)))) hE
  have h2 := density_bound hL hpos (fun o : L.Key → Fin g.T =>
    (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
          ∑ h : L.Key → Fin (2 ^ L.W), F (∑ y, unitVec (dst g L.W j hj (o y) (h y))))
  have h3 := push_dst (L := L) hj hW F
  have h4 := avg_eq_integral (L := L) F
  have h5 := conv_bound g.k L.KA.card C S K' lam hS (by simpa [TPGeom.T] using hL.load)
  refine le_trans h1 (le_trans h2 ?_)
  gcongr
  exact (h3.le.trans (h4.le.trans h5))

end RebuildBound.TG1Proof
