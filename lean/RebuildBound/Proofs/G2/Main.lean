import RebuildBound.Proofs.FiniteCoupling.Prob
import RebuildBound.Proofs.G2.Range
import RebuildBound.Proofs.G2.Words
import RebuildBound.Proofs.P11ab
import RebuildBound.Proofs.P11d
import RebuildBound.Proofs.P11e

/-!
# G2: the completed-A coarse-range bound (assembly)

1. Union over the `2^(b - lo)` ranges (`prob_le_cover_of`).
2. For one range and one old history (`hist_bound`): the event is at most the
   stop-loss of the reference count; the count depends on the words only
   through their low `b` bits on A's keys (`refC_congr`), so the average over
   the merge family's words is the average over `K → Bits b` (`avg_comp`,
   `fiber_resW`); there the count is the blind route's `rangeCount`
   (`refC_eq_rangeCount`) and P11ab applies.
3. The bound depends on the history only through A's old homes; grouping by
   old homes and the density factor give `D` times the uniform old-home
   average (`density_bound`), which is P11d's left side (`fiber_resO`,
   `posOf_resO`); P11e evaluates P11d's right side.
-/

open scoped ENNReal NNReal
open MeasureTheory

namespace RebuildBound.G2

open RebuildBound.Model RebuildBound.Spec

variable {g : Geom} (L : JobLaw g)

/-- A fixed input assignment for the structural contract. -/
def h0 : L.Key → Fin (2 ^ L.W) := fun _ => ⟨0, by positivity⟩

variable {L} {lam D : ℝ≥0} (hL : InputLaw L lam D) {rule : CapRule}
  (hv : rule.Valid)

/-- The per-range test of an old-home vector (P11ab's right side). -/
noncomputable def Gf (C P Lf lo : ℕ) {K : Type} [Fintype K] [DecidableEq K] {b : ℕ} (R : Bits b)
    (pos : K → Bits b) : ℝ≥0∞ :=
  wordAvg (fun h : K → Bits b => firstArrivalTest C P Lf lo R (rawArrivals pos h (lo + 1)))

include hL hv in
/-- One range, one old history: P11ab. -/
theorem hist_bound (hlo : g.lo < g.k) (P Lf : ℕ) {R : ℕ} (hR : R < g.ranges) (hist : L.Hist) :
    (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
        ∑ hW : L.Key → Fin (2 ^ L.W),
          ((refC rule g (L.wordFn hW) (L.aIn hist).1 (L.aIn hist).2 P R - Lf : ℕ) : ℝ≥0∞) ≤
      Gf g.C P Lf g.lo (natToBits (g.k + 1) (R * 2 ^ g.lo)) (aPos g (L.wOld hist) L.KA) := by
  have hI := (hL.shape hist (h0 L)).valid_self
  have hK : (((L.inputs hist (L.wordFn (h0 L))).aAll).map Rec.key).toFinset = L.KA :=
    hL.aKeys hist
  set b := g.k + 1
  have hb : b ≤ L.W := hL.wide
  -- the words matter only through their low `b` bits on A's keys
  have hcongr : ∀ hW : L.Key → Fin (2 ^ L.W),
      refC rule g (L.wordFn hW) (L.aIn hist).1 (L.aIn hist).2 P R =
        refC rule g (wOf L.KA b (resW L.KA L.KB L.W b hW)) (L.aIn hist).1 (L.aIn hist).2 P R := by
    intro hW
    apply refC_congr hv g hI hK _ P R (by omega)
    intro x hx
    have hxu : x ∈ L.KA ∪ L.KB := Finset.mem_union_left _ hx
    have e1 := wOf_mem (resW L.KA L.KB L.W b hW) ⟨x, hx⟩
    simp only at e1
    rw [e1, resW]
    simp only
    rw [bitsEquiv_natToBits, Nat.mod_mod]
    simp [JobLaw.wordFn, hxu, b]
  simp_rw [hcongr]
  rw [avg_comp (resW L.KA L.KB L.W b) _ (resW_fiber_ne_zero L.KA L.KB L.W b)
    (fiber_resW L.KA L.KB hb)
    (fun h => ((refC rule g (wOf L.KA b h) (L.aIn hist).1 (L.aIn hist).2 P R - Lf : ℕ) : ℝ≥0∞))]
  have hvalid := aRoute_valid hv g hI hK
  have hab := RebuildBound.P11ab g.C (aPos g (L.wOld hist) L.KA)
    (aRoute rule g L.KA (L.aIn hist).1) hvalid g.lo (by omega)
    (earlyK rule g L.KA (L.aIn hist).1 (L.aIn hist).2 P) P Lf
    (natToBits (g.k + 1) (R * 2 ^ g.lo))
    (earlyK_disjoint hv g hI P hlo) (earlyK_card (rule := rule) (inp := L.inputs hist (L.wordFn (h0 L))) g P) (earlyK_blind hv g hI hK P hlo)
  unfold wordAvg at hab
  unfold Gf wordAvg
  refine le_trans (le_of_eq ?_) hab
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  exact congrArg (fun n : ℕ => ((n - Lf : ℕ) : ℝ≥0∞)) (refC_eq_rangeCount hv g hI hK P hlo h hR)

/-- A's old homes of a history. -/
def oh (hist : L.Hist) : {x // x ∈ L.KA} → Fin (2 ^ g.k) :=
  fun x => ⟨L.wOld hist x.val % g.U, Nat.mod_lt _ (by simp [Geom.U])⟩

/-- A's starting buckets from old homes. -/
def posOf {K : Type} (o : K → Fin (2 ^ g.k)) : K → Bits (g.k + 1) :=
  fun x => natToBits (g.k + 1) (2 ^ g.k + (o x : ℕ))

theorem aPos_eq (hist : L.Hist) : aPos g (L.wOld hist) L.KA = posOf (oh hist) := rfl

include hL in
/-- The old-home density. -/
theorem density_bound (G : ({x // x ∈ L.KA} → Fin (2 ^ g.k)) → ℝ≥0∞) :
    ∑ hist, L.weight hist * G (oh hist) ≤
      (D : ℝ≥0∞) * ((Fintype.card ({x // x ∈ L.KA} → Fin (2 ^ g.k)) : ℝ≥0∞)⁻¹ *
        ∑ o, G o) := by
  rw [← Finset.sum_fiberwise Finset.univ oh (fun hist => L.weight hist * G (oh hist))]
  have hcard : (Fintype.card ({x // x ∈ L.KA} → Fin (2 ^ g.k)) : ℝ≥0∞) =
      (g.U : ℝ≥0∞) ^ L.KA.card := by
    simp [Geom.U]
  rw [hcard, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o _
  have hfilt : ∀ hist ∈ Finset.univ.filter (fun hist => oh hist = o),
      L.weight hist * G (oh hist) = L.weight hist * G o := by
    intro hist hh
    rw [(Finset.mem_filter.1 hh).2]
  rw [Finset.sum_congr rfl hfilt, ← Finset.sum_mul]
  have hden := hL.density o
  have hset : (Finset.univ.filter (fun hist => oh hist = o)) =
      Finset.univ.filter (fun hist => ∀ x : L.KA, L.wOld hist x % g.U = o x) := by
    ext hist
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, oh, funext_iff, Fin.ext_iff]
  rw [hset]
  calc (∑ hist ∈ Finset.univ.filter (fun hist => ∀ x : L.KA, L.wOld hist x % g.U = o x),
        L.weight hist) * G o ≤ ((D : ℝ≥0∞) / (g.U : ℝ≥0∞) ^ L.KA.card) * G o := by
        gcongr
    _ = _ := by rw [div_eq_mul_inv]; ring

include hL hv in
/-- One range: the bound `D · stopLoss`. -/
theorem range_bound (hlo : g.lo < g.k) {TA : ℕ} (Lf : ℕ) (S : ℕ → ℕ) {R : ℕ} (hR : R < g.ranges) :
    L.prob (fun hist w => Lf < refCoarse g w (reference rule g w (L.inputs hist w))
        (L.inputs hist w) (TA + sumUpTo S g.lo) R) ≤
      (D : ℝ≥0∞) * stopLoss (rangeLaw g.C lam (TA + sumUpTo S g.lo) (halfPow (g.k + 1 - g.lo))
        (2 ^ g.lo) (g.k + 1 - g.lo)) Lf := by
  set P := TA + sumUpTo S g.lo
  set R' : Bits (g.k + 1) := natToBits (g.k + 1) (R * 2 ^ g.lo)
  -- the event is below the stop-loss of the reference count
  have h1 : L.prob (fun hist w => Lf < refCoarse g w (reference rule g w (L.inputs hist w))
        (L.inputs hist w) P R) ≤
      ∑ hist, L.weight hist * Gf g.C P Lf g.lo R' (posOf (oh hist)) := by
    unfold JobLaw.prob
    apply Finset.sum_le_sum
    intro hist _
    gcongr
    refine le_trans ?_ (hist_bound hL hv hlo P Lf hR hist)
    gcongr with hW
    split_ifs with hE
    · have : 1 ≤ refC rule g (L.wordFn hW) (L.aIn hist).1 (L.aIn hist).2 P R - Lf := by
        change Lf < refC rule g (L.wordFn hW) (L.aIn hist).1 (L.aIn hist).2 P R at hE
        omega
      exact_mod_cast this
    · exact zero_le
  refine h1.trans ((density_bound hL (fun o => Gf g.C P Lf g.lo R' (posOf o))).trans ?_)
  gcongr
  -- the uniform old-home average is P11d's left side
  have hK : (Fintype.card {x // x ∈ L.KA} : ℝ≥0) ≤ lam * 2 ^ g.k := by
    rw [Fintype.card_coe]
    have := hL.aLoad
    simpa [Geom.U] using this
  have hd := RebuildBound.P11d (K := {x // x ∈ L.KA}) (k := g.k) g.C P Lf g.lo R' lam hlo hK
  have he := RebuildBound.P11e (b := g.k + 1) g.C P Lf g.lo R' lam (by omega)
  rw [he] at hd
  refine le_trans (le_of_eq ?_) hd
  rw [← avg_comp (resO g.k) _ (by positivity : (∏ _x : {x // x ∈ L.KA}, 2) ≠ 0)
    (fiber_resO g.k) (fun o => Gf g.C P Lf g.lo R' (posOf o))]
  have hpos : ∀ a : {x // x ∈ L.KA} → Bits (g.k + 1),
      posOf (resO g.k a) = fun x => Function.update (a x) (Fin.last g.k) true :=
    fun a => funext (posOf_resO g.k a)
  simp only [hpos]
  rfl

end RebuildBound.G2
