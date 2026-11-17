import RebuildBound.Proofs.FiniteCoupling.Prob
import RebuildBound.Proofs.TG1.Sched
import RebuildBound.Proofs.G3
import RebuildBound.Proofs.BlindBits.Words
import RebuildBound.Proofs.P8c

/-!
# TG1: the raw destination

The raw destination `dst` (uniform on `[0, T)` for a uniform start and uniform word) and
its push-forward. The union bound and the first-moment step are
`FiniteLawProof.prob_*_of L.prob_eq`.
-/

open scoped ENNReal NNReal
open MeasureTheory

namespace RebuildBound.TG1Proof

open RebuildBound.Model RebuildBound.Spec RebuildBound.G3Proof

variable {g : TPGeom} (L : TPJobLaw g)

theorem wordFn_val (h : L.Key → Fin (2 ^ L.W)) (y : L.Key) : L.wordFn h y = (h y : ℕ) := by
  unfold TPJobLaw.wordFn; simp [y.2]

/-! ### The raw destination -/

theorem dst_lt {k j : ℕ} (hj : j < k) {o a : ℕ} (ho : o < 2 ^ k) :
    2 ^ (j + 1) * (o / 2 ^ (j + 1)) + a % 2 ^ (j + 1) < 2 ^ k := by
  have hb : 0 < 2 ^ (j + 1) := by positivity
  have hk : 2 ^ k = 2 ^ (j + 1) * 2 ^ (k - (j + 1)) := by
    rw [← pow_add]; congr 1; omega
  have h1 : o / 2 ^ (j + 1) < 2 ^ (k - (j + 1)) := by
    rw [Nat.div_lt_iff_lt_mul hb, mul_comm, ← hk]; exact ho
  have h2 := Nat.mod_lt a hb
  have h3 : 2 ^ (j + 1) * (o / 2 ^ (j + 1) + 1) ≤ 2 ^ (j + 1) * 2 ^ (k - (j + 1)) :=
    Nat.mul_le_mul_left _ h1
  rw [hk]; nlinarith

/-- The raw destination of a start bucket `o` and a word `a`, after the stage of bit `j`. -/
def dst (g : TPGeom) (W j : ℕ) (hj : j < g.k) (o : Fin g.T) (a : Fin (2 ^ W)) : Fin g.T :=
  ⟨2 ^ (j + 1) * ((o : ℕ) / 2 ^ (j + 1)) + (a : ℕ) % 2 ^ (j + 1), dst_lt hj o.isLt⟩

theorem card_div_fiber (N b c q : ℕ) (hN : N = b * c) (hb : 0 < b) (hq : q < c) :
    (Finset.univ.filter (fun o : Fin N => (o : ℕ) / b = q)).card = b := by
  subst hN
  have h : (Finset.univ : Finset (Fin b)).card =
      (Finset.univ.filter (fun o : Fin (b * c) => (o : ℕ) / b = q)).card := by
    refine Finset.card_nbij'
      (fun i : Fin b => (⟨b * q + i, ?_⟩ : Fin (b * c)))
      (fun o : Fin (b * c) => (⟨(o : ℕ) % b, Nat.mod_lt _ hb⟩ : Fin b)) ?_ ?_ ?_ ?_
    · have hi := i.isLt
      have : b * (q + 1) ≤ b * c := Nat.mul_le_mul_left _ hq
      nlinarith
    · intro i _
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      rw [Nat.mul_add_div hb, Nat.div_eq_of_lt i.isLt, add_zero]
    · intro o _; simp
    · intro i _
      apply Fin.ext
      simp only
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
    · intro o ho
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ho
      apply Fin.ext
      simp only
      rw [← ho]
      exact (Nat.div_add_mod _ _)
  simpa using h.symm

theorem dst_eq_iff {j : ℕ} {o a e : ℕ} (hb : 0 < 2 ^ (j + 1)) :
    2 ^ (j + 1) * (o / 2 ^ (j + 1)) + a % 2 ^ (j + 1) = e ↔
      o / 2 ^ (j + 1) = e / 2 ^ (j + 1) ∧ a % 2 ^ (j + 1) = e % 2 ^ (j + 1) := by
  have h2 := Nat.mod_lt a hb
  constructor
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [Nat.mul_add_div hb, Nat.div_eq_of_lt h2, add_zero]
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h2]
  · rintro ⟨h1, h3⟩
    rw [h1, h3]; exact Nat.div_add_mod e _

theorem fiber_dst {W j : ℕ} (hj : j < g.k) (hW : g.k ≤ W) (e : Fin g.T) :
    (Finset.univ.filter (fun p : Fin g.T × Fin (2 ^ W) => dst g W j hj p.1 p.2 = e)).card =
      2 ^ W := by
  classical
  have hb : 0 < 2 ^ (j + 1) := by positivity
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have step : ∀ o : Fin g.T, (∑ a : Fin (2 ^ W), if dst g W j hj o a = e then 1 else 0) =
      if (o : ℕ) / 2 ^ (j + 1) = (e : ℕ) / 2 ^ (j + 1) then 2 ^ (W - (j + 1)) else 0 := by
    intro o
    rw [← Finset.card_filter]
    split_ifs with h
    · rw [← RebuildBound.G2.card_mod_fiber (W := W) (b := j + 1) (by omega)
        (n := (e : ℕ) % 2 ^ (j + 1)) (Nat.mod_lt _ hb)]
      congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, dst, Fin.ext_iff]
      rw [dst_eq_iff hb]
      simp [h]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a _ ha
      apply h
      simp only [dst, Fin.ext_iff] at ha
      exact ((dst_eq_iff hb).1 ha).1
  simp_rw [step]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul]
  have hT : g.T = 2 ^ (j + 1) * 2 ^ (g.k - (j + 1)) := by
    unfold TPGeom.T; rw [← pow_add]; congr 1; omega
  have hq : (e : ℕ) / 2 ^ (j + 1) < 2 ^ (g.k - (j + 1)) := by
    rw [Nat.div_lt_iff_lt_mul hb, mul_comm, ← hT]; exact e.isLt
  rw [card_div_fiber g.T _ _ _ hT hb hq, ← pow_add]
  congr 1; omega

/-- The average over pairs of a function of the pair of independent vectors. -/
theorem avg_pair {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (G : (ι → A) → (ι → B) → ℝ≥0∞) :
    (Fintype.card (ι → A) : ℝ≥0∞)⁻¹ *
      ∑ o : ι → A, ((Fintype.card (ι → B) : ℝ≥0∞)⁻¹ * ∑ h : ι → B, G o h) =
    (Fintype.card (ι → A × B) : ℝ≥0∞)⁻¹ *
      ∑ q : ι → A × B, G (fun i => (q i).1) (fun i => (q i).2) := by
  let e := Equiv.arrowProdEquivProdArrow ι (fun _ => A) (fun _ => B)
  have h1 : ∑ q : ι → A × B, G (fun i => (q i).1) (fun i => (q i).2) =
      ∑ pr : (ι → A) × (ι → B), G pr.1 pr.2 :=
    Fintype.sum_equiv e _ _ (fun q => rfl)
  have hc : Fintype.card (ι → A × B) = Fintype.card (ι → A) * Fintype.card (ι → B) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  rw [h1, Fintype.sum_prod_type, hc, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    ← Finset.mul_sum, ← mul_assoc]

end RebuildBound.TG1Proof
