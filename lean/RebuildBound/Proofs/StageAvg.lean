import RebuildBound.Proofs.ProductAverage
import RebuildBound.Spec.G

/-!
# StageAvg: counting and averaging lemmas (from G1.Count, G1.Stage)

`pow_countP_sum`, `sum_fin_ite_eq`, residue counts `card_mod_eq_le`, the raw
destination map `rd`, `avg_ite`, `pow_le_exp`, `list_sum_range`, and the
stage factor `stagePsi`. Moved from the binary d = 2 chain (`G1.Count`,
`G1.Stage`); namespace `RebuildBound.G1Proof` kept.
-/

open scoped ENNReal NNReal
namespace RebuildBound.G1Proof
open RebuildBound.Model
theorem sum_fin_ite_eq {n : ℕ} (J : Finset (Fin n)) (y : ℕ) :
    (∑ v ∈ J, if (y == (v : ℕ)) = true then 1 else 0 : ℕ) =
      if y ∈ J.map Fin.valEmbedding then 1 else 0 := by
  by_cases hy : y < n
  · have e : ∀ v : Fin n, ((y == (v : ℕ)) = true) ↔ (⟨y, hy⟩ = v) := by
      intro v; simp [Fin.ext_iff]
    simp only [e]
    rw [Finset.sum_ite_eq]
    congr 1
    apply propext
    simp only [Finset.mem_map, Fin.valEmbedding_apply]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨v, hv, rfl⟩; simpa using hv
  · have e : ∀ v : Fin n, ¬ ((y == (v : ℕ)) = true) := by
      intro v h; simp at h; omega
    have e2 : y ∉ J.map Fin.valEmbedding := by
      simp only [Finset.mem_map, Fin.valEmbedding_apply, not_exists, not_and]
      intro v _ h; omega
    simp [e, e2]

theorem pow_countP_sum (z : ℝ) {n : ℕ} (J : Finset (Fin n)) (f : Model.LogicalKey → ℕ) (l : List Rec)
    (hl : (l.map Rec.key).Nodup) :
    z ^ (∑ v ∈ J, l.countP (fun r => f r.key == (v : ℕ))) =
      ∏ x ∈ (l.map Rec.key).toFinset, (if f x ∈ J.map Fin.valEmbedding then z else 1) := by
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.map_cons, List.nodup_cons] at hl
    rw [List.map_cons, List.toFinset_cons, Finset.prod_insert (by simpa using hl.1), ← ih hl.2]
    simp only [List.countP_cons, Finset.sum_add_distrib, pow_add]
    rw [mul_comm]
    congr 1
    rw [sum_fin_ite_eq]
    split_ifs <;> simp

theorem card_mod_eq_le (m t r : ℕ) (_hm : 0 < m) :
    (∑ a ∈ Finset.range (m * t), if a % m = r then 1 else 0 : ℕ) ≤ t := by
  rw [← Finset.card_filter]
  calc _ ≤ (Finset.range t).card := by
        refine Finset.card_le_card_of_injOn (fun a => a / m) ?_ ?_
        · intro a ha
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha
          simp only [Finset.coe_range, Set.mem_Iio]
          exact Nat.div_lt_of_lt_mul ha.1
        · intro a ha b hb hab
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hb
          simp only at hab
          calc a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm
            _ = m * (b / m) + b % m := by rw [hab, ha.2, hb.2]
            _ = b := Nat.div_add_mod b m
    _ = t := Finset.card_range t

/-- The raw destination `2^(j+1) ⌊(U + o) / 2^(j+1)⌋ + (a mod 2^(j+1))`. -/
def rd (U j o a : ℕ) : ℕ := 2 ^ (j + 1) * ((U + o) / 2 ^ (j + 1)) + a % 2 ^ (j + 1)

theorem rd_eq_imp (U j o a v : ℕ) (h : rd U j o a = v) :
    (U + o) / 2 ^ (j + 1) = v / 2 ^ (j + 1) ∧ a % 2 ^ (j + 1) = v % 2 ^ (j + 1) := by
  unfold rd at h
  subst h
  have hm : 0 < 2 ^ (j + 1) := by positivity
  constructor
  · rw [Nat.mul_add_div hm, Nat.div_eq_of_lt (Nat.mod_lt _ hm), add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_mod]

theorem avg_ite (M : ℕ) (hM : 0 < M) (P : ℕ → Prop) [DecidablePred P] (z : ℝ) :
    (M : ℝ)⁻¹ * ∑ a : Fin M, (if P a then z else 1) =
      1 + (z - 1) * ((∑ a ∈ Finset.range M, if P a then 1 else 0 : ℕ) : ℝ) / M := by
  rw [Fin.sum_univ_eq_sum_range (fun a => if P a then z else 1)]
  have e : ∀ a, (if P a then z else 1) = 1 + (z - 1) * (if P a then 1 else 0 : ℝ) := by
    intro a; split_ifs <;> ring
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  push_cast
  have hM' : (M : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  field_simp

theorem pow_le_exp (n : ℕ) (M lam c : ℝ) (hM : 0 < M) (hc : 0 ≤ c) (hn : (n : ℝ) ≤ lam * M) :
    (1 + c / M) ^ n ≤ Real.exp (lam * c) := by
  calc (1 + c / M) ^ n ≤ (Real.exp (c / M)) ^ n := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp (c / M)]
    _ = Real.exp (n * (c / M)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (lam * c) := by
        apply Real.exp_le_exp.mpr
        rw [mul_div_assoc', div_le_iff₀ hM]
        nlinarith

end RebuildBound.G1Proof
namespace RebuildBound.G1Proof
theorem list_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

end RebuildBound.G1Proof

open scoped ENNReal NNReal
namespace RebuildBound.G1Proof
open RebuildBound.Model RebuildBound.Spec
variable {g : Geom} (L : JobLaw g)
/-- The per-key average for stage `j` at old home `o`. -/
noncomputable def stagePsi (W U j : ℕ) (J' : Finset ℕ) (z : ℝ) (o : ℕ) : ℝ :=
  ((2 ^ W : ℕ) : ℝ)⁻¹ * ∑ a : Fin (2 ^ W), (if rd U j o a ∈ J' then z else 1)

theorem stagePsi_nonneg (W U j : ℕ) (J' : Finset ℕ) (z : ℝ) (hz : 1 ≤ z) (o : ℕ) :
    0 ≤ stagePsi W U j J' z o := by
  unfold stagePsi
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => ?_)
  split_ifs <;> linarith

variable {TA TB : ℕ} {lam D : ℝ≥0}
end RebuildBound.G1Proof
