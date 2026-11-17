import RebuildBound.Proofs.ProductAverage
import RebuildBound.Spec.G
import RebuildBound.Proofs.StageAvg

/-!
# G1: counting and averaging lemmas

* `avg_prod`: the uniform average over a function space of a product of
  per-coordinate factors is the product of the per-coordinate averages.
* `pow_countP_sum`: for a list distinct by key, `z ^ (Σ_{v ∈ J} #{r : f r.key = v})`
  is a product over its keys.
* Counting in `ℕ`: residues mod `m` in `[0, m t)`, and the column sums of the raw
  destination map `(o, a) ↦ 2^(j+1) ⌊(U + o) / 2^(j+1)⌋ + (a mod 2^(j+1))`.
* `avg_ite`: the average of `if P a then z else 1`.
* `pow_le_exp`: `(1 + c / M)^n ≤ exp (λ c)` when `n ≤ λ M`.
-/

open scoped ENNReal NNReal

namespace RebuildBound.G1Proof

open RebuildBound.Model

/-! ### Averages over function spaces -/

theorem avg_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : ι → Fin m → ℝ) :
    ((Fintype.card (ι → Fin m) : ℝ))⁻¹ * ∑ h : ι → Fin m, ∏ i, f i (h i) =
      ∏ i, ((m : ℝ)⁻¹ * ∑ a, f i a) := by
  exact ProductAverage.avg_prod m f

/-! ### Counts of a list distinct by key -/

/-! ### Counting in `ℕ` -/

theorem card_div_eq_le (U m c : ℕ) (hm : 0 < m) :
    (∑ o ∈ Finset.range U, if (U + o) / m = c then 1 else 0 : ℕ) ≤ m := by
  rw [← Finset.card_filter]
  calc _ ≤ (Finset.Ico (m * c) (m * c + m)).card := by
        refine Finset.card_le_card_of_injOn (fun o => U + o) ?_ ?_
        · intro o ho
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ho
          simp only [Finset.coe_Ico, Set.mem_Ico]
          have h1 := Nat.div_add_mod (U + o) m
          have h2 := Nat.mod_lt (U + o) hm
          rw [ho.2] at h1
          constructor <;> omega
        · intro a _ b _ h
          simpa using h
    _ = m := by simp

/-- Column sums of the raw destination map: every destination has at most
`2^W` preimages `(o, a) ∈ [0, U) × [0, 2^W)`. -/
theorem stage_count (U W j : ℕ) (hj : j + 1 ≤ W) (J' : Finset ℕ) :
    (∑ o ∈ Finset.range U, ∑ a ∈ Finset.range (2 ^ W),
      if rd U j o a ∈ J' then 1 else 0 : ℕ) ≤ J'.card * 2 ^ W := by
  have hm : 0 < 2 ^ (j + 1) := by positivity
  have hW : 2 ^ W = 2 ^ (j + 1) * 2 ^ (W - (j + 1)) := by
    rw [← pow_add]; congr 1; omega
  calc (∑ o ∈ Finset.range U, ∑ a ∈ Finset.range (2 ^ W),
        if rd U j o a ∈ J' then 1 else 0 : ℕ)
      = ∑ o ∈ Finset.range U, ∑ a ∈ Finset.range (2 ^ W), ∑ v ∈ J',
          (if rd U j o a = v then 1 else 0 : ℕ) := by
        refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_ite_eq]
    _ = ∑ o ∈ Finset.range U, ∑ v ∈ J', ∑ a ∈ Finset.range (2 ^ W),
          (if rd U j o a = v then 1 else 0 : ℕ) := by
        refine Finset.sum_congr rfl fun o _ => ?_
        exact Finset.sum_comm
    _ = ∑ v ∈ J', ∑ o ∈ Finset.range U, ∑ a ∈ Finset.range (2 ^ W),
          (if rd U j o a = v then 1 else 0 : ℕ) := Finset.sum_comm
    _ ≤ ∑ v ∈ J', ∑ o ∈ Finset.range U, ∑ a ∈ Finset.range (2 ^ W),
          ((if (U + o) / 2 ^ (j + 1) = v / 2 ^ (j + 1) then 1 else 0) *
            (if a % 2 ^ (j + 1) = v % 2 ^ (j + 1) then 1 else 0) : ℕ) := by
        gcongr with v _ o _ a _
        by_cases h : rd U j o a = v
        · obtain ⟨h1, h2⟩ := rd_eq_imp U j o a v h
          simp [h, h1, h2]
        · simp [h]
    _ = ∑ v ∈ J', (∑ o ∈ Finset.range U,
          (if (U + o) / 2 ^ (j + 1) = v / 2 ^ (j + 1) then 1 else 0 : ℕ)) *
          (∑ a ∈ Finset.range (2 ^ W), (if a % 2 ^ (j + 1) = v % 2 ^ (j + 1) then 1 else 0 : ℕ)) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_mul_sum]
    _ ≤ ∑ v ∈ J', 2 ^ (j + 1) * 2 ^ (W - (j + 1)) := by
        gcongr with v _
        · exact card_div_eq_le U _ _ hm
        · rw [hW]; exact card_mod_eq_le _ _ _ hm
    _ = J'.card * 2 ^ W := by rw [Finset.sum_const, smul_eq_mul, hW]

/-- Residues in a set `J'`: at most `|J'| t` elements of `[0, m t)`. -/
theorem home_count (m t : ℕ) (hm : 0 < m) (J' : Finset ℕ) :
    (∑ a ∈ Finset.range (m * t), if a % m ∈ J' then 1 else 0 : ℕ) ≤ J'.card * t := by
  calc (∑ a ∈ Finset.range (m * t), if a % m ∈ J' then 1 else 0 : ℕ)
      = ∑ a ∈ Finset.range (m * t), ∑ v ∈ J', (if a % m = v then 1 else 0 : ℕ) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_ite_eq]
    _ = ∑ v ∈ J', ∑ a ∈ Finset.range (m * t), (if a % m = v then 1 else 0 : ℕ) :=
        Finset.sum_comm
    _ ≤ ∑ v ∈ J', t := by
        gcongr with v _
        exact card_mod_eq_le m t v hm
    _ = J'.card * t := by rw [Finset.sum_const, smul_eq_mul]

/-! ### Real averages -/

end RebuildBound.G1Proof

