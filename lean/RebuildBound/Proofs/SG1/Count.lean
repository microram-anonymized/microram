import RebuildBound.Proofs.SG1.Dens
import RebuildBound.Proofs.StageAvg

/-!
# SG1: counting lemmas for the stage and home maps
-/

open scoped ENNReal NNReal

namespace RebuildBound.SG1Proof

open RebuildBound.Model RebuildBound.Spec

theorem card_div_eq_le' (U M m c : ℕ) (hm : 0 < m) :
    (∑ o ∈ Finset.range M, if (U + o) / m = c then 1 else 0 : ℕ) ≤ m := by
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

/-- Column sums of the raw destination map over `M` old homes. -/
theorem stage_count' (U M W j : ℕ) (hj : j + 1 ≤ W) (J' : Finset ℕ) :
    (∑ o ∈ Finset.range M, ∑ a ∈ Finset.range (2 ^ W),
      if G1Proof.rd U j o a ∈ J' then 1 else 0 : ℕ) ≤ J'.card * 2 ^ W := by
  have hm : 0 < 2 ^ (j + 1) := by positivity
  have hW : 2 ^ W = 2 ^ (j + 1) * 2 ^ (W - (j + 1)) := by
    rw [← pow_add]; congr 1; omega
  calc (∑ o ∈ Finset.range M, ∑ a ∈ Finset.range (2 ^ W),
        if G1Proof.rd U j o a ∈ J' then 1 else 0 : ℕ)
      = ∑ o ∈ Finset.range M, ∑ a ∈ Finset.range (2 ^ W), ∑ v ∈ J',
          (if G1Proof.rd U j o a = v then 1 else 0 : ℕ) := by
        refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_ite_eq]
    _ = ∑ o ∈ Finset.range M, ∑ v ∈ J', ∑ a ∈ Finset.range (2 ^ W),
          (if G1Proof.rd U j o a = v then 1 else 0 : ℕ) := by
        refine Finset.sum_congr rfl fun o _ => ?_
        exact Finset.sum_comm
    _ = ∑ v ∈ J', ∑ o ∈ Finset.range M, ∑ a ∈ Finset.range (2 ^ W),
          (if G1Proof.rd U j o a = v then 1 else 0 : ℕ) := Finset.sum_comm
    _ ≤ ∑ v ∈ J', ∑ o ∈ Finset.range M, ∑ a ∈ Finset.range (2 ^ W),
          ((if (U + o) / 2 ^ (j + 1) = v / 2 ^ (j + 1) then 1 else 0) *
            (if a % 2 ^ (j + 1) = v % 2 ^ (j + 1) then 1 else 0) : ℕ) := by
        gcongr with v _ o _ a _
        by_cases h : G1Proof.rd U j o a = v
        · obtain ⟨h1, h2⟩ := G1Proof.rd_eq_imp U j o a v h
          simp [h, h1, h2]
        · simp [h]
    _ = ∑ v ∈ J', (∑ o ∈ Finset.range M,
          (if (U + o) / 2 ^ (j + 1) = v / 2 ^ (j + 1) then 1 else 0 : ℕ)) *
          (∑ a ∈ Finset.range (2 ^ W), (if a % 2 ^ (j + 1) = v % 2 ^ (j + 1) then 1 else 0 : ℕ)) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_mul_sum]
    _ ≤ ∑ v ∈ J', 2 ^ (j + 1) * 2 ^ (W - (j + 1)) := by
        gcongr with v _
        · exact card_div_eq_le' U M _ _ hm
        · rw [hW]; exact G1Proof.card_mod_eq_le _ _ _ hm
    _ = J'.card * 2 ^ W := by rw [Finset.sum_const, smul_eq_mul, hW]

/-! ### The current-home map -/

/-- The ceiling `⌈2^(W - k) / r⌉`. -/
def qOf (g : SepGeom) (W : ℕ) : ℕ := (2 ^ (W - g.k) + g.r - 1) / g.r

theorem le_r_mul_qOf (g : SepGeom) (W : ℕ) (hr : 0 < g.r) : 2 ^ (W - g.k) ≤ g.r * qOf g W := by
  unfold qOf
  have h1 := Nat.div_add_mod (2 ^ (W - g.k) + g.r - 1) g.r
  have h2 := Nat.mod_lt (2 ^ (W - g.k) + g.r - 1) hr
  generalize g.r * ((2 ^ (W - g.k) + g.r - 1) / g.r) = Y at h1 ⊢
  omega

theorem homeOf_eq_imp (g : SepGeom) (hr : 0 < g.r) (a v : ℕ) (h : g.homeOf a = v) :
    a % 2 ^ g.k = v % 2 ^ g.k ∧ a / 2 ^ g.k % g.r = v / 2 ^ g.k := by
  unfold SepGeom.homeOf SepGeom.cls at h
  have hP : 0 < 2 ^ g.k := by positivity
  have h1 : a % 2 ^ g.k < 2 ^ g.k := Nat.mod_lt _ hP
  subst h
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  · rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt h1, zero_add]

/-- At most `⌈2^(W-k)/r⌉` words of width `W` have a given home. -/
theorem home_count_one (g : SepGeom) (hr : 0 < g.r) (W : ℕ) (hW : g.k ≤ W) (v : ℕ) :
    (∑ a ∈ Finset.range (2 ^ W), if g.homeOf a = v then 1 else 0 : ℕ) ≤ qOf g W := by
  rw [← Finset.card_filter]
  have hP : 0 < 2 ^ g.k := by positivity
  have hW' : 2 ^ W = 2 ^ g.k * 2 ^ (W - g.k) := by
    rw [← pow_add]; congr 1; omega
  calc _ ≤ ((Finset.range (g.r * qOf g W)).filter fun h => h % g.r = v / 2 ^ g.k).card := by
        refine Finset.card_le_card_of_injOn (fun a => a / 2 ^ g.k) ?_ ?_
        · intro a ha
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
          obtain ⟨h1, h2⟩ := homeOf_eq_imp g hr a v ha.2
          refine ⟨?_, h2⟩
          have : a / 2 ^ g.k < 2 ^ (W - g.k) := by
            apply Nat.div_lt_of_lt_mul
            rw [← hW']; exact ha.1
          exact lt_of_lt_of_le this (le_r_mul_qOf g W hr)
        · intro a ha b hb hab
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hb
          simp only at hab
          obtain ⟨h1, _⟩ := homeOf_eq_imp g hr a v ha.2
          obtain ⟨h2, _⟩ := homeOf_eq_imp g hr b v hb.2
          calc a = 2 ^ g.k * (a / 2 ^ g.k) + a % 2 ^ g.k := (Nat.div_add_mod a _).symm
            _ = 2 ^ g.k * (b / 2 ^ g.k) + b % 2 ^ g.k := by rw [hab, h1, h2]
            _ = b := Nat.div_add_mod b _
    _ ≤ _ := by
        rw [Finset.card_filter]
        exact G1Proof.card_mod_eq_le _ _ _ hr

end RebuildBound.SG1Proof
