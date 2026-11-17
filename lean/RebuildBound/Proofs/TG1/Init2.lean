import RebuildBound.Proofs.TG1.Bridge

/-!
# IG1: the stash term of an initialization (P8c, P7)
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.TG1Proof

open RebuildBound.Model RebuildBound.Spec RebuildBound.P11dProof

theorem card_block {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (m : List α) (_hnd : m.Nodup) (N q : ℕ) (hN : 0 < N) :
    (m.toFinset.filter (fun x => m.idxOf x / N = q)).card ≤ N := by
  classical
  have h1 : (m.toFinset.filter (fun x => m.idxOf x / N = q)).card ≤
      (Finset.Ico (q * N) (q * N + N)).card := by
    refine Finset.card_le_card_of_injOn (fun x => m.idxOf x) ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, List.mem_toFinset, Set.mem_ofPred_eq] at hx
      simp only [Finset.coe_Ico, Set.mem_Ico]
      have := Nat.div_add_mod (m.idxOf x) N
      have h2 := Nat.mod_lt (m.idxOf x) hN
      rw [hx.2] at this
      have h3 : q * N = N * q := mul_comm _ _
      constructor <;> omega
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, List.mem_toFinset, Set.mem_ofPred_eq] at hx hy
      exact (List.idxOf_inj hx.1).mp hxy
  simpa using h1

theorem card_dst_a {g : TPGeom} {W j : ℕ} (hj : j < g.k) (hW : g.k ≤ W) (o e : Fin g.T) :
    (Finset.univ.filter (fun a : Fin (2 ^ W) => dst g W j hj o a = e)).card =
      if (o : ℕ) / 2 ^ (j + 1) = (e : ℕ) / 2 ^ (j + 1) then 2 ^ (W - (j + 1)) else 0 := by
  classical
  have hb : 0 < 2 ^ (j + 1) := by positivity
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

theorem law_dst {g : TPGeom} {W j : ℕ} (hj : j < g.k) (hW : g.k ≤ W) (o v : Fin g.T) :
    law (dst g W j hj o) v =
      if (o : ℕ) / 2 ^ (j + 1) = (v : ℕ) / 2 ^ (j + 1) then 1 / 2 ^ (j + 1) else 0 := by
  unfold law
  rw [card_dst_a hj hW]
  split_ifs
  · have : (2 : ℝ≥0) ^ W = 2 ^ (j + 1) * 2 ^ (W - (j + 1)) := by
      rw [← pow_add]; congr 1; omega
    simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    rw [this]
    field_simp
  · simp

variable {g : TPGeom} (L : TPJobLaw g)

theorem mean_bound (input : List Rec) (hnd : (input.map Rec.key).Nodup)
    (hKA : (input.map Rec.key).toFinset = L.KA) (hlen : input.length ≤ g.C / 2 * g.T)
    (hW : g.k ≤ L.W) {j : ℕ} (hj : j < g.k) (v : Fin g.T) :
    ∑ y : L.Key, law (dst g L.W j hj (oP L (pos0 g input) y)) v ≤ ((g.C / 2 : ℕ) : ℝ≥0) := by
  classical
  have hb : 0 < 2 ^ (j + 1) := by positivity
  have hpos : ∀ x ∈ L.KA, pos0 g input x < g.T := by
    intro x hx
    rw [← hKA] at hx
    have hx' := List.mem_toFinset.mp hx
    have hlt : (input.map Rec.key).idxOf x < input.length := by
      simpa using List.idxOf_lt_length_iff.mpr hx'
    unfold pos0
    rcases Nat.eq_zero_or_pos (g.C / 2) with h0 | h0
    · rw [h0] at hlen; omega
    · rw [Nat.div_lt_iff_lt_mul h0]; rw [mul_comm] at hlen; omega
  simp_rw [law_dst hj hW]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun y : L.Key => ((oP L (pos0 g input) y : Fin g.T) : ℕ) /
      2 ^ (j + 1) = (v : ℕ) / 2 ^ (j + 1))).card ≤ g.C / 2 * 2 ^ (j + 1) := by
    rcases Nat.eq_zero_or_pos (g.C / 2) with h0 | h0
    · have : input = [] := by
        rw [h0] at hlen; simpa using hlen
      subst this
      have : L.KA = ∅ := by rw [← hKA]; simp
      have hemp : IsEmpty L.Key := ⟨fun y => by simpa [this] using y.2⟩
      simp
    · have h1 : (Finset.univ.filter (fun y : L.Key => ((oP L (pos0 g input) y : Fin g.T) : ℕ) /
          2 ^ (j + 1) = (v : ℕ) / 2 ^ (j + 1))).card =
          (L.KA.filter (fun x => (input.map Rec.key).idxOf x / (g.C / 2 * 2 ^ (j + 1)) =
            (v : ℕ) / 2 ^ (j + 1))).card := by
        rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_coe_sort L.KA]
        refine Finset.sum_congr rfl fun y _ => ?_
        have hy := hpos y.1 y.2
        have hm : pos0 g input y.1 % g.T = pos0 g input y.1 := Nat.mod_eq_of_lt hy
        simp only [oP, hm]
        simp only [pos0, Nat.div_div_eq_div_mul]
      rw [h1, ← hKA]
      exact card_block (input.map Rec.key) hnd
        (g.C / 2 * 2 ^ (j + 1)) ((v : ℕ) / 2 ^ (j + 1)) (Nat.mul_pos h0 hb)
  have hr : (((Finset.univ.filter (fun y : L.Key => ((oP L (pos0 g input) y : Fin g.T) : ℕ) /
      2 ^ (j + 1) = (v : ℕ) / 2 ^ (j + 1))).card : ℕ) : ℝ≥0) * (1 / 2 ^ (j + 1)) ≤
      ((g.C / 2 : ℕ) : ℝ≥0) := by
    calc _ ≤ ((g.C / 2 * 2 ^ (j + 1) : ℕ) : ℝ≥0) * (1 / 2 ^ (j + 1)) := by
          gcongr
      _ = _ := by push_cast; field_simp
  exact hr

theorem pos0_lt (input : List Rec) (hKA : (input.map Rec.key).toFinset = L.KA)
    (hlen : input.length ≤ g.C / 2 * g.T) : ∀ x ∈ L.KA, pos0 g input x < g.T := by
  intro x hx
  rw [← hKA] at hx
  have hx' := List.mem_toFinset.mp hx
  have hlt : (input.map Rec.key).idxOf x < input.length := by
    simpa using List.idxOf_lt_length_iff.mpr hx'
  unfold pos0
  rcases Nat.eq_zero_or_pos (g.C / 2) with h0 | h0
  · rw [h0] at hlen; omega
  · rw [Nat.div_lt_iff_lt_mul h0]; rw [mul_comm] at hlen; omega

theorem init_stash (input : List Rec) (hL : InitLaw L input) {j : ℕ} (hj : j < g.k)
    (C S K' : ℕ) (hS : S < K')
    (E : L.Hist → (Model.LogicalKey → ℕ) → Prop)
    (hE : ∀ hist h, E hist (L.wordFn h) → 1 ≤ restrictedStopLoss (Finset.univ : Finset (Fin g.T))
      C S (∑ y, unitVec (dst g L.W j hj (oP L (pos0 g input) y) (h y)))) :
    L.prob E ≤ ENNReal.ofReal (Phi K' g.T C ((g.C / 2 : ℕ) : ℝ) S) := by
  classical
  have hW : g.k ≤ L.W := hL.wide
  have hlen := hL.count
  have hT : Nonempty (Fin (2 ^ L.W)) := ⟨⟨0, by positivity⟩⟩
  let F : (Fin g.T → ℕ) → ℝ≥0∞ := restrictedStopLoss (Finset.univ : Finset (Fin g.T)) C S
  let n := Fintype.card L.Key
  let e : L.Key ≃ Fin n := Fintype.equivFin L.Key
  let d : Fin n → Fin (2 ^ L.W) → Fin g.T := fun i a =>
    dst g L.W j hj (oP L (pos0 g input) (e.symm i)) a
  refine le_trans (FiniteLawProof.prob_le_avg_of L.prob_eq hL.weight_sum E
    (fun h => F (∑ y, unitVec (dst g L.W j hj (oP L (pos0 g input) y) (h y)))) hE) ?_
  have hb := bridgeV (κ := Fin g.T) (A := Fin (2 ^ L.W)) n d F
  have heq : (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h : L.Key → Fin (2 ^ L.W),
        F (∑ y, unitVec (dst g L.W j hj (oP L (pos0 g input) y) (h y))) =
      ∫⁻ y, F y ∂(convList (List.ofFn fun i => unitLaw (law (d i)))) := by
    rw [hb, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    congr 1
    refine Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl _)) _ _ ?_
    intro h
    congr 1
    simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, d,
      Equiv.symm_symm, Equiv.symm_apply_apply]
    exact (Equiv.sum_comp e (fun i : Fin n => unitVec (dst g L.W j hj
      (oP L (pos0 g input) (e.symm i)) (h (e.symm i))))).symm.trans (by
        refine Finset.sum_congr rfl fun y _ => ?_
        simp) |>.symm
  rw [heq]
  have hP8 := RebuildBound.P8c (Finset.univ : Finset (Fin g.T)) C S ((g.C / 2 : ℕ) : ℝ≥0)
    (List.ofFn fun i => law (d i)) ?_ ?_
  · rw [List.map_ofFn] at hP8
    have h7 := RebuildBound.P7 (Finset.univ : Finset (Fin g.T)) C S K' ((g.C / 2 : ℕ) : ℝ≥0) hS
    rw [Finset.card_univ, Fintype.card_fin] at h7
    exact le_trans hP8 h7
  · intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact sum_law _
  · intro v
    rw [List.map_ofFn, List.sum_ofFn]
    have := mean_bound L input hL.nodup hL.keys hlen hW hj v
    refine le_trans (le_of_eq ?_) this
    exact Equiv.sum_comp e.symm (fun y => law (dst g L.W j hj (oP L (pos0 g input) y)) v)

end RebuildBound.TG1Proof
