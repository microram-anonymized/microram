import RebuildBound.Proofs.SG1p.Gen

/-!
# SG1p: the count vectors as sums of unit vectors, and the ranges of the maps
-/

open scoped ENNReal NNReal

namespace RebuildBound.SG1pProof

open RebuildBound.Model RebuildBound.Spec RebuildBound.SG1Proof

/-- A clamped coercion into `Fin N`. -/
def dN (N : ℕ) (hN : 0 < N) (x : ℕ) : Fin N := if h : x < N then ⟨x, h⟩ else ⟨0, hN⟩

theorem dN_val (N : ℕ) (hN : 0 < N) (x : ℕ) (hx : x < N) : (dN N hN x : ℕ) = x := by
  simp [dN, hx]

theorem dN_eq_iff (N : ℕ) (hN : 0 < N) (x : ℕ) (hx : x < N) (v : Fin N) :
    dN N hN x = v ↔ x = (v : ℕ) := by
  rw [Fin.ext_iff, dN_val N hN x hx]

theorem countP_key (P : Model.LogicalKey → Bool) : ∀ (l : List Rec), (l.map Rec.key).Nodup →
    l.countP (fun r => P r.key) = ∑ x ∈ (l.map Rec.key).toFinset, if P x = true then 1 else 0
  | [], _ => by simp
  | r :: l, hl => by
    simp only [List.map_cons, List.nodup_cons] at hl
    rw [List.map_cons, List.toFinset_cons, Finset.sum_insert (by simpa using hl.1),
      List.countP_cons, countP_key P l hl.2]
    simp [add_comm]

theorem count_vec {N : ℕ} (hN : 0 < N) (l : List Rec) (hl : (l.map Rec.key).Nodup)
    (K : Finset Model.LogicalKey) (hK : (l.map Rec.key).toFinset = K) (f : Model.LogicalKey → ℕ) (hf : ∀ x ∈ K, f x < N)
    (v : Fin N) :
    l.countP (fun r => f r.key == (v : ℕ)) = (∑ x : K, unitVec (dN N hN (f x.1))) v := by
  rw [countP_key (fun x => f x == (v : ℕ)) l hl, hK, Finset.sum_apply,
    ← Finset.sum_coe_sort K]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [unitVec, Pi.single_apply]
  by_cases h : f x.1 = (v : ℕ)
  · have e : dN N hN (f x.1) = v := by
      rw [Fin.ext_iff, dN_val N hN _ (hf x.1 x.2), h]
    rw [if_pos (by simpa using h), if_pos e.symm]
  · have : ¬ v = dN N hN (f x.1) := by
      intro h'
      rw [Fin.ext_iff, dN_val N hN _ (hf x.1 x.2)] at h'
      exact h h'.symm
    simp [h, this]

theorem rd_lt (g : SepGeom) (hg : g.Valid) (j : ℕ) (hj : j < g.k) (o a : ℕ)
    (ho : o < (g.d - 1) * g.U) : G1Proof.rd g.U j o a < g.N := by
  unfold G1Proof.rd
  have hm : 0 < 2 ^ (j + 1) := by positivity
  obtain ⟨Q, hQ⟩ : 2 ^ (j + 1) ∣ g.N := by
    unfold SepGeom.N
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 hj) _
  have hd := hg.2.1
  have hUo : g.U + o < g.N := by
    rw [N_eq]
    have : g.d * g.U = g.U + (g.d - 1) * g.U := by
      obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (show 1 ≤ g.d by omega)
      rw [he]; simp [Nat.add_mul]
    omega
  have h1 : (g.U + o) / 2 ^ (j + 1) < Q := Nat.div_lt_of_lt_mul (by rw [← hQ]; exact hUo)
  have h2 := Nat.mod_lt a hm
  calc 2 ^ (j + 1) * ((g.U + o) / 2 ^ (j + 1)) + a % 2 ^ (j + 1)
      < 2 ^ (j + 1) * ((g.U + o) / 2 ^ (j + 1)) + 2 ^ (j + 1) := by omega
    _ = 2 ^ (j + 1) * ((g.U + o) / 2 ^ (j + 1) + 1) := by ring
    _ ≤ 2 ^ (j + 1) * Q := Nat.mul_le_mul_left _ h1
    _ = g.N := hQ.symm

theorem homeOf_lt (g : SepGeom) (hr : 0 < g.r) (t : ℕ) : g.homeOf t < g.N := by
  unfold SepGeom.homeOf SepGeom.cls SepGeom.N
  have hP : 0 < 2 ^ g.k := by positivity
  have h1 := Nat.mod_lt t hP
  have h2 := Nat.mod_lt (t / 2 ^ g.k) hr
  calc t % 2 ^ g.k + 2 ^ g.k * (t / 2 ^ g.k % g.r)
      < 2 ^ g.k + 2 ^ g.k * (t / 2 ^ g.k % g.r) := by omega
    _ = 2 ^ g.k * (t / 2 ^ g.k % g.r + 1) := by ring
    _ ≤ 2 ^ g.k * g.r := Nat.mul_le_mul_left _ h2
    _ = g.r * 2 ^ g.k := by ring

theorem N_pos (g : SepGeom) (hg : g.Valid) : 0 < g.N := by
  unfold SepGeom.N
  have := hg.1
  positivity

end RebuildBound.SG1pProof
