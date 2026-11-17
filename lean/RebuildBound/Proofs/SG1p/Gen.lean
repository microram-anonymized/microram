import RebuildBound.Proofs.SG1p.Conv
import RebuildBound.Proofs.P7fin
import RebuildBound.Proofs.P8a

/-!
# SG1p: the generic stop-loss term

For a fixed key set `K`, a per-key state `s hist x ∈ Fin M` (the old home) with density `D`
against uniform, and a per-key destination `φ (s x) (word x)` in a finite set `ι`, the
probability that the excess of the destination counts exceeds `S` is at most
`D c^|K| Φ_{K'}`, where the destination law is at most `c` times a law `q` with masses at most
`p*` and `|K| p* ≤ λ` (density step, then P8a, then P7).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.SG1pProof

open RebuildBound.Model RebuildBound.Spec RebuildBound.P11dProof RebuildBound.G3Proof

variable {g : SepGeom} (L : SJobLaw g)

/-- The keys of `K` as a subtype of the union's key type. -/
def subKeyEquiv (K : Finset Model.LogicalKey) (hK : K ⊆ L.KA ∪ L.KB) : {y : L.Key // y.1 ∈ K} ≃ K where
  toFun y := ⟨y.1.1, y.2⟩
  invFun x := ⟨⟨x.1, hK x.2⟩, x.2⟩
  left_inv y := rfl
  right_inv x := rfl

theorem avg_sub (K : Finset Model.LogicalKey) (hK : K ⊆ L.KA ∪ L.KB)
    (G : (K → Fin (2 ^ L.W)) → ℝ≥0∞) :
    (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h : L.Key → Fin (2 ^ L.W), G (fun x : K => h ⟨x.1, hK x.2⟩) =
    (Fintype.card (K → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ * ∑ γ, G γ := by
  classical
  have := avg_restrict (Y := L.Key) (A := Fin (2 ^ L.W)) (fun y : L.Key => y.1 ∈ K)
    (fun g' => G (fun x : K => g' ⟨⟨x.1, hK x.2⟩, x.2⟩))
  simp only at this
  rw [this]
  have hc : Fintype.card ({y : L.Key // y.1 ∈ K} → Fin (2 ^ L.W)) =
      Fintype.card (K → Fin (2 ^ L.W)) :=
    Fintype.card_congr (Equiv.arrowCongr (subKeyEquiv L K hK) (Equiv.refl _))
  rw [hc]
  congr 1
  exact Fintype.sum_equiv (Equiv.arrowCongr (subKeyEquiv L K hK) (Equiv.refl _)) _ _
    (fun g' => rfl)

theorem density_fiber {I : Type} [Fintype I] [DecidableEq I] {M : ℕ} (Hist : Type) [Fintype Hist] [DecidableEq Hist]
    (w : Hist → ℝ≥0∞) (s : Hist → (I → Fin M)) (D : ℝ≥0∞)
    (hdens : ∀ o : I → Fin M,
      (∑ hist ∈ Finset.univ.filter (fun hist => s hist = o), w hist) ≤ D / (M : ℝ≥0∞) ^ Fintype.card I)
    (Av : (I → Fin M) → ℝ≥0∞) :
    ∑ hist, w hist * Av (s hist) ≤ D / (M : ℝ≥0∞) ^ Fintype.card I * ∑ o, Av o := by
  rw [← Finset.sum_fiberwise Finset.univ s]
  calc ∑ o, ∑ hist ∈ Finset.univ.filter (fun hist => s hist = o), w hist * Av (s hist)
      = ∑ o, (∑ hist ∈ Finset.univ.filter (fun hist => s hist = o), w hist) * Av o := by
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun hist hh => ?_
        rw [(Finset.mem_filter.mp hh).2]
    _ ≤ ∑ o, (D / (M : ℝ≥0∞) ^ Fintype.card I) * Av o := by
        gcongr with o _
        exact hdens o
    _ = _ := by rw [Finset.mul_sum]


/-- **The generic term.** -/
theorem gen_bound (hw : ∑ hist, L.weight hist = 1)
    (K : Finset Model.LogicalKey) (hK : K ⊆ L.KA ∪ L.KB) {M : ℕ} (hM : 0 < M)
    (s : L.Hist → (K → Fin M)) (D : ℝ≥0)
    (hdens : ∀ o : K → Fin M,
      (∑ hist ∈ Finset.univ.filter (fun hist => s hist = o), L.weight hist) ≤
        (D : ℝ≥0∞) / (M : ℝ≥0∞) ^ K.card)
    {ι : Type} [Fintype ι] [DecidableEq ι] (φ : Fin M → Fin (2 ^ L.W) → ι)
    (c : ℝ≥0) (q : ι → ℝ≥0) (hq1 : ∑ v, q v = 1)
    (hlaw : ∀ v, law (fun p : Fin M × Fin (2 ^ L.W) => φ p.1 p.2) v ≤ c * q v)
    (pstar lam : ℝ≥0) (hqp : ∀ v, q v ≤ pstar) (hload : (K.card : ℝ≥0) * pstar ≤ lam)
    (C S K' : ℕ) (hSK : S < K') (E : L.Hist → (Model.LogicalKey → ℕ) → Prop)
    (hE : ∀ hist h, E hist (L.wordFn h) →
      S < ∑ v, ((∑ x : K, unitVec (φ (s hist x) (h ⟨x.1, hK x.2⟩))) v - C)) :
    L.prob E ≤ (D : ℝ≥0∞) * (c : ℝ≥0∞) ^ K.card *
      ENNReal.ofReal (Phi K' (Fintype.card ι) C lam S) := by
  classical
  have hn : Fintype.card K = K.card := Fintype.card_coe K
  haveI : Nonempty (Fin M × Fin (2 ^ L.W)) := ⟨(⟨0, hM⟩, ⟨0, by positivity⟩)⟩
  set F : (ι → ℕ) → ℝ≥0∞ := restrictedStopLoss (Finset.univ : Finset ι) C S with hF
  set d : Fin M × Fin (2 ^ L.W) → ι := fun p => φ p.1 p.2 with hd
  let Av : (K → Fin M) → ℝ≥0∞ := fun o =>
    (Fintype.card (K → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ γ : K → Fin (2 ^ L.W), F (∑ x : K, unitVec (φ (o x) (γ x)))
  have hA : L.prob E ≤ ∑ hist, L.weight hist * Av (s hist) := by
    unfold SJobLaw.prob
    gcongr with hist _
    have := avg_sub L K hK (fun γ => F (∑ x : K, unitVec (φ (s hist x) (γ x))))
    simp only at this
    show _ ≤ (Fintype.card (K → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ γ : K → Fin (2 ^ L.W), F (∑ x : K, unitVec (φ (s hist x) (γ x)))
    rw [← this]
    gcongr with h _
    split_ifs with h1
    · have := hE hist h h1
      rw [hF]
      unfold restrictedStopLoss
      refine Nat.one_le_cast.mpr ?_
      omega
    · exact zero_le
  have hdens' : ∀ o : K → Fin M,
      (∑ hist ∈ Finset.univ.filter (fun hist => s hist = o), L.weight hist) ≤
        (D : ℝ≥0∞) / (M : ℝ≥0∞) ^ Fintype.card K := by
    rw [hn]; exact hdens
  have hB := density_fiber (I := K) (M := M) L.Hist L.weight s D hdens' Av
  have hC : (D : ℝ≥0∞) / (M : ℝ≥0∞) ^ Fintype.card K * ∑ o, Av o =
      (D : ℝ≥0∞) * ∫⁻ y, F y ∂(convList (List.replicate (Fintype.card K)
        (unitLaw (law d)))) := by
    rw [bridge_fin (ι := K) d F]
    let e := Equiv.arrowProdEquivProdArrow K (fun _ => Fin M) (fun _ => Fin (2 ^ L.W))
    have hs : ∑ δ : K → Fin M × Fin (2 ^ L.W), F (∑ i, unitVec (d (δ i))) =
        ∑ o : K → Fin M, ∑ γ : K → Fin (2 ^ L.W), F (∑ x : K, unitVec (φ (o x) (γ x))) := by
      rw [← Fintype.sum_prod_type']
      exact Fintype.sum_equiv e _ _ (fun δ => rfl)
    rw [hs]
    simp only [Av]
    rw [← Finset.mul_sum]
    have hcA : Fintype.card (Fin M × Fin (2 ^ L.W)) = M * 2 ^ L.W := by simp
    have hcW : Fintype.card (K → Fin (2 ^ L.W)) = (2 ^ L.W) ^ K.card := by simp
    rw [hcA, hcW, hn]
    push_cast
    rw [mul_pow, ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp)), ENNReal.div_eq_inv_mul]
    ring
  have hD : (D : ℝ≥0∞) * ∫⁻ y, F y ∂(convList (List.replicate (Fintype.card K)
        (unitLaw (law d)))) ≤ (D : ℝ≥0∞) * ((c : ℝ≥0∞) ^ K.card *
      ENNReal.ofReal (Phi K' (Fintype.card ι) C lam S)) := by
    gcongr
    rw [hn]
    refine le_trans (conv_compare (law d) q c (sum_law d) hq1 hlaw K.card F) ?_
    gcongr
    have h8 := RebuildBound.P8a (Finset.univ : Finset ι) C S pstar lam
      (List.replicate K.card q) ?_ ?_ ?_
    · rw [List.map_replicate] at h8
      refine le_trans h8 ?_
      have := RebuildBound.P7 (Finset.univ : Finset ι) C S K' lam hSK
      rwa [Finset.card_univ] at this
    · intro p hp
      rw [List.eq_of_mem_replicate hp]; exact hq1
    · intro p hp v
      rw [List.eq_of_mem_replicate hp]; exact hqp v
    · simpa using hload
  calc L.prob E ≤ _ := hA
    _ ≤ _ := hB
    _ = _ := hC
    _ ≤ _ := hD
    _ = _ := by ring

end RebuildBound.SG1pProof
