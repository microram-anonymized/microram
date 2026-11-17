import RebuildBound.Proofs.NativeMatch.Rule
import RebuildBound.Proofs.NativeMatch.Union

/-!
# False matches under a uniform permutation

At exactly sixteen bytes the stored key is one ideal block-cipher permutation
`σ` of the key block. Fix a comparison whose subject `x` is not a partner and
condition on the images `f` of the `k` distinct partners. Every permutation
with those images sends `x` outside them, and swapping two values outside the
images is a bijection between the fibres, so `σ x` is uniform on the other
`N - k` words. The cover set `T f` contains the `k` partner images and has at
most `M` points, so the conditional probability is `(|T f| - k) / (N - k)`,
which is at most `M / N` whenever `M ≤ N`. `NativeMatch/Union.lean` then gives
the list and environment bounds, as for the random function; every event is
measurable because permutations carry the discrete σ-algebra.
-/
namespace RebuildBound
open Spec Spec.NativeMatch Spec.NativeNormalize MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace NativeMatchProof

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Permutations agreeing with `f` on `S` and sending `x` to `y`. -/
def permFiber (S : Finset α) (x : α) (f : S → α) (y : α) : Finset (Equiv.Perm α) :=
  univ.filter fun σ => (fun q : S => σ q) = f ∧ σ x = y

/-- Swapping two values outside the image of `f` matches the fibres. -/
theorem permFiber_card_swap (S : Finset α) (x : α) (f : S → α) (y y' : α)
    (hy : ∀ q, f q ≠ y) (hy' : ∀ q, f q ≠ y') :
    (permFiber S x f y).card = (permFiber S x f y').card := by
  have hmaps : ∀ {a b : α}, (∀ q, f q ≠ a) → (∀ q, f q ≠ b) → ∀ σ ∈ permFiber S x f a,
      Equiv.swap a b * σ ∈ permFiber S x f b := by
    intro a b ha hb σ hσ
    simp only [permFiber, mem_filter, mem_univ, true_and] at hσ ⊢
    obtain ⟨hf, hx⟩ := hσ
    refine ⟨?_, by simp [hx]⟩
    funext q
    have hq : σ q = f q := congrFun hf q
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, hq]
    exact Equiv.swap_apply_of_ne_of_ne (ha q) (hb q)
  refine card_nbij' (fun σ => Equiv.swap y y' * σ) (fun σ => Equiv.swap y y' * σ)
    (fun σ hσ => hmaps hy hy' σ hσ) (fun σ hσ => ?_) ?_ ?_
  · rw [Equiv.swap_comm]
    exact hmaps hy' hy σ hσ
  · intro σ _
    simp [Equiv.swap_mul_self_mul]
  · intro σ _
    simp [Equiv.swap_mul_self_mul]

/-- Counting form of the conditional bound: if `x ∉ S` and the target set
`T f` contains the images of `S` and has at most `M ≤ N` points, then at most
a fraction `M / N` of all permutations send `x` into `T`. -/
theorem perm_count (S : Finset α) (x : α) (hx : x ∉ S)
    (T : (S → α) → Finset α) (M : Nat) (hT : ∀ f, (T f).card ≤ M)
    (hR : ∀ f (q : S), f q ∈ T f) (hM : M ≤ Fintype.card α) :
    Fintype.card α * (univ.filter fun σ : Equiv.Perm α => σ x ∈ T (fun q : S => σ q)).card ≤
      M * (Fintype.card α).factorial := by
  set N := Fintype.card α
  let A : (S → α) → Finset (Equiv.Perm α) := fun f =>
    univ.filter fun σ => (fun q : S => σ q) = f
  have hsumE : (univ.filter fun σ : Equiv.Perm α => σ x ∈ T (fun q : S => σ q)).card =
      ∑ f, ((A f).filter fun σ => σ x ∈ T f).card := by
    rw [card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm α => fun q : S => σ q)
      (t := univ) (fun _ _ => mem_coe.mpr (mem_univ _))]
    refine sum_congr rfl fun f _ => ?_
    congr 1
    ext σ
    simp only [mem_filter, mem_univ, true_and, A]
    constructor
    · rintro ⟨h1, rfl⟩
      exact ⟨rfl, h1⟩
    · rintro ⟨rfl, h1⟩
      exact ⟨h1, rfl⟩
  have hsumA : N.factorial = ∑ f, (A f).card := by
    rw [← Fintype.card_perm, ← card_univ,
      card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm α => fun q : S => σ q)
      (t := univ) (fun _ _ => mem_coe.mpr (mem_univ _))]
  have hper : ∀ f, N * ((A f).filter fun σ => σ x ∈ T f).card ≤ M * (A f).card := by
    intro f
    by_cases hA : (A f).Nonempty
    swap
    · rw [not_nonempty_iff_eq_empty.mp hA]
      simp
    obtain ⟨σ0, hσ0⟩ := hA
    have hf0 : (fun q : S => σ0 q) = f := by simpa [A] using hσ0
    let R : Finset α := univ.image f
    have hRcard : R.card = S.card := by
      rw [card_image_of_injective _ (by
        intro a b hab
        rw [← hf0] at hab
        exact Subtype.ext (σ0.injective hab)), card_univ, Fintype.card_coe]
    have hRT : R ⊆ T f := by
      intro y hy
      obtain ⟨q, _, rfl⟩ := mem_image.mp hy
      exact hR f q
    -- every permutation in `A f` sends `x` outside the partner images
    have hout : ∀ σ ∈ A f, σ x ∉ R := by
      intro σ hσ hmem
      obtain ⟨q, _, hq⟩ := mem_image.mp hmem
      have hσf : (fun q : S => σ q) = f := by simpa [A] using hσ
      rw [← hσf] at hq
      exact hx (σ.injective hq ▸ q.property)
    let y0 := σ0 x
    have hy0 : ∀ q, f q ≠ y0 := fun q h => hout σ0 hσ0 (mem_image.mpr ⟨q, mem_univ _, h⟩)
    let c := (permFiber S x f y0).card
    have hfib : ∀ y, y ∉ R → (permFiber S x f y).card = c := by
      intro y hy
      exact permFiber_card_swap S x f y y0
        (fun q h => hy (mem_image.mpr ⟨q, mem_univ _, h⟩)) hy0
    have hfibR : ∀ y, y ∈ R → (permFiber S x f y).card = 0 := by
      intro y hy
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro σ hσ
      simp only [permFiber, mem_filter, mem_univ, true_and] at hσ
      exact hout σ (by simp [A, hσ.1]) (hσ.2 ▸ hy)
    -- decompose `A f` and its filtered part by the image of `x`
    have hdecomp : ∀ U : Finset α, ((A f).filter fun σ => σ x ∈ U).card =
        ∑ y ∈ U, (permFiber S x f y).card := by
      intro U
      rw [card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm α => σ x) (t := U)
        (fun σ hσ => by simpa using (mem_filter.mp hσ).2)]
      refine sum_congr rfl fun y _ => ?_
      congr 1
      ext σ
      simp only [permFiber, A, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, rfl⟩
        exact ⟨⟨h1, by assumption⟩, rfl⟩
    have hsplit : ∀ U : Finset α, ∑ y ∈ U, (permFiber S x f y).card = (U \ R).card * c := by
      intro U
      rw [← sum_sdiff (s₁ := U ∩ R) (s₂ := U) inter_subset_left]
      rw [sum_eq_zero (fun y hy => hfibR y (mem_inter.mp hy).2), add_zero,
        sum_congr (s₂ := U \ (U ∩ R)) rfl (fun y hy => hfib y (by
          intro h
          exact (mem_sdiff.mp hy).2 (mem_inter.mpr ⟨(mem_sdiff.mp hy).1, h⟩))),
        sum_const, Nat.nsmul_eq_mul, sdiff_inter_self_left]
    have hAf : (A f).card = (N - S.card) * c := by
      have := hdecomp univ
      rw [show ((A f).filter fun σ => σ x ∈ (univ : Finset α)) = A f by simp] at this
      rw [this, hsplit, ← hRcard, card_sdiff_of_subset (subset_univ _), card_univ]
    have hEf : ((A f).filter fun σ => σ x ∈ T f).card = ((T f).card - S.card) * c := by
      rw [hdecomp, hsplit, card_sdiff_of_subset hRT, hRcard]
    rw [hAf, hEf]
    have hTk : (T f).card - S.card ≤ M - S.card := Nat.sub_le_sub_right (hT f) _
    calc N * (((T f).card - S.card) * c) ≤ N * ((M - S.card) * c) := by gcongr
      _ = (N * (M - S.card)) * c := by ring
      _ ≤ (M * (N - S.card)) * c := by
          refine Nat.mul_le_mul_right c ?_
          rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_comm N M]
          exact Nat.sub_le_sub_left (Nat.mul_le_mul_right _ hM) _
      _ = M * ((N - S.card) * c) := by ring
  rw [hsumE, mul_sum, hsumA, mul_sum]
  exact sum_le_sum fun f _ => hper f

/-- One comparison under a uniform permutation, subject absent from partners. -/
theorem perm_comparison_le (count width : Nat) (x : Fingerprint (width * count))
    (P : List (Fingerprint (width * count))) (hx : x ∉ P) :
    permLaw (width * count) {σ | segMatch (σ x) (P.map σ)} ≤
      ((P.length ^ count : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (width * count) := by
  classical
  set N := Fintype.card (Fingerprint (width * count)) with hN
  have hN' : (N : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (width * count) := by simp [hN, Fingerprint]
  let S := P.toFinset
  have hxS : x ∉ S := fun h => hx (List.mem_toFinset.mp h)
  let T : (S → Fingerprint (width * count)) → Finset (Fingerprint (width * count)) :=
    fun f => univ.filter fun v => ∀ s, ∃ q : S, keySegment (f q) s = keySegment v s
  let M := min (S.card ^ count) N
  have hT : ∀ f, (T f).card ≤ M := fun f =>
    le_min ((card_box_image_le count width f).trans_eq (by rw [Fintype.card_coe]))
      (card_le_univ _)
  have hR : ∀ f (q : S), f q ∈ T f := fun f q => by
    simp only [T, mem_filter, mem_univ, true_and]
    exact fun s => ⟨q, rfl⟩
  have hcount := perm_count S x hxS T M hT hR (min_le_right _ _)
  have hset : {σ : Equiv.Perm (Fingerprint (width * count)) | segMatch (σ x) (P.map σ)} =
      ↑(univ.filter fun σ : Equiv.Perm (Fingerprint (width * count)) =>
        σ x ∈ T (fun q : S => σ q)) := by
    ext σ
    simp only [segMatch, List.mem_map, coe_filter, mem_filter, mem_univ, true_and,
      Set.mem_ofPred_eq, T, S]
    constructor
    · intro h s
      obtain ⟨_, ⟨p, hp, rfl⟩, he⟩ := h s
      exact ⟨⟨p, List.mem_toFinset.mpr hp⟩, he⟩
    · intro h s
      obtain ⟨⟨p, hp⟩, he⟩ := h s
      exact ⟨σ p, ⟨p, List.mem_toFinset.mp hp, rfl⟩, he⟩
  rw [hset, permLaw, uniformOn_univ, Measure.count_apply_finset, Fintype.card_perm, ← hN]
  set E := (univ.filter fun σ : Equiv.Perm (Fingerprint (width * count)) =>
    σ x ∈ T (fun q : S => σ q)).card
  have hc : (N : ℝ≥0∞) * E ≤ M * N.factorial := by exact_mod_cast hcount
  have hM : (M : ℝ≥0∞) ≤ ((P.length ^ count : Nat) : ℝ≥0∞) := Nat.cast_le.mpr
    ((min_le_left _ _).trans (Nat.pow_le_pow_left (List.toFinset_card_le P) _))
  -- clear the denominators with `N * N!`, then use `M ≤ partners ^ count`
  calc (E : ℝ≥0∞) / N.factorial = N * E / (N * N.factorial) :=
        (ENNReal.mul_div_mul_left _ _ (by simp [hN']) (by simp)).symm
    _ ≤ M * N.factorial / (N * N.factorial) := ENNReal.div_le_div_right hc _
    _ = M / N := ENNReal.mul_div_mul_right _ _ (by simp [Nat.factorial_ne_zero]) (by simp)
    _ ≤ ((P.length ^ count : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (width * count) := by
        rw [hN']
        exact ENNReal.div_le_div_right hM _

end NativeMatchProof

open NativeMatchProof

theorem NativeMatchPermutation : NativeMatchPermutation_statement := by
  intro Env _ μ _ count width budget cmp hcmp hw
  exact env_le (permLaw (width * count)) count width (fun σ => ⇑σ)
    (perm_comparison_le count width) μ (fun _ => MeasurableSet.of_discrete) budget cmp hcmp hw

end RebuildBound
