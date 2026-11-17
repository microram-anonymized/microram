import RebuildBound.Spec.Prob.Trunc
import RebuildBound.Proofs.NTop.Sound
import Mathlib.MeasureTheory.Group.Convolution

/-!
# Point masses of the discrete laws (package NCA1)

On countable spaces with measurable singletons every law is determined by its
point masses. These lemmas compute the point masses of `bind`, `map`,
`restrict`, `thinPair`, and of convolutions on `ℕ` and `ℕ × ℕ`, and scale
the binomial and Poisson masses to natural numbers.
-/

open MeasureTheory ProbabilityTheory Finset RebuildBound.Spec
open scoped ENNReal NNReal unitInterval BigOperators

namespace RebuildBound.NCA1

section
variable {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  [MeasurableSpace β] [MeasurableSingletonClass β]
set_option linter.unusedSectionVars false

lemma bind_singleton (μ : Measure α) (κ : α → Measure β) (x : β) :
    (μ.bind κ) {x} = ∑' y, μ {y} * κ y {x} := by
  rw [Measure.bind_apply (measurableSet_singleton x) (Measurable.of_discrete).aemeasurable,
    lintegral_countable']
  exact tsum_congr fun y => mul_comm _ _

lemma bind_univ (μ : Measure α) (κ : α → Measure β) :
    (μ.bind κ) Set.univ = ∫⁻ y, κ y Set.univ ∂μ :=
  Measure.bind_apply MeasurableSet.univ (Measurable.of_discrete).aemeasurable

lemma map_singleton (μ : Measure α) (f : α → β) (x : β) : (μ.map f) {x} = μ (f ⁻¹' {x}) :=
  Measure.map_apply Measurable.of_discrete (measurableSet_singleton x)

lemma restrict_singleton (μ : Measure α) (s : Set α) (x : α) :
    (μ.restrict s) {x} = s.indicator (fun y => μ {y}) x := by
  rw [Measure.restrict_apply (measurableSet_singleton x)]
  by_cases h : x ∈ s
  · rw [Set.singleton_inter_of_mem h, Set.indicator_of_mem h]
  · rw [Set.singleton_inter_of_notMem h, measure_empty, Set.indicator_of_notMem h]

lemma measure_finset (μ : Measure α) (s : Finset α) : μ ↑s = ∑ x ∈ s, μ {x} :=
  (sum_measure_singleton (μ := μ)).symm

end

lemma prod_singleton {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν] (a : α) (b : β) :
    (μ.prod ν) {(a, b)} = μ {a} * ν {b} := by
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]

lemma thinPair_singleton (p : I) (y : ℕ × ℕ) (a b : ℕ) :
    thinPair p y {(a, b)} = binomial y.1 p {a} * binomial y.2 p {b} := by
  rw [Spec.thinPair, prod_singleton]

lemma thinPair_univ (p : I) (y : ℕ × ℕ) : thinPair p y Set.univ = 1 := by
  rw [Spec.thinPair, ← Set.univ_prod_univ, Measure.prod_prod, measure_univ, measure_univ, one_mul]

lemma conv_univ {M : Type*} [AddMonoid M] [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M]
    (μ ν : Measure M) [SFinite ν] : (μ ∗ ν) Set.univ = μ Set.univ * ν Set.univ := by
  rw [Measure.conv, Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod]

lemma conv_singleton_nat (μ ν : Measure ℕ) (n : ℕ) :
    (μ ∗ ν) {n} = ∑ ij ∈ antidiagonal n, μ {ij.1} * ν {ij.2} := by
  rw [Measure.conv, map_singleton]
  have : (fun x : ℕ × ℕ => x.1 + x.2) ⁻¹' {n} = ↑(antidiagonal n) := by
    ext ⟨i, j⟩; simp [mem_antidiagonal]
  rw [this, measure_finset]
  exact sum_congr rfl fun ij _ => prod_singleton μ ν ij.1 ij.2

lemma conv_singleton_pair (μ ν : Measure (ℕ × ℕ)) (u v : ℕ) :
    (μ ∗ ν) {(u, v)} = ∑ ij ∈ antidiagonal u, ∑ kl ∈ antidiagonal v,
      μ {(ij.1, kl.1)} * ν {(ij.2, kl.2)} := by
  rw [Measure.conv, map_singleton]
  let e : (ℕ × ℕ) × (ℕ × ℕ) → (ℕ × ℕ) × (ℕ × ℕ) := fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))
  have he : Function.Injective e := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ h
    simp only [e, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    subst h1 h2 h3 h4; rfl
  have hs : (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1 + x.2) ⁻¹' {(u, v)} =
      ↑((antidiagonal u ×ˢ antidiagonal v).image e) := by
    ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp only [Set.mem_preimage, Prod.mk_add_mk, Set.mem_singleton_iff, Prod.mk.injEq, coe_image,
      coe_product, Set.mem_image, Set.mem_prod, mem_coe, mem_antidiagonal, Prod.exists, e]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨a, c, b, d, ⟨h1, h2⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
    · rintro ⟨_, _, _, _, ⟨h1, h2⟩, ⟨rfl, rfl⟩, rfl, rfl⟩; exact ⟨h1, h2⟩
  rw [hs, measure_finset, sum_image he.injOn, sum_product]
  exact sum_congr rfl fun ij _ => sum_congr rfl fun kl _ => prod_singleton μ ν _ _

/-- `Bin(n, a/d){k} · d^n` is a natural number. -/
def thinCoef (a d n k : ℕ) : ℕ := n.choose k * a ^ k * (d - a) ^ (n - k)

lemma le_of_prob {p : I} {a d : ℕ} (hd : 0 < d) (hp : (p : ℝ) = a / d) : a ≤ d := by
  have h1 : (p : ℝ) ≤ 1 := p.2.2
  rw [hp, div_le_one (by exact_mod_cast hd)] at h1
  exact_mod_cast h1

lemma binom_scaled {p : I} {a d : ℕ} (hd : 0 < d) (hp : (p : ℝ) = a / d) (n k : ℕ) :
    binomial n p {k} * (d : ℝ≥0∞) ^ n = (thinCoef a d n k : ℝ≥0∞) := by
  have had := le_of_prob hd hp
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [binomial_singleton, ← ENNReal.ofReal_natCast d, ← ENNReal.ofReal_pow hd'.le,
    ← ENNReal.ofReal_mul binomial_nonneg, ← ENNReal.ofReal_natCast (thinCoef a d n k)]
  congr 1
  unfold thinCoef
  rw [hp]
  by_cases hk : k ≤ n
  · obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
    rw [Nat.add_sub_cancel_left]
    push_cast [Nat.cast_sub had]
    have h1 : (1 : ℝ) - a / d = (d - a) / d := by field_simp
    rw [pow_add, h1, div_pow, div_pow]
    field_simp
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma pois_scaled {lam : ℝ≥0} {a b D N r : ℕ} (hlam : (lam : ℝ) = a / b) (hD : 0 < D)
    (hb : 0 < b) (hr : 0 < r) (hL : 0 < NTop.lmNum D N r a b) (n : ℕ) :
    poissonMeasure lam {n} * D ≤ (NTop.pT D a b (NTop.eNum D N r a b) n : ℝ≥0∞) := by
  rw [poissonMeasure_singleton]
  have h := NTop.pT_ge hD hb hr (NTop.eNum_ge hD hb hr N hL) n
  rw [← hlam] at h
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  calc ENNReal.ofReal (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n.factorial : ℝ)) * D
      ≤ ENNReal.ofReal ((NTop.pT D a b (NTop.eNum D N r a b) n : ℝ) / D) * D := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_natCast D, ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hD'.ne',
        ENNReal.ofReal_natCast]

end RebuildBound.NCA1
