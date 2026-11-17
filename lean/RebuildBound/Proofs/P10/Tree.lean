import RebuildBound.Proofs.P10.Poisson
import RebuildBound.Proofs.ShadowLaw.Tree

/-!
# P10: the shadow tree and its truncation

* `shadowTree_tot`: every node total is `Po(λ)`: caps preserve totals, thinning both
  counts by `p` thins the total (`binomial_conv`), a thinned `Po(λ)` is `Po(λ p)`
  (`poisson_bind_binomial`), and two independent `Po(λ/2)` add to `Po(λ)`.
* `truncTree_le`: `truncTree C λ H t ≤ shadowTree C λ t`.
* `truncTree_mass`: `1 ≤ mass(truncTree t) + (2^t - 1) P(Po(λ) > H)`. The convolution
  of two copies of the truncated child loses `1 - a²` of mass, at most `2 (1 - a)`, and
  the restriction at the new node removes at most `P(Po(λ) > H)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P10Proof

open RebuildBound.Spec RebuildBound.P11eProof

/-- The total `M + R` of a node state. -/
def tot (s : ℕ × ℕ) : ℕ := s.1 + s.2

lemma tot_capPair (C : ℕ) (s : ℕ × ℕ) : tot (capPair C s) = tot s := by
  simp only [tot, capPair]
  omega

/-! ### Measure-level helpers on the discrete state space -/

lemma map_bind_nat (μ : Measure (ℕ × ℕ)) (κ : ℕ × ℕ → Measure (ℕ × ℕ)) (f : ℕ × ℕ → ℕ) :
    (μ.bind κ).map f = μ.bind (fun a => (κ a).map f) := by
  ext s hs
  rw [Measure.map_apply Measurable.of_discrete hs,
    Measure.bind_apply (Measurable.of_discrete hs) Measurable.of_discrete.aemeasurable,
    Measure.bind_apply hs Measurable.of_discrete.aemeasurable]
  refine lintegral_congr fun a => ?_
  rw [Measure.map_apply Measurable.of_discrete hs]

lemma bind_map_nat (μ : Measure (ℕ × ℕ)) (f : ℕ × ℕ → ℕ) (κ : ℕ → Measure ℕ) :
    (μ.map f).bind κ = μ.bind (fun a => κ (f a)) := by
  ext s hs
  rw [Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
    Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
    lintegral_map Measurable.of_discrete Measurable.of_discrete]

lemma bind_mono_left {μ ν : Measure (ℕ × ℕ)} (h : μ ≤ ν) (κ : ℕ × ℕ → Measure (ℕ × ℕ)) :
    μ.bind κ ≤ ν.bind κ := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
    Measure.bind_apply hs Measurable.of_discrete.aemeasurable]
  exact lintegral_mono' h le_rfl

lemma conv_mono' {μ μ' ν ν' : Measure (ℕ × ℕ)} [SFinite ν'] (h1 : μ ≤ μ') (h2 : ν ≤ ν') :
    μ ∗ ν ≤ μ' ∗ ν' :=
  Measure.map_mono (Measure.prod_mono h1 h2) Measurable.of_discrete

lemma bind_thinPair_univ (μ : Measure (ℕ × ℕ)) (p : I) :
    (μ.bind (thinPair p)) Set.univ = μ Set.univ := by
  rw [Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable]
  simp

lemma conv_univ (μ ν : Measure (ℕ × ℕ)) [SFinite ν] :
    (μ ∗ ν) Set.univ = μ Set.univ * ν Set.univ := by
  rw [Measure.conv, Measure.map_apply Measurable.of_discrete MeasurableSet.univ,
    Set.preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod]

lemma isFinite_bind_thinPair (μ : Measure (ℕ × ℕ)) [IsFiniteMeasure μ] (p : I) :
    IsFiniteMeasure (μ.bind (thinPair p)) :=
  ⟨by rw [bind_thinPair_univ]; exact measure_lt_top μ _⟩

/-! ### Totals -/

lemma thinPair_map_tot (p : I) (s : ℕ × ℕ) : (thinPair p s).map tot = binomial (tot s) p :=
  binomial_conv s.1 s.2 p

lemma thin_tot (μ : Measure (ℕ × ℕ)) (r : ℝ≥0) (h : μ.map tot = poissonMeasure r) (p : I) :
    (μ.bind (thinPair p)).map tot = poissonMeasure (r * pNN p) := by
  rw [map_bind_nat]
  simp_rw [thinPair_map_tot]
  rw [← bind_map_nat μ tot (fun n => binomial n p), h, poisson_bind_binomial]

/-- The total as an additive monoid hom. -/
def totHom : ℕ × ℕ →+ ℕ := AddMonoidHom.coprod (AddMonoidHom.id ℕ) (AddMonoidHom.id ℕ)

lemma conv_map_tot (μ ν : Measure (ℕ × ℕ)) [SFinite μ] [SFinite ν] :
    (μ ∗ ν).map tot = μ.map tot ∗ ν.map tot :=
  Measure.map_conv_addMonoidHom totHom Measurable.of_discrete

lemma shadowTree_tot (C : ℕ) (lam : ℝ≥0) :
    ∀ t, 1 ≤ t → (shadowTree C lam t).map tot = poissonMeasure lam
  | 0, h => absurd h (by norm_num)
  | 1, _ => by
    rw [shadowTree, Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    have : tot ∘ (fun n => capPair C (n, 0)) = id := by
      funext n
      simp only [Function.comp, tot, capPair, id]
      omega
    rw [this, Measure.map_id]
  | t + 2, _ => by
    have ih := shadowTree_tot C lam (t + 1) (by omega)
    have := isProb_shadowTree C lam (t + 1)
    rw [shadowTree, Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    have hc : tot ∘ capPair C = tot := funext (tot_capPair C)
    rw [hc, conv_map_tot, thin_tot _ _ ih, poissonMeasure_conv_poissonMeasure]
    congr 1
    apply NNReal.eq
    rw [NNReal.coe_add]
    show (lam : ℝ) * (1 / 2) + (lam : ℝ) * (1 / 2) = lam
    ring

lemma shadowTree_high (C : ℕ) (lam : ℝ≥0) (H t : ℕ) (ht : 1 ≤ t) :
    shadowTree C lam t (lowTotal H)ᶜ = poissonMeasure lam {n | H < n} := by
  rw [← shadowTree_tot C lam t ht, Measure.map_apply Measurable.of_discrete (MeasurableSet.of_discrete)]
  congr 1
  ext s
  simp [lowTotal, tot]

/-- The second moment of a node total is at most `λ + λ²`. -/
lemma shadowTree_moment (C : ℕ) (lam : ℝ≥0) (t : ℕ) :
    ∫⁻ s, ((tot s : ℕ) : ℝ≥0∞) ^ 2 ∂(shadowTree C lam t) ≤ (lam : ℝ≥0∞) + (lam : ℝ≥0∞) ^ 2 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [shadowTree, lintegral_dirac, tot]
  · rw [← lintegral_map (f := fun n : ℕ => ((n : ℕ) : ℝ≥0∞) ^ 2) Measurable.of_discrete
      Measurable.of_discrete, shadowTree_tot C lam t ht, lintegral_sq_poisson]

/-! ### The truncated tree -/

lemma truncTree_le (C : ℕ) (lam : ℝ≥0) (H : ℕ) :
    ∀ t, truncTree C lam H t ≤ shadowTree C lam t
  | 0 => by rw [truncTree, shadowTree]
  | 1 => by
    rw [truncTree, shadowTree]
    exact Measure.restrict_le_self
  | t + 2 => by
    have h := truncTree_le C lam H (t + 1)
    have := isProb_shadowTree C lam (t + 1)
    rw [truncTree, shadowTree]
    refine Measure.restrict_le_self.trans (Measure.map_mono ?_ Measurable.of_discrete)
    exact conv_mono' (bind_mono_left h _) (bind_mono_left h _)

instance isFinite_truncTree (C : ℕ) (lam : ℝ≥0) (H t : ℕ) :
    IsFiniteMeasure (truncTree C lam H t) :=
  have := isProb_shadowTree C lam t
  isFiniteMeasure_of_le _ (truncTree_le C lam H t)

lemma truncTree_univ_le (C : ℕ) (lam : ℝ≥0) (H t : ℕ) : truncTree C lam H t Set.univ ≤ 1 := by
  have := isProb_shadowTree C lam t
  exact (truncTree_le C lam H t Set.univ).trans prob_le_one

lemma mass_aux {a b : ℝ≥0∞} (ha : a ≤ 1) (h : 1 ≤ a + b) : 1 ≤ a * a + 2 * b := by
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp
  lift a to ℝ≥0 using ne_top_of_le_ne_top ENNReal.one_ne_top ha
  lift b to ℝ≥0 using hb
  have ha' : (a : ℝ) ≤ 1 := by exact_mod_cast ha
  have h' : (1 : ℝ) ≤ a + b := by exact_mod_cast h
  have : (1 : ℝ) ≤ a * a + 2 * b := by nlinarith [a.2]
  have : (1 : ℝ≥0) ≤ a * a + 2 * b := by exact_mod_cast this
  exact_mod_cast this

/-- The truncated tree misses at most `(2^t - 1) P(Po(λ) > H)` of mass. -/
lemma truncTree_mass (C : ℕ) (lam : ℝ≥0) (H : ℕ) :
    ∀ t, 1 ≤ truncTree C lam H t Set.univ +
      ((2 ^ t - 1 : ℕ) : ℝ≥0∞) * poissonMeasure lam {n | H < n}
  | 0 => by simp [truncTree]
  | 1 => by
    have := isProb_shadowTree C lam 1
    have h1 : shadowTree C lam 1 (lowTotal H) + shadowTree C lam 1 (lowTotal H)ᶜ = 1 := by
      rw [measure_add_measure_compl MeasurableSet.of_discrete, measure_univ]
    rw [shadowTree_high C lam H 1 le_rfl] at h1
    have e : truncTree C lam H 1 = (shadowTree C lam 1).restrict (lowTotal H) := by
      rw [truncTree, shadowTree]
    rw [e, Measure.restrict_apply_univ, ← h1]
    simp
  | t + 2 => by
    have ih := truncTree_mass C lam H (t + 1)
    have hFp := isProb_shadowTree C lam (t + 1)
    set G := truncTree C lam H (t + 1) with hG
    set F := shadowTree C lam (t + 1) with hF
    set τ := poissonMeasure lam {n | H < n} with hτ
    set a := G Set.univ with ha
    set b := ((2 ^ (t + 1) - 1 : ℕ) : ℝ≥0∞) * τ with hb
    have hGF : G ≤ F := truncTree_le C lam H (t + 1)
    have ha1 : a ≤ 1 := truncTree_univ_le C lam H (t + 1)
    have hcG := isFinite_bind_thinPair G half
    set QG := (G.bind (thinPair half) ∗ G.bind (thinPair half)).map (capPair C) with hQG
    set QF := (F.bind (thinPair half) ∗ F.bind (thinPair half)).map (capPair C) with hQF
    have eG : truncTree C lam H (t + 2) = QG.restrict (lowTotal H) := by
      rw [truncTree]
    have eF : shadowTree C lam (t + 2) = QF := by
      rw [shadowTree]
    have hle : QG ≤ QF :=
      Measure.map_mono (conv_mono' (bind_mono_left hGF _) (bind_mono_left hGF _))
        Measurable.of_discrete
    have hQGu : QG Set.univ = a * a := by
      rw [hQG, Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ,
        conv_univ, bind_thinPair_univ]
    have hQFu : QF Set.univ = 1 := by
      rw [← eF]
      have := isProb_shadowTree C lam (t + 2)
      exact measure_univ
    have hQFc : QF (lowTotal H)ᶜ = τ := by
      rw [← eF]
      exact shadowTree_high C lam H (t + 2) (by omega)
    have hlow : MeasurableSet (lowTotal H) := MeasurableSet.of_discrete
    -- `QF low + QG univ ≤ QG low + QF univ`
    have key : QF (lowTotal H) + QG Set.univ ≤ QG (lowTotal H) + QF Set.univ := by
      rw [← measure_add_measure_compl (μ := QG) hlow, ← measure_add_measure_compl (μ := QF) hlow]
      calc QF (lowTotal H) + (QG (lowTotal H) + QG (lowTotal H)ᶜ)
          = QG (lowTotal H) + (QF (lowTotal H) + QG (lowTotal H)ᶜ) := by ring
        _ ≤ QG (lowTotal H) + (QF (lowTotal H) + QF (lowTotal H)ᶜ) := by
          gcongr
    have hsplit : QF (lowTotal H) + τ = 1 := by
      rw [← hQFc, measure_add_measure_compl hlow, hQFu]
    rw [hQGu, hQFu] at key
    rw [eG, Measure.restrict_apply_univ]
    have hab := mass_aux ha1 ih
    have hnat : (2 ^ (t + 2) - 1 : ℕ) = 2 * (2 ^ (t + 1) - 1) + 1 := by
      have := Nat.one_le_two_pow (n := t + 1)
      rw [pow_succ 2 (t + 1)]
      omega
    rw [hnat, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    refine (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 ?_
    calc 1 + 1 ≤ (QF (lowTotal H) + τ) + (a * a + 2 * b) := by
          rw [hsplit]
          gcongr
      _ = (QF (lowTotal H) + a * a) + (τ + 2 * b) := by ring
      _ ≤ (QG (lowTotal H) + 1) + (τ + 2 * b) := by gcongr
      _ = QG (lowTotal H) + (2 * ((2 ^ (t + 1) - 1 : ℕ) : ℝ≥0∞) + 1) * τ + 1 := by
          rw [hb]
          ring

end RebuildBound.P10Proof
