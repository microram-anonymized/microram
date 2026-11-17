import RebuildBound.Spec.P11de

/-!
# P11e: product laws on a discrete node set

General lemmas on `Measure.pi ν` over a finite index type with a countable
discrete state space `α`, all proved on singletons (`Measure.ext_of_singleton`):

* `lintegral_pi_update`: integrating a kernel into one coordinate replaces that
  coordinate's law by the bind;
* `lintegral_pi_resample`: its special case of an independent resample;
* `map_pairSplit`: grouping the coordinates into pairs `σ (inl t), σ (inr t)`;
* `map_pairMap`: a map that combines each pair into its first slot and puts a
  constant in the second.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace RebuildBound.P11eProof

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} [MeasurableSpace α]
  [DiscreteMeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

lemma isProb_bind (μ : Measure α) [IsProbabilityMeasure μ] (κ : α → Measure α)
    [hκ : ∀ x, IsProbabilityMeasure (κ x)] : IsProbabilityMeasure (μ.bind κ) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable]
  simp

open scoped Classical in
lemma preimage_update_singleton (y z : ι → α) (a : ι) :
    Function.update y a ⁻¹' {z} = if (∀ i, i ≠ a → y i = z i) then {z a} else ∅ := by
  ext w
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.update_eq_iff]
  split_ifs with h
  · simp only [Set.mem_singleton_iff]
    exact ⟨fun h' => h'.1, fun hw => ⟨hw, h⟩⟩
  · simp only [Set.mem_empty_iff_false, iff_false, not_and]
    intro _ h'
    exact h h'

lemma prod_update_singleton (ν : ι → Measure α) (z : ι → α) (a : ι) (w : α) :
    ∏ i, ν i {Function.update z a w i} = ν a {w} * ∏ i ∈ Finset.univ.erase a, ν i {z i} := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

open scoped Classical in
lemma pi_bind_update (ν ν' : ι → Measure α) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, IsProbabilityMeasure (ν' i)] (κ : α → Measure α) (a : ι)
    (ha : ν' a = (ν a).bind κ) (hi : ∀ i, i ≠ a → ν' i = ν i) :
    (Measure.pi ν).bind (fun y => (κ (y a)).map (Function.update y a)) = Measure.pi ν' := by
  refine Measure.ext_of_singleton fun z => ?_
  rw [Measure.bind_apply (measurableSet_singleton z) Measurable.of_discrete.aemeasurable,
    Measure.pi_singleton]
  simp_rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton z),
    preimage_update_singleton]
  rw [lintegral_countable']
  have hsupp : Function.support (fun y : ι → α =>
      κ (y a) (if (∀ i, i ≠ a → y i = z i) then {z a} else ∅) * Measure.pi ν {y}) ⊆
      Set.range (Function.update z a) := by
    intro y hy
    by_cases h : ∀ i, i ≠ a → y i = z i
    · refine ⟨y a, ?_⟩
      funext i
      by_cases hia : i = a
      · subst hia; simp
      · rw [Function.update_of_ne hia, h i hia]
    · simp [h] at hy
  rw [← (Function.update_injective z a).tsum_eq hsupp]
  have hterm : ∀ w : α, κ (Function.update z a w a)
      (if (∀ i, i ≠ a → Function.update z a w i = z i) then {z a} else ∅) *
        Measure.pi ν {Function.update z a w} =
      (κ w {z a} * ν a {w}) * ∏ i ∈ Finset.univ.erase a, ν i {z i} := by
    intro w
    have h : ∀ i, i ≠ a → Function.update z a w i = z i :=
      fun i hi => Function.update_of_ne hi _ _
    rw [ite_eq_left h, Function.update_self, Measure.pi_singleton, prod_update_singleton, mul_assoc]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_right, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), ha,
    Measure.bind_apply (measurableSet_singleton _) Measurable.of_discrete.aemeasurable,
    lintegral_countable']
  congr 1
  refine Finset.prod_congr rfl fun i hmem => ?_
  rw [hi i (Finset.ne_of_mem_erase hmem)]

/-- Integrating a kernel `κ` into coordinate `a` of a product law replaces the law of
that coordinate by `(ν a).bind κ`. -/
lemma lintegral_pi_update (ν ν' : ι → Measure α) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, IsProbabilityMeasure (ν' i)] (κ : α → Measure α) (a : ι)
    (ha : ν' a = (ν a).bind κ) (hi : ∀ i, i ≠ a → ν' i = ν i) (f : (ι → α) → ℝ≥0∞) :
    ∫⁻ y, ∫⁻ z, f (Function.update y a z) ∂(κ (y a)) ∂(Measure.pi ν) =
      ∫⁻ y, f y ∂(Measure.pi ν') := by
  rw [← pi_bind_update ν ν' κ a ha hi, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete]

/-- Resampling coordinate `a` independently from its own law. -/
lemma lintegral_pi_resample (ν : ι → Measure α) [∀ i, IsProbabilityMeasure (ν i)] (a : ι)
    (f : (ι → α) → ℝ≥0∞) :
    ∫⁻ y, f y ∂(Measure.pi ν) =
      ∫⁻ y, ∫⁻ z, f (Function.update y a z) ∂(ν a) ∂(Measure.pi ν) := by
  rw [lintegral_pi_update ν ν (fun _ => ν a) a ?_ (fun _ _ => rfl)]
  rw [Measure.bind_const, measure_univ, one_smul]

/-! ### Pairs of coordinates -/

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Group the coordinates into the pairs `(σ (inl t), σ (inr t))`. -/
def pairSplit (σ : T ⊕ T ≃ ι) : (ι → α) ≃ (T → α × α) where
  toFun y t := (y (σ (.inl t)), y (σ (.inr t)))
  invFun z i := Sum.elim (fun t => (z t).1) (fun t => (z t).2) (σ.symm i)
  left_inv y := by
    funext i
    obtain ⟨s, rfl⟩ := σ.surjective i
    cases s <;> simp
  right_inv z := by
    funext t
    simp

lemma map_pairSplit (ν : ι → Measure α) [∀ i, IsProbabilityMeasure (ν i)] (σ : T ⊕ T ≃ ι) :
    (Measure.pi ν).map (pairSplit σ) =
      Measure.pi (fun t => (ν (σ (.inl t))).prod (ν (σ (.inr t)))) := by
  refine Measure.ext_of_singleton fun z => ?_
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton z)]
  have hpre : (pairSplit σ : (ι → α) → (T → α × α)) ⁻¹' {z} = {(pairSplit σ).symm z} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (Equiv.eq_symm_apply (pairSplit σ)).symm
  rw [hpre, Measure.pi_singleton, Measure.pi_singleton,
    ← Fintype.prod_equiv σ (fun s => ν (σ s) {(pairSplit σ).symm z (σ s)}) _ (fun _ => rfl),
    Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  have hz : ({z t} : Set (α × α)) = {(z t).1} ×ˢ {(z t).2} := by simp
  rw [hz, Measure.prod_prod]
  simp [pairSplit]

lemma map_extend (μ : T → Measure α) [∀ t, IsProbabilityMeasure (μ t)] (σ : T ⊕ T ≃ ι) (c : α)
    (X : (T → α) → (ι → α)) (hX1 : ∀ z t, X z (σ (.inl t)) = z t)
    (hX2 : ∀ z t, X z (σ (.inr t)) = c)
    (ν' : ι → Measure α) [∀ i, IsProbabilityMeasure (ν' i)]
    (h1 : ∀ t, ν' (σ (.inl t)) = μ t) (h2 : ∀ t, ν' (σ (.inr t)) = Measure.dirac c) :
    (Measure.pi μ).map X = Measure.pi ν' := by
  refine Measure.ext_of_singleton fun w => ?_
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton w), Measure.pi_singleton,
    ← Fintype.prod_equiv σ (fun s => ν' (σ s) {w (σ s)}) _ (fun _ => rfl), Fintype.prod_sum_type]
  simp only [h1, h2]
  by_cases hc : ∀ t, w (σ (.inr t)) = c
  · have hpre : X ⁻¹' {w} = {fun t => w (σ (.inl t))} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro rfl
        funext t
        rw [hX1]
      · rintro rfl
        funext i
        obtain ⟨s, rfl⟩ := σ.surjective i
        cases s with
        | inl t => rw [hX1]
        | inr t => rw [hX2, hc]
    rw [hpre, Measure.pi_singleton]
    simp [hc]
  · push Not at hc
    obtain ⟨t0, ht0⟩ := hc
    have hpre : X ⁻¹' {w} = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      apply ht0
      rw [← h, hX2]
    have hz : ∏ t, Measure.dirac c {w (σ (.inr t))} = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ t0) (by simp [Ne.symm ht0])
    rw [hpre, measure_empty, hz, mul_zero]

/-- Combining each pair `(σ (inl t), σ (inr t))` by `f` into the first slot and
putting `c` in the second maps a product law to a product law. -/
lemma map_pairMap (ν : ι → Measure α) [∀ i, IsProbabilityMeasure (ν i)] (σ : T ⊕ T ≃ ι)
    (f : α × α → α) (c : α) (H : (ι → α) → (ι → α))
    (hH1 : ∀ y t, H y (σ (.inl t)) = f (y (σ (.inl t)), y (σ (.inr t))))
    (hH2 : ∀ y t, H y (σ (.inr t)) = c)
    (ν' : ι → Measure α) [∀ i, IsProbabilityMeasure (ν' i)]
    (h1 : ∀ t, ν' (σ (.inl t)) = ((ν (σ (.inl t))).prod (ν (σ (.inr t)))).map f)
    (h2 : ∀ t, ν' (σ (.inr t)) = Measure.dirac c) :
    (Measure.pi ν).map H = Measure.pi ν' := by
  let X : (T → α) → (ι → α) := fun z i => Sum.elim z (fun _ => c) (σ.symm i)
  have hHe : H = X ∘ (fun z t => f (z t)) ∘ pairSplit σ := by
    funext y i
    obtain ⟨s, rfl⟩ := σ.surjective i
    cases s <;> simp [X, hH1, hH2, pairSplit]
  rw [hHe, ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    ← Measure.map_map Measurable.of_discrete Measurable.of_discrete, map_pairSplit,
    Measure.pi_map_pi (fun _ => Measurable.of_discrete.aemeasurable)]
  exact map_extend _ σ c X (fun z t => by simp [X]) (fun z t => by simp [X]) ν' h1 h2

end General

end RebuildBound.P11eProof
