import RebuildBound.Proofs.P12e.Block

/-!
# P12e: one backward binary stage in `r` blocks

The block index of a node `(i, W)` is inert: the stage map of `rBackStage` acts on
every block as the binary stage map `stageMap` of P11e (`P11e/Stage.lean`) on that
block's nodes, and its image law is again a product (`map_pairMap`, grouping each
node `(i, W)` with bit `j` of `R` with its sibling `(i, W')` across bit `j`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

set_option linter.unusedSectionVars false

namespace RebuildBound.P12eProof

open RebuildBound.Spec RebuildBound.P11eProof

variable {r b : ℕ}

@[simp] lemma mem_allRNodes (v : RNode r b) : v ∈ allRNodes r b := by
  simp [allRNodes]

/-- Every node of `r` blocks is a node `(i, W)` with bit `j` of `W` equal to `c`, or
its sibling across bit `j`. -/
def flipEquivR (j : Fin b) (c : Bool) : (Fin r × Top j c) ⊕ (Fin r × Top j c) ≃ RNode r b :=
  (Equiv.prodSumDistrib (Fin r) (Top j c) (Top j c)).symm.trans
    (Equiv.prodCongr (Equiv.refl _) (flipEquiv j c))

@[simp] lemma flipEquivR_inl (j : Fin b) (c : Bool) (t : Fin r × Top j c) :
    flipEquivR j c (.inl t) = (t.1, t.2.1) := by
  simp [flipEquivR]

@[simp] lemma flipEquivR_inr (j : Fin b) (c : Bool) (t : Fin r × Top j c) :
    flipEquivR j c (.inr t) = (t.1, Function.update t.2.1 j (!c)) := by
  simp [flipEquivR]

lemma sum_filter_update (j : Fin b) (c : Bool) (f : Bits b → ℕ × ℕ) (W : Bits b) :
    ∑ V ∈ Finset.univ.filter (fun V : Bits b => Function.update V j c = W), f V =
      if W j = c then f W + f (Function.update W j (!c)) else 0 :=
  RebuildBound.P11eProof.sum_filter_update j c f W

lemma sum_filter_block {β : Type*} [AddCommMonoid β] (j : Fin b) (c : Bool)
    (y : RNode r b → β) (v : RNode r b) :
    ∑ V ∈ Finset.univ.filter (fun V : RNode r b => (V.1, Function.update V.2 j c) = v), y V =
      ∑ W ∈ Finset.univ.filter (fun W : Bits b => Function.update W j c = v.2), y (v.1, W) := by
  obtain ⟨i0, W0⟩ := v
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Prod.mk.injEq]
  rw [Finset.sum_eq_single i0]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

/-- The stage map on node pairs of `r` blocks: the binary stage map in every block. -/
def stageMapR (C : ℕ) (j : Fin b) (c : Bool) (y : RNode r b → ℕ × ℕ) (v : RNode r b) :
    ℕ × ℕ :=
  stageMap C j c (fun W => y (v.1, W)) v.2

lemma capAll_sumAlong_toSR (C : ℕ) (j : Fin b) (c : Bool) (y : RNode r b → ℕ × ℕ) :
    capAll (allRNodes r b) C
        (sumAlong (fun V : RNode r b => (V.1, Function.update V.2 j c)) (toS y)) =
      toS (stageMapR C j c y) := by
  rw [sumAlong_toS, capAll_toS]
  congr 1
  funext v
  simp only [allRNodes, Finset.mem_toList, Finset.mem_univ, ite_true, stageMapR, stageMap]
  rw [sum_filter_block, sum_filter_update]

/-- The law of the stage map's output under a product law `μ`: the binary one in every
block. -/
noncomputable def combLawR (C : ℕ) (j : Fin b) (c : Bool) (μ : RNode r b → Measure (ℕ × ℕ))
    (v : RNode r b) : Measure (ℕ × ℕ) :=
  combLaw C j c (fun W => μ (v.1, W)) v.2

/-- The product law after one stage: thin every node, then the stage map. -/
noncomputable def stepLawR (C : ℕ) (j : Fin b) (c : Bool) (ν : RNode r b → Measure (ℕ × ℕ)) :
    RNode r b → Measure (ℕ × ℕ) :=
  combLawR C j c (fun v => (ν v).bind (thinPair half))

lemma map_stageMapR (C : ℕ) (j : Fin b) (c : Bool) (μ : RNode r b → Measure (ℕ × ℕ))
    (hμ : ∀ i, IsProbabilityMeasure (μ i)) :
    (Measure.pi μ).map (stageMapR C j c) = Measure.pi (combLawR C j c μ) := by
  have : ∀ v, IsProbabilityMeasure (combLawR C j c μ v) :=
    fun v => isProb_combLaw C j c _ (fun _ => hμ _) v.2
  refine map_pairMap μ (flipEquivR j c) (fun q => capPair C (q.1 + q.2)) (0, 0) _ ?_ ?_ _ ?_ ?_
  · intro y t
    simp [stageMapR, stageMap, t.2.2]
  · intro y t
    simp [stageMapR, stageMap, capPair]
  · intro t
    simp only [flipEquivR_inl, flipEquivR_inr, combLawR, combLaw, t.2.2, ite_true]
    rw [Measure.conv, Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    rfl
  · intro t
    simp [combLawR, combLaw]

/-- One backward stage in `r` blocks against a product law of node pairs. -/
lemma lintegral_rBackStage (C : ℕ) (R : Bits b) (j : ℕ) (hj : j < b)
    (ν : RNode r b → Measure (ℕ × ℕ)) (hν : ∀ i, IsProbabilityMeasure (ν i))
    (ψ : States (RNode r b) → ℝ≥0∞) :
    ∫⁻ y, rBackStage C R j ψ (toS y) ∂(Measure.pi ν) =
      ∫⁻ y, ψ (toS y) ∂(Measure.pi (stepLawR C ⟨j, hj⟩ (R ⟨j, hj⟩) ν)) := by
  have hth : ∀ i, IsProbabilityMeasure ((ν i).bind (thinPair half)) := fun _ => inferInstance
  simp only [rBackStage, hj, dite_true]
  rw [lintegral_thinAll half _ (allRNodes r b) (Finset.nodup_toList _) ν hν]
  simp only [mem_allRNodes, ite_true, Function.comp_apply, capAll_sumAlong_toSR]
  rw [← lintegral_map (f := fun w => ψ (toS w)) Measurable.of_discrete Measurable.of_discrete,
    map_stageMapR C _ _ _ hth]
  rfl

end RebuildBound.P12eProof
