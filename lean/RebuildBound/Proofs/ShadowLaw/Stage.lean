import RebuildBound.Proofs.ShadowLaw.Pi

/-!
# ShadowLaw: stage laws of the shadow tree (from P11e.Stage)

Moved from the d = 2 chain (`P11e.Stage`); namespace `RebuildBound.P11eProof` kept.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval
set_option linter.unusedSectionVars false
namespace RebuildBound.P11eProof
open RebuildBound.Spec
instance isProb_thinPair (p : I) (s : ℕ × ℕ) : IsProbabilityMeasure (thinPair p s) := by
  unfold thinPair
  infer_instance

instance isProb_bind_thinPair (μ : Measure (ℕ × ℕ)) [IsProbabilityMeasure μ] (p : I) :
    IsProbabilityMeasure (μ.bind (thinPair p)) :=
  isProb_bind μ (thinPair p)

section States
variable {ι : Type*} [DecidableEq ι]
/-- Node states from node pairs `(main, shadow)`. -/
def toS (y : ι → ℕ × ℕ) : States ι
  | (v, .main) => (y v).1
  | (v, .shadow) => (y v).2

@[simp] lemma toS_main (y : ι → ℕ × ℕ) (v : ι) : toS y (v, .main) = (y v).1 := rfl

@[simp] lemma toS_shadow (y : ι → ℕ × ℕ) (v : ι) : toS y (v, .shadow) = (y v).2 := rfl

lemma setNode_toS (a : ι) (m r : ℕ) (y : ι → ℕ × ℕ) :
    setNode a m r (toS y) = toS (Function.update y a (m, r)) := by
  funext ⟨v, s⟩
  by_cases hv : v = a
  · subst hv
    cases s <;> simp [setNode]
  · cases s <;> simp [setNode, hv]

lemma thinAt_toS (a : ι) (p : I) (G : States ι → ℝ≥0∞) (y : ι → ℕ × ℕ) :
    thinAt a p G (toS y) = ∫⁻ z, G (toS (Function.update y a z)) ∂(thinPair p (y a)) := by
  rw [thinPair, lintegral_prod _ Measurable.of_discrete.aemeasurable]
  simp only [thinAt, toS_main, toS_shadow, setNode_toS]

lemma mainEmbed_eq (N : ι → ℕ) : mainEmbed N = toS (fun v => (N v, 0)) := by
  funext ⟨v, s⟩
  cases s <;> rfl

lemma capAt_toS (a : ι) (C : ℕ) (y : ι → ℕ × ℕ) :
    capAt a C (toS y) = toS (Function.update y a (capPair C (y a))) := by
  rw [capAt, toS_main, toS_shadow, setNode_toS]
  rfl

lemma capPair_idem (C : ℕ) (s : ℕ × ℕ) : capPair C (capPair C s) = capPair C s := by
  simp only [capPair, Prod.mk.injEq]
  omega

lemma capAll_toS (C : ℕ) (y : ι → ℕ × ℕ) :
    ∀ l : List ι, capAll l C (toS y) = toS (fun v => if v ∈ l then capPair C (y v) else y v)
  | [] => by simp [capAll]
  | a :: l => by
    show capAt a C (capAll l C (toS y)) = _
    rw [capAll_toS C y l, capAt_toS]
    congr 1
    funext v
    by_cases hv : v = a
    · subst hv
      simp only [Function.update_self, List.mem_cons, true_or, ite_true]
      split_ifs <;> simp [capPair_idem]
    · simp [hv]

/-- Capping an exhaustive node list embeds the capped first arrivals. -/
lemma capAll_mainEmbed (C : ℕ) (l : List ι) (hl : ∀ v, v ∈ l) (N : ι → ℕ) :
    capAll l C (mainEmbed N) = toS (fun v => capPair C (N v, 0)) := by
  rw [mainEmbed_eq, capAll_toS]
  simp only [hl, ite_true]

lemma sumAlong_toS {κ : Type*} [Fintype κ] (parent : κ → ι) (y : κ → ℕ × ℕ) :
    sumAlong parent (toS y) =
      toS (fun W => ∑ V ∈ Finset.univ.filter (fun V => parent V = W), y V) := by
  funext ⟨W, s⟩
  cases s <;> simp [sumAlong, Prod.fst_sum, Prod.snd_sum]

variable [Fintype ι]
/-- Thinning every node of a nodup list, against a product law of node pairs. -/
lemma lintegral_thinAll (p : I) (F : States ι → ℝ≥0∞) :
    ∀ (l : List ι), l.Nodup → ∀ (ν : ι → Measure (ℕ × ℕ)), (∀ i, IsProbabilityMeasure (ν i)) →
      ∫⁻ y, thinAll l (fun _ => p) F (toS y) ∂(Measure.pi ν) =
        ∫⁻ y, F (toS y) ∂(Measure.pi (fun v => if v ∈ l then (ν v).bind (thinPair p) else ν v))
  | [], _, ν, hν => by simp [thinAll]
  | a :: l, hl, ν, hν => by
    have ha : a ∉ l := (List.nodup_cons.1 hl).1
    let ν1 := Function.update ν a ((ν a).bind (thinPair p))
    have hν1 : ∀ i, IsProbabilityMeasure (ν1 i) := by
      intro i
      by_cases hi : i = a
      · subst hi
        simp only [ν1, Function.update_self]
        infer_instance
      · simp only [ν1, Function.update_of_ne hi]
        infer_instance
    have step : ∫⁻ y, thinAll (a :: l) (fun _ => p) F (toS y) ∂(Measure.pi ν) =
        ∫⁻ y, thinAll l (fun _ => p) F (toS y) ∂(Measure.pi ν1) := by
      show ∫⁻ y, thinAt a p (thinAll l (fun _ => p) F) (toS y) ∂(Measure.pi ν) = _
      simp_rw [thinAt_toS]
      exact lintegral_pi_update ν ν1 (thinPair p) a (by simp [ν1])
        (fun i hi => by simp [ν1, hi]) (fun y => thinAll l (fun _ => p) F (toS y))
    rw [step, lintegral_thinAll p F l (List.nodup_cons.1 hl).2 ν1 hν1]
    congr 2
    funext v
    by_cases hv : v = a
    · subst hv
      simp [ν1, ha]
    · simp [ν1, hv]

end States
section Bits
variable {b : ℕ}
/-- The nodes whose bit `j` is `r`. -/
abbrev Top (j : Fin b) (r : Bool) := {W : Bits b // W j = r}

/-- Every node is a node of `Top j r` or its sibling across bit `j`. -/
def flipEquiv (j : Fin b) (r : Bool) : Top j r ⊕ Top j r ≃ Bits b where
  toFun s := match s with
    | .inl t => t.1
    | .inr t => Function.update t.1 j (!r)
  invFun W := if h : W j = r then .inl ⟨W, h⟩ else .inr ⟨Function.update W j r, by simp⟩
  left_inv s := by
    cases s with
    | inl t => simp [t.2]
    | inr t =>
      have h : ¬ (Function.update t.1 j (!r) j = r) := by simp
      simp only [h, dite_false, Sum.inr.injEq]
      apply Subtype.ext
      simp only [Function.update_idem]
      exact Function.update_eq_self_iff.mpr (by simp [t.2])
  right_inv W := by
    by_cases h : W j = r
    · simp [h]
    · simp only [h, dite_false, Function.update_idem]
      have : W j = !r := by cases hW : W j <;> cases r <;> simp_all
      rw [← this, Function.update_eq_self]

@[simp] lemma flipEquiv_inl (j : Fin b) (r : Bool) (t : Top j r) :
    flipEquiv j r (.inl t) = t.1 := rfl

@[simp] lemma flipEquiv_inr (j : Fin b) (r : Bool) (t : Top j r) :
    flipEquiv j r (.inr t) = Function.update t.1 j (!r) := rfl

lemma filter_update_eq (j : Fin b) (r : Bool) (W : Bits b) :
    Finset.univ.filter (fun V : Bits b => Function.update V j r = W) =
      if W j = r then {W, Function.update W j (!r)} else ∅ := by
  ext V
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update_eq_iff]
  split_ifs with hW
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hV⟩
      by_cases hVj : V j = r
      · left
        funext i
        by_cases hi : i = j
        · subst hi; rw [hVj, hW]
        · exact hV i hi
      · right
        funext i
        by_cases hi : i = j
        · subst hi
          rw [Function.update_self]
          cases hv : V i <;> cases r <;> simp_all
        · rw [Function.update_of_ne hi]
          exact hV i hi
    · rintro (rfl | rfl)
      · exact ⟨hW.symm, fun _ _ => rfl⟩
      · exact ⟨hW.symm, fun i hi => Function.update_of_ne hi _ _⟩
  · simp only [Finset.notMem_empty, iff_false, not_and]
    intro h
    exact absurd h.symm hW

/-- Sum over the two preimages of a Boolean-coordinate update. -/
lemma sum_filter_update {β : Type*} [AddCommMonoid β] (j : Fin b) (c : Bool)
    (f : Bits b → β) (W : Bits b) :
    ∑ V ∈ Finset.univ.filter (fun V : Bits b => Function.update V j c = W), f V =
      if W j = c then f W + f (Function.update W j (!c)) else 0 := by
  rw [filter_update_eq]
  split_ifs with hW
  · rw [Finset.sum_pair]
    intro h
    have := congrFun h j
    simp [hW] at this
  · simp

/-- The stage map on node pairs: the node with bit `j` equal to `r` receives itself
plus its sibling, every node is capped, and the other nodes are empty. -/
def stageMap (C : ℕ) (j : Fin b) (r : Bool) (y : Bits b → ℕ × ℕ) (W : Bits b) : ℕ × ℕ :=
  capPair C (if W j = r then y W + y (Function.update W j (!r)) else 0)

/-- The law of the stage map's output under a product law `μ`. -/
noncomputable def combLaw (C : ℕ) (j : Fin b) (r : Bool) (μ : Bits b → Measure (ℕ × ℕ))
    (W : Bits b) : Measure (ℕ × ℕ) :=
  if W j = r then (μ W ∗ μ (Function.update W j (!r))).map (capPair C)
  else Measure.dirac (0, 0)

/-- The product law after one stage: thin every node, then the stage map. -/
noncomputable def stepLaw (C : ℕ) (j : Fin b) (r : Bool) (ν : Bits b → Measure (ℕ × ℕ)) :
    Bits b → Measure (ℕ × ℕ) :=
  combLaw C j r (fun v => (ν v).bind (thinPair half))

lemma isProb_combLaw (C : ℕ) (j : Fin b) (r : Bool) (μ : Bits b → Measure (ℕ × ℕ))
    (hμ : ∀ i, IsProbabilityMeasure (μ i)) (W : Bits b) :
    IsProbabilityMeasure (combLaw C j r μ W) := by
  unfold combLaw
  split_ifs
  · infer_instance
  · infer_instance

end Bits
end RebuildBound.P11eProof
