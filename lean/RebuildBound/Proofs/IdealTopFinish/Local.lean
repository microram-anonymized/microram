import RebuildBound.Spec.IdealDirectLocal
import RebuildBound.Proofs.IdealHierarchy
import RebuildBound.Proofs.FiniteCoupling
import RebuildBound.Proofs.HierarchyTopLaw.Finish
import RebuildBound.Proofs.G3fin

/-! A top-finish section projects one current-family word per input key and
independent words on the remaining finite source keys. Preparation and the
lower carry may both depend on this family; their complete record sets stay
fixed while their layouts vary. No capacity-success premise is imposed. -/
namespace RebuildBound.IdealTopFinishProof
open Model Spec Spec.IdealHierarchy Spec.IdealDirect MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

abbrev Hist (K KU : Finset LogicalKey) := ↥(K \ KU) → Word64

noncomputable def extend (K KU : Finset LogicalKey) (hist : Hist K KU)
    (w : LogicalKey → Nat) : LogicalKey → Nat :=
  fun key => if key ∈ KU then w key else
    if hK : key ∈ K \ KU then (hist ⟨key, hK⟩).val else 0

noncomputable def law (row : TopGeom) (K : Finset LogicalKey) (RA RB : Finset Rec)
    (producer : (LogicalKey → Nat) → TopInputs) : TopJobLaw row where
  RA := RA
  RB := RB
  W := 64
  Hist := Hist K (RA.image Rec.key ∪ RB.image Rec.key)
  weight _ := (Fintype.card (Hist K (RA.image Rec.key ∪ RB.image Rec.key)) : ℝ≥0∞)⁻¹
  inputs hist w := producer (extend K (RA.image Rec.key ∪ RB.image Rec.key) hist w)

theorem law_valid (row : TopGeom) (K : Finset LogicalKey) (RA RB : Finset Rec)
    (producer : (LogicalKey → Nat) → TopInputs) (unsh : Rec → Bool)
    (hwide : row.k + row.e ≤ 64)
    (hshape : ∀ w, TopShape row unsh w (producer w))
    (hA : ∀ w, (producer w).aAll.toFinset = RA)
    (hB : ∀ w, (producer w).bAll.toFinset = RB)
    (hloadA : RA.card ≤ 32 * row.T)
    (hloadW : (liveSet RA RB).card ≤ 32 * row.T) :
    TopLaw (law row K RA RB producer) unsh 32 where
  weight_sum := by
    change (∑ _ : Hist K (RA.image Rec.key ∪ RB.image Rec.key),
      (Fintype.card (Hist K (RA.image Rec.key ∪ RB.image Rec.key)) : ℝ≥0∞)⁻¹) = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)
  shape hist h := by
    apply HierarchyTopLawProof.topShape_congr (hshape _)
    intro r hr
    have hkey : r.key ∈ RA.image Rec.key ∪ RB.image Rec.key := by
      rcases List.mem_append.mp hr with ha | hb
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _
          (by rw [← hA]; exact List.mem_toFinset.mpr ha))
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
          (by rw [← hB]; exact List.mem_toFinset.mpr hb))
    simp only [extend, ite_eq_left hkey]
  aRecs hist h := hA _
  bRecs hist h := hB _
  wide := hwide
  aLoad := by exact_mod_cast hloadA
  wLoad := by exact_mod_cast hloadW

def read (family : IdealKey.Family) (K KU : Finset LogicalKey)
    (inside : familyBlock family → Word64) : Hist K KU × (KU → Word64) :=
  (fun key => inside ⟨.inl (family, key.val), rfl⟩,
   fun key => inside ⟨.inl (family, key.val), rfl⟩)

private def pick (family : IdealKey.Family) (K KU : Finset LogicalKey) :
    ↥(K \ KU) ⊕ KU → familyBlock family
  | .inl key => ⟨.inl (family, key.val), rfl⟩
  | .inr key => ⟨.inl (family, key.val), rfl⟩

private theorem pick_injective (family : IdealKey.Family) (K KU : Finset LogicalKey) :
    Function.Injective (pick family K KU) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext (Prod.mk.inj (Sum.inl.inj h)).2)
    | inr b =>
      have hk := (Prod.mk.inj (Sum.inl.inj h)).2
      exact False.elim ((Finset.mem_sdiff.mp a.property).2 (hk.symm ▸ b.property))
  | inr a =>
    cases b with
    | inl b =>
      have hk := (Prod.mk.inj (Sum.inl.inj h)).2
      exact False.elim ((Finset.mem_sdiff.mp b.property).2 (hk ▸ a.property))
    | inr b => exact congrArg Sum.inr (Subtype.ext (Prod.mk.inj (Sum.inl.inj h)).2)

private theorem read_uniform (family : IdealKey.Family) (K KU : Finset LogicalKey) :
    (Measure.infinitePi (fun _ : familyBlock family => IdealKey.wordLaw)).map
      (read family K KU) = uniformOn (Set.univ : Set (Hist K KU × (KU → Word64))) := by
  let e := Equiv.sumArrowEquivProdArrow ↥(K \ KU) KU Word64
  have he : read family K KU = e ∘ (fun fresh key => fresh (pick family K KU key)) := rfl
  rw [he, ← Measure.map_map Measurable.of_discrete (by fun_prop),
    Measure.map_infinitePi_infinitePi_of_inj (pick_injective family K KU),
    Measure.infinitePi_eq_pi]
  have hu : Measure.pi (fun _ : ↥(K \ KU) ⊕ KU => IdealKey.wordLaw) =
      uniformOn (Set.univ : Set (↥(K \ KU) ⊕ KU → Word64)) := by
    simpa [IdealKey.wordLaw] using
      (uniformOn_pi (f := fun _ : ↥(K \ KU) ⊕ KU => (Set.univ : Set Word64))).symm
  rw [hu, HierarchyLevelOneProof.map_uniform_equiv e]

theorem coupling (family : IdealKey.Family) (row : TopGeom) (K : Finset LogicalKey)
    (RA RB : Finset Rec) (producer : (LogicalKey → Nat) → TopInputs) :
    FiniteCoupling (Measure.infinitePi (fun _ : familyBlock family => IdealKey.wordLaw))
      (law row K RA RB producer).toFinite
      (read family K (RA.image Rec.key ∪ RB.image Rec.key)) := by
  let KU := RA.image Rec.key ∪ RB.image Rec.key
  change ∀ outcome : Hist K KU × (KU → Word64),
    (Measure.infinitePi (fun _ : familyBlock family => IdealKey.wordLaw))
      ((read family K KU) ⁻¹' {outcome}) ≤
      (Fintype.card (Hist K KU) : ℝ≥0∞)⁻¹ *
        (Fintype.card (KU → Word64) : ℝ≥0∞)⁻¹
  intro outcome
  rw [← Measure.map_apply (by unfold read; fun_prop) (measurableSet_singleton outcome),
    read_uniform, uniformOn_univ, Measure.count_singleton]
  rw [Fintype.card_prod, Nat.cast_mul, one_div,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

/-- The complete top-finish contribution inherits its analytic bound. Source
keys outside A and B are independent finite history; keys shared by A and B
use exactly the same current word. Empty restrictions are covered unchanged. -/
theorem local_bound (family : IdealKey.Family) (row : TopGeom) (K1 K2 : Nat)
    (hv : row.Valid) (hwide : row.k + row.e ≤ 64)
    (hK1 : row.C < K1) (hK2 : min row.SMerge row.STier < K2)
    (K : Finset LogicalKey) (RA RB : Finset Rec)
    (producer : (LogicalKey → Nat) → TopInputs) (unsh : Rec → Bool)
    (hshape : ∀ w, TopShape row unsh w (producer w))
    (hA : ∀ w, (producer w).aAll.toFinset = RA)
    (hB : ∀ w, (producer w).bAll.toFinset = RB)
    (hloadA : RA.card ≤ 32 * row.T)
    (hloadW : (liveSet RA RB).card ≤ 32 * row.T)
    (hlocal : ∀ w w', (∀ key ∈ K, w key = w' key) → producer w = producer w') :
    (Measure.infinitePi (fun _ : familyBlock family => IdealKey.wordLaw))
      {inside | TopTiersFit row (producer (familyWords family inside)) ∧
        (topJob row unsh (familyWords family inside)
          (producer (familyWords family inside))).toBool = false} ≤
      ENNReal.ofReal (topFinishBound row.C row.SR row.rho row.I row.T
        (min row.SMerge row.STier) K1 K2 32) := by
  classical
  let KU := RA.image Rec.key ∪ RB.image Rec.key
  let L := law row K RA RB producer
  have hL := law_valid row K RA RB producer unsh hwide hshape hA hB hloadA hloadW
  have hbound := G3 row L unsh 32 K1 K2 hL hv hK1 hK2
  refine (FiniteCouplingProof.finite_transport_sub _ L.toFinite
    (read family K KU) (coupling family row K RA RB producer)
    (topFailEvent L unsh) _ ?_).trans hbound
  intro inside hevent
  let sampled := read family K KU inside
  have hword : ∀ key ∈ K,
      familyWords family inside key = extend K KU sampled.1 (L.wordFn sampled.2) key := by
    intro key hk
    by_cases hu : key ∈ KU
    · simp only [extend, ite_eq_left hu]
      change _ = if hx : key ∈ KU then _ else 0
      rw [dite_eq_left hu]
      rfl
    · have hr : key ∈ K \ KU := Finset.mem_sdiff.mpr ⟨hk, hu⟩
      simp only [extend, ite_eq_right hu, dite_eq_left hr]
      rfl
  have hinp := hlocal _ _ hword
  have hmem : ∀ r ∈ (producer (familyWords family inside)).aAll ++
      (producer (familyWords family inside)).bAll, r.key ∈ KU := by
    intro r hr
    rcases List.mem_append.mp hr with ha | hb
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _
        (by rw [← hA]; exact List.mem_toFinset.mpr ha))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (by rw [← hB]; exact List.mem_toFinset.mpr hb))
  have hcur : ∀ r ∈ (producer (familyWords family inside)).aAll ++
      (producer (familyWords family inside)).bAll,
      familyWords family inside r.key = L.wordFn sampled.2 r.key := by
    intro r hr
    change _ = if hx : r.key ∈ KU then _ else 0
    rw [dite_eq_left (hmem r hr)]
    rfl
  change TopTiersFit row (producer (extend K KU sampled.1 (L.wordFn sampled.2))) ∧
    (topJob row unsh (L.wordFn sampled.2)
      (producer (extend K KU sampled.1 (L.wordFn sampled.2)))).toBool = false
  rw [← hinp, ← TopJobWordLocal row unsh _ _ _ hcur]
  exact hevent

end RebuildBound.IdealTopFinishProof
