import RebuildBound.Proofs.IdealDirectA.Local
import RebuildBound.Proofs.HierarchyTopLaw.Density
import RebuildBound.Proofs.TPJobfin.Generic
import RebuildBound.Proofs.WordLocalTP

/-! A top-preparation section reads the old family on a finite source set and
an independent current word on every A key. The previous homes are exactly
uniform: the binary home bits split off from the rest of the old history. -/
namespace RebuildBound.IdealTopPrepProof
open Model Spec Spec.IdealHierarchy MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open IdealDirectAProof (freshBlock oldWords currentWords)

abbrev Hist (K KA : Finset LogicalKey) :=
  (KA → Word64) × (↥(K \ KA) → Word64)

noncomputable def oldWord (K KA : Finset LogicalKey) (hist : Hist K KA) : LogicalKey → Nat :=
  fun key => if hA : key ∈ KA then (hist.1 ⟨key, hA⟩).val else
    if hK : key ∈ K \ KA then (hist.2 ⟨key, hK⟩).val else 0

noncomputable def law (row : TPGeom) (K KA : Finset LogicalKey)
    (producer : (LogicalKey → Nat) → TPInputs) : TPJobLaw row where
  KA := KA
  W := 64
  Hist := Hist K KA
  weight _ := (Fintype.card (Hist K KA) : ℝ≥0∞)⁻¹
  aIn hist := producer (oldWord K KA hist)
  pos hist key := oldWord K KA hist key % row.T

/-- Splitting every old word into home bits and unused bits gives the exact
joint home law, including an empty A set and extra source keys. -/
theorem density_bits (K KA : Finset LogicalKey) (b : Nat) (hb : b ≤ 64)
    (target : KA → Fin (2 ^ b)) :
    (∑ _hist ∈ Finset.univ.filter (fun hist : Hist K KA =>
        ∀ key : KA, (hist.1 key).val % 2 ^ b = (target key).val),
      (Fintype.card (Hist K KA) : ℝ≥0∞)⁻¹) =
      ((2 ^ b : ℝ≥0∞) ^ KA.card)⁻¹ := by
  classical
  let f : (KA → Word64) ≃ (KA → Fin (2 ^ b)) × (KA → Fin (2 ^ (64 - b))) :=
    (Equiv.arrowCongr (Equiv.refl KA) (HierarchyTopLawProof.divmodBits b hb)).trans
      (Equiv.arrowProdEquivProdArrow _ _ _)
  let e := (f.prodCongr (Equiv.refl (↥(K \ KA) → Word64))).trans (Equiv.prodAssoc _ _ _)
  have heq : (Finset.univ.filter fun hist : Hist K KA =>
      ∀ key : KA, (hist.1 key).val % 2 ^ b = (target key).val) =
      Finset.univ.filter fun hist => (e hist).1 = target := by
    ext hist
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, Fin.ext_iff]
    rfl
  rw [heq, HierarchyTopLawProof.fiber_sum]
  simp

theorem law_valid (row : TPGeom) (K KA : Finset LogicalKey)
    (producer : (LogicalKey → Nat) → TPInputs) (hwide : row.k ≤ 64)
    (hshape : ∀ old, TPShape row (fun key => old key % row.T) (producer old))
    (hkeys : ∀ old, ((producer old).aAll.map Rec.key).toFinset = KA)
    (hload : KA.card ≤ 32 * row.T) : TPLaw (law row K KA producer) 32 1 where
  weight_sum := by
    change (∑ _ : Hist K KA, (Fintype.card (Hist K KA) : ℝ≥0∞)⁻¹) = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)
  shape hist := hshape _
  aKeys hist := hkeys _
  wide := hwide
  load := by exact_mod_cast hload
  density target := by
    change KA → Fin (2 ^ row.k) at target
    have heq : (Finset.univ.filter fun hist : Hist K KA =>
        ∀ key : KA, (law row K KA producer).pos hist key = (target key).val) =
        Finset.univ.filter fun hist : Hist K KA =>
        ∀ key : KA, (hist.1 key).val % 2 ^ row.k = (target key).val := by
      apply Finset.filter_congr
      intro hist _
      apply forall_congr'
      intro key
      simp only [law, oldWord, dite_eq_left key.property, TPGeom.T]
    change (∑ hist ∈ Finset.univ.filter (fun hist : Hist K KA =>
      ∀ key : KA, (law row K KA producer).pos hist key = (target key).val),
      (Fintype.card (Hist K KA) : ℝ≥0∞)⁻¹) ≤
      1 / ((2 ^ row.k : Nat) : ℝ≥0∞) ^ KA.card
    rw [heq, density_bits K KA row.k hwide target]
    simp

def read (oldFamily currentFamily : IdealKey.Family) (K KA : Finset LogicalKey)
    (inside : freshBlock oldFamily currentFamily → Word64) : Hist K KA × (KA → Word64) :=
  ((fun key => inside ⟨.inl (oldFamily, key.val), Or.inl rfl⟩,
    fun key => inside ⟨.inl (oldFamily, key.val), Or.inl rfl⟩),
    fun key => inside ⟨.inl (currentFamily, key.val), Or.inr rfl⟩)

private def pick (oldFamily currentFamily : IdealKey.Family) (K KA : Finset LogicalKey) :
    (KA ⊕ ↥(K \ KA)) ⊕ KA → freshBlock oldFamily currentFamily
  | .inl (.inl key) => ⟨.inl (oldFamily, key.val), Or.inl rfl⟩
  | .inl (.inr key) => ⟨.inl (oldFamily, key.val), Or.inl rfl⟩
  | .inr key => ⟨.inl (currentFamily, key.val), Or.inr rfl⟩

private theorem pick_injective (oldFamily currentFamily : IdealKey.Family)
    (hne : oldFamily ≠ currentFamily) (K KA : Finset LogicalKey) :
    Function.Injective (pick oldFamily currentFamily K KA) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  rcases a with (a | a) | a <;> rcases b with (b | b) | b
  · exact congrArg (Sum.inl ∘ Sum.inl) (Subtype.ext (Prod.mk.inj (Sum.inl.inj h)).2)
  · have hk := (Prod.mk.inj (Sum.inl.inj h)).2
    exact False.elim ((Finset.mem_sdiff.mp b.property).2 (hk ▸ a.property))
  · exact False.elim (hne (Prod.mk.inj (Sum.inl.inj h)).1)
  · have hk := (Prod.mk.inj (Sum.inl.inj h)).2
    exact False.elim ((Finset.mem_sdiff.mp a.property).2 (hk.symm ▸ b.property))
  · exact congrArg (Sum.inl ∘ Sum.inr) (Subtype.ext (Prod.mk.inj (Sum.inl.inj h)).2)
  · exact False.elim (hne (Prod.mk.inj (Sum.inl.inj h)).1)
  · exact False.elim (hne (Prod.mk.inj (Sum.inl.inj h)).1.symm)
  · exact False.elim (hne (Prod.mk.inj (Sum.inl.inj h)).1.symm)
  · exact congrArg Sum.inr (Subtype.ext (Prod.mk.inj (Sum.inl.inj h)).2)

private theorem read_uniform (oldFamily currentFamily : IdealKey.Family)
    (hne : oldFamily ≠ currentFamily) (K KA : Finset LogicalKey) :
    (Measure.infinitePi (fun _ : freshBlock oldFamily currentFamily => IdealKey.wordLaw)).map
      (read oldFamily currentFamily K KA) =
      uniformOn (Set.univ : Set (Hist K KA × (KA → Word64))) := by
  let R := ↥(K \ KA)
  let e := (Equiv.sumArrowEquivProdArrow (KA ⊕ R) KA Word64).trans
    (Equiv.prodCongr (Equiv.sumArrowEquivProdArrow KA R Word64) (Equiv.refl _))
  have he : read oldFamily currentFamily K KA =
      e ∘ (fun fresh key => fresh (pick oldFamily currentFamily K KA key)) := rfl
  rw [he, ← Measure.map_map Measurable.of_discrete (by fun_prop),
    Measure.map_infinitePi_infinitePi_of_inj (pick_injective _ _ hne _ _),
    Measure.infinitePi_eq_pi]
  have hu : Measure.pi (fun _ : (KA ⊕ R) ⊕ KA => IdealKey.wordLaw) =
      uniformOn (Set.univ : Set ((KA ⊕ R) ⊕ KA → Word64)) := by
    simpa [IdealKey.wordLaw] using
      (uniformOn_pi (f := fun _ : (KA ⊕ R) ⊕ KA => (Set.univ : Set Word64))).symm
  rw [hu, HierarchyLevelOneProof.map_uniform_equiv e]

theorem coupling (oldFamily currentFamily : IdealKey.Family)
    (hne : oldFamily ≠ currentFamily) (row : TPGeom) (K KA : Finset LogicalKey)
    (producer : (LogicalKey → Nat) → TPInputs) :
    FiniteCoupling
      (Measure.infinitePi (fun _ : freshBlock oldFamily currentFamily => IdealKey.wordLaw))
      (law row K KA producer).toFinite (read oldFamily currentFamily K KA) := by
  change ∀ outcome : Hist K KA × (KA → Word64),
    (Measure.infinitePi (fun _ : freshBlock oldFamily currentFamily => IdealKey.wordLaw))
      ((read oldFamily currentFamily K KA) ⁻¹' {outcome}) ≤
      (Fintype.card (Hist K KA) : ℝ≥0∞)⁻¹ *
        (Fintype.card (KA → Word64) : ℝ≥0∞)⁻¹
  intro outcome
  rw [← Measure.map_apply (by unfold read; fun_prop) (measurableSet_singleton outcome),
    read_uniform _ _ hne, uniformOn_univ, Measure.count_singleton]
  rw [Fintype.card_prod, Nat.cast_mul, one_div,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

/-- The complete bounded preparation inherits its analytic budget on this
outside section. The producer can retain overflow records from earlier jobs. -/
theorem local_bound (oldFamily currentFamily : IdealKey.Family)
    (hne : oldFamily ≠ currentFamily) (row : TPGeom) (K1 K2 : Nat)
    (hv : row.Valid) (hwide : row.k ≤ 64)
    (hdfs : row.dfs = true → row.I + 1 < row.k)
    (hK1 : row.stashPages * row.C < K1) (hK2 : row.drainPages * row.C < K2)
    (K KA : Finset LogicalKey) (producer : (LogicalKey → Nat) → TPInputs)
    (unsh : Rec → Bool)
    (hshape : ∀ old, TPShape row (fun key => old key % row.T) (producer old))
    (hkeys : ∀ old, ((producer old).aAll.map Rec.key).toFinset = KA)
    (hload : KA.card ≤ 32 * row.T)
    (hlocal : ∀ old old', (∀ key ∈ K, old key = old' key) → producer old = producer old') :
    (Measure.infinitePi (fun _ : freshBlock oldFamily currentFamily => IdealKey.wordLaw))
      {inside | TPTiersFit row (producer (oldWords oldFamily currentFamily inside)) ∧
        (tpJob engineRule row unsh (currentWords oldFamily currentFamily inside)
          (producer (oldWords oldFamily currentFamily inside))).toBool = false} ≤
      tpBound row 32 1 K1 K2 := by
  classical
  let L := law row K KA producer
  have hL := law_valid row K KA producer hwide hshape hkeys hload
  have hbound := TPJob row L unsh 32 1 engineRule K1 K2 hv hL D1 hdfs hK1 hK2
  refine (FiniteCouplingProof.finite_transport_sub _ L.toFinite
    (read oldFamily currentFamily K KA) (coupling _ _ hne row K KA producer)
    (tpFailEvent L engineRule unsh) _ ?_).trans hbound
  intro inside hevent
  let sampled := read oldFamily currentFamily K KA inside
  have hold : ∀ key ∈ K,
      oldWords oldFamily currentFamily inside key = oldWord K KA sampled.1 key := by
    intro key hk
    by_cases ha : key ∈ KA
    · simp only [oldWord, dite_eq_left ha]
      rfl
    · have hr : key ∈ K \ KA := Finset.mem_sdiff.mpr ⟨hk, ha⟩
      simp only [oldWord, dite_eq_right ha, dite_eq_left hr]
      rfl
  have hinp := hlocal _ _ hold
  have hmem : ∀ r ∈ (producer (oldWords oldFamily currentFamily inside)).aAll,
      r.key ∈ KA := by
    intro r hr
    rw [← hkeys (oldWords oldFamily currentFamily inside)]
    exact List.mem_toFinset.mpr (List.mem_map_of_mem hr)
  have hcur : ∀ r ∈ (producer (oldWords oldFamily currentFamily inside)).aAll,
      currentWords oldFamily currentFamily inside r.key = L.wordFn sampled.2 r.key := by
    intro r hr
    change _ = if hx : r.key ∈ KA then _ else 0
    rw [dite_eq_left (hmem r hr)]
    rfl
  change TPTiersFit row (producer (oldWord K KA sampled.1)) ∧
    (tpJob engineRule row unsh (L.wordFn sampled.2)
      (producer (oldWord K KA sampled.1))).toBool = false
  rw [← hinp, ← TPJobWordLocal row unsh _ _ _ hcur]
  exact hevent

end RebuildBound.IdealTopPrepProof
