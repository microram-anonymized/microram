import RebuildBound.Proofs.IdealDirectA.Local
import RebuildBound.Proofs.AdaptiveSepA.Cell
import RebuildBound.Proofs.OldWordDensity

/-! A separated early-A section projects the old family on a finite source
set and the new family on the fixed A population. Extra old source words are
part of the history. The old-home density is its exact uniform marginal. -/
namespace RebuildBound.IdealSepAProof
open Model Model.DirectJob Spec Spec.IdealHierarchy MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open IdealDirectAProof (freshBlock oldWords currentWords)

abbrev Hist (K KA : Finset LogicalKey) :=
  (KA → Word64) × (↥(K \ KA) → Word64)

noncomputable def oldWord (K KA : Finset LogicalKey) (hist : Hist K KA) : LogicalKey → Nat :=
  fun key => if hA : key ∈ KA then (hist.1 ⟨key, hA⟩).val else
    if hK : key ∈ K \ KA then (hist.2 ⟨key, hK⟩).val else 0

noncomputable def law (row : SepGeom) (K KA : Finset LogicalKey)
    (producer : (LogicalKey → Nat) → SInputs) : SJobLaw row where
  KA := KA
  KB := ∅
  W := 64
  Hist := Hist K KA
  weight _ := (Fintype.card (Hist K KA) : ℝ≥0∞)⁻¹
  aIn hist := ((producer (oldWord K KA hist)).aMain, (producer (oldWord K KA hist)).aTier)
  wOld := oldWord K KA
  bIn _ _ := (List.replicate row.U (Bucket.empty row.C), List.replicate row.bTierPages [])

theorem law_valid (row : SepGeom) (K KA : Finset LogicalKey)
    (producer : (LogicalKey → Nat) → SInputs)
    (hrow : HierarchySepLawProof.RowOK row) (hd : 2 ≤ row.d)
    (hshape : ∀ old current, SInputShape row old current
      (DirectJobABoundsProof.aOnlyInputs row (producer old)))
    (hkeys : ∀ old, ((producer old).aAll.map Rec.key).toFinset = KA)
    (hload : KA.card ≤ 32 * ((row.d - 1) * row.U)) :
    SInputLaw (law row K KA producer) 32 (row.oldDensity 64 KA.card) where
  weight_sum := by
    change (∑ _ : Hist K KA, (Fintype.card (Hist K KA) : ℝ≥0∞)⁻¹) = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)
  shape hist current := hshape (oldWord K KA hist) _
  aKeys hist := hkeys _
  bKeys hist current := by
    have hblank : (List.replicate row.U (Bucket.empty row.C)).flatMap Bucket.recs = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro b hb
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hb
      simp [Bucket.empty, Bucket.recs]
    change (((List.replicate row.U (Bucket.empty row.C)).flatMap Bucket.recs ++
      (List.replicate row.bTierPages ([] : List Rec)).flatten).map Rec.key).toFinset = ∅
    simp [hblank]
  wide := hrow.1
  aLoad := by exact_mod_cast hload
  bLoad := by change ((∅ : Finset LogicalKey).card : ℝ≥0) ≤ _; simp
  density := by
    intro target
    have hden := OldWordDensity row KA target (by omega) hrow.2.1
    refine le_trans (le_of_eq ?_) (le_trans (le_of_eq
      (HierarchySepLawProof.density_eq KA (↥(K \ KA) → Word64)
        (fun h => ∀ x : KA, row.oldHome (h x) = (target x : Nat)))) hden)
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun hist _ => ?_
    have heq : (∀ x : KA, row.oldHome ((law row K KA producer).wOld hist x) =
        (target x : Nat)) ↔ (∀ x : KA, row.oldHome (hist.1 x) = (target x : Nat)) := by
      apply forall_congr'
      intro x
      simp only [law, oldWord, dite_eq_left x.property]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact absurd (heq.mp h₁) h₂
    · exact absurd (heq.mpr h₂) h₁
    · rfl

def read (oldFamily currentFamily : IdealKey.Family) (K KA : Finset LogicalKey)
    (inside : freshBlock oldFamily currentFamily → Word64) :
    Hist K KA × (↥(KA ∪ (∅ : Finset LogicalKey)) → Word64) :=
  ((fun key => inside ⟨.inl (oldFamily, key.val), Or.inl rfl⟩,
    fun key => inside ⟨.inl (oldFamily, key.val), Or.inl rfl⟩),
    fun key => inside ⟨.inl (currentFamily, key.val), Or.inr rfl⟩)

private def pick (oldFamily currentFamily : IdealKey.Family) (K KA : Finset LogicalKey) :
    (KA ⊕ ↥(K \ KA)) ⊕ ↥(KA ∪ (∅ : Finset LogicalKey)) → freshBlock oldFamily currentFamily
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
      uniformOn (Set.univ : Set (Hist K KA × (↥(KA ∪ (∅ : Finset LogicalKey)) → Word64))) := by
  let KC := ↥(KA ∪ (∅ : Finset LogicalKey))
  let R := ↥(K \ KA)
  let e := (Equiv.sumArrowEquivProdArrow (KA ⊕ R) KC Word64).trans
    (Equiv.prodCongr (Equiv.sumArrowEquivProdArrow KA R Word64) (Equiv.refl _))
  have he : read oldFamily currentFamily K KA =
      e ∘ (fun fresh key => fresh (pick oldFamily currentFamily K KA key)) := rfl
  rw [he, ← Measure.map_map Measurable.of_discrete (by fun_prop),
    Measure.map_infinitePi_infinitePi_of_inj (pick_injective _ _ hne _ _),
    Measure.infinitePi_eq_pi]
  have hu : Measure.pi (fun _ : (KA ⊕ R) ⊕ KC => IdealKey.wordLaw) =
      uniformOn (Set.univ : Set ((KA ⊕ R) ⊕ KC → Word64)) := by
    simpa [IdealKey.wordLaw] using
      (uniformOn_pi (f := fun _ : (KA ⊕ R) ⊕ KC => (Set.univ : Set Word64))).symm
  rw [hu, HierarchyLevelOneProof.map_uniform_equiv e]

theorem coupling (oldFamily currentFamily : IdealKey.Family)
    (hne : oldFamily ≠ currentFamily) (row : SepGeom) (K KA : Finset LogicalKey)
    (producer : (LogicalKey → Nat) → SInputs) :
    FiniteCoupling
      (Measure.infinitePi (fun _ : freshBlock oldFamily currentFamily => IdealKey.wordLaw))
      (law row K KA producer).toFinite (read oldFamily currentFamily K KA) := by
  change ∀ outcome : Hist K KA × (↥(KA ∪ (∅ : Finset LogicalKey)) → Word64),
    (Measure.infinitePi (fun _ : freshBlock oldFamily currentFamily => IdealKey.wordLaw))
      ((read oldFamily currentFamily K KA) ⁻¹' {outcome}) ≤
      (Fintype.card (Hist K KA) : ℝ≥0∞)⁻¹ *
        (Fintype.card (↥(KA ∪ (∅ : Finset LogicalKey)) → Word64) : ℝ≥0∞)⁻¹
  intro outcome
  rw [← Measure.map_apply (by unfold read; fun_prop) (measurableSet_singleton outcome),
    read_uniform _ _ hne, uniformOn_univ, Measure.count_singleton]
  rw [Fintype.card_prod, Nat.cast_mul, one_div,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

/-- Fixing the outside environment leaves a finite old-source restriction and
an independent current word for each A key. Both witness events ignore B. -/
theorem local_bound (oldFamily currentFamily : IdealKey.Family)
    (hne : oldFamily ≠ currentFamily) (row : SepGeom)
    (hrow : HierarchySepLawProof.RowOK row) (hd : 2 ≤ row.d)
    (hv : row.Valid) (hC : row.C = 64) (hIK : row.I < row.K)
    (hcut : row.stashPages * row.C < 256)
    (K KA : Finset LogicalKey) (hKA : KA ⊆ K)
    (producer : (LogicalKey → Nat) → SInputs)
    (hshape : ∀ old current, SInputShape row old current
      (DirectJobABoundsProof.aOnlyInputs row (producer old)))
    (hkeys : ∀ old, ((producer old).aAll.map Rec.key).toFinset = KA)
    (hload : KA.card ≤ 32 * ((row.d - 1) * row.U))
    (hlocal : ∀ old old', (∀ key ∈ K, old key = old' key) →
      (producer old).aMain = (producer old').aMain ∧
      (producer old).aTier = (producer old').aTier) :
    (Measure.infinitePi (fun _ : freshBlock oldFamily currentFamily => IdealKey.wordLaw))
      {inside | sharedARouteWitness row (oldWords oldFamily currentFamily inside)
          (currentWords oldFamily currentFamily inside)
          (producer (oldWords oldFamily currentFamily inside)) ∨
        sharedARangeWitness row (currentWords oldFamily currentFamily inside)
          (producer (oldWords oldFamily currentFamily inside))} ≤ selSepABound row := by
  classical
  let L := law row K KA producer
  have hL := law_valid row K KA producer hrow hd hshape hkeys hload
  have hbound := AdaptiveSepAProof.aBound row L 32 (row.oldDensity 64 KA.card) 256 hv hL
    (by norm_num) (by rw [hC]; norm_num) hIK hcut
  refine (FiniteCouplingProof.finite_transport_sub _ L.toFinite
    (read oldFamily currentFamily K KA) (coupling _ _ hne row K KA producer)
    (fun hist w => sharedARouteWitness row (L.wOld hist) w (L.inputs hist w) ∨
      sRangeEvent row L engineRule hist w) _ ?_).trans
    (hbound.trans (AdaptiveSepAProof.sepABound_mono row 64 32 256 hv.1
      (HierarchySepLawProof.oldDensity_mono hrow hload) hload))
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
  obtain ⟨hm, ht⟩ := hlocal _ _ hold
  have hmem : ∀ r ∈ (producer (oldWords oldFamily currentFamily inside)).aAll,
      r.key ∈ KA := by
    intro r hr
    rw [← hkeys (oldWords oldFamily currentFamily inside)]
    exact List.mem_toFinset.mpr (List.mem_map_of_mem hr)
  have hcur : ∀ r ∈ (producer (oldWords oldFamily currentFamily inside)).aAll,
      currentWords oldFamily currentFamily inside r.key = L.wordFn sampled.2 r.key := by
    intro r hr
    have hk : r.key ∈ KA ∪ (∅ : Finset LogicalKey) := Finset.mem_union_left _ (hmem r hr)
    change _ = if hx : r.key ∈ KA ∪ (∅ : Finset LogicalKey) then _ else 0
    rw [dite_eq_left hk]
    rfl
  have hwold : ∀ r ∈ (producer (oldWords oldFamily currentFamily inside)).aAll,
      oldWords oldFamily currentFamily inside r.key = L.wOld sampled.1 r.key :=
    fun r hr => hold r.key (hKA (hmem r hr))
  have hm' : (producer (oldWords oldFamily currentFamily inside)).aMain =
      (L.inputs sampled.1 (L.wordFn sampled.2)).aMain := hm
  have ht' : (producer (oldWords oldFamily currentFamily inside)).aTier =
      (L.inputs sampled.1 (L.wordFn sampled.2)).aTier := ht
  exact hevent.imp
    (AdaptiveSepAProof.route_congr row _ _ _ _ _ _ hm' ht' hwold hcur).mp
    (AdaptiveSepAProof.range_congr row _ _ _ _ hm' ht' hcur).mp

end RebuildBound.IdealSepAProof
