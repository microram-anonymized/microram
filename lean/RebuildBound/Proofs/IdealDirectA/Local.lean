import RebuildBound.Spec.IdealHierarchy
import RebuildBound.Proofs.IdealHierarchy
import RebuildBound.Proofs.FiniteCoupling
import RebuildBound.Proofs.DirectJobHistoryGeometry
import RebuildBound.Proofs.AdaptiveLevelOneA.Local
import RebuildBound.Spec.AdaptiveStepsJobs

/-! A direct A section has one fixed source history and two independently
sampled families. Only the finite keys of that history are projected; unused
coordinates never need a finite dictionary or a counting argument. -/
namespace RebuildBound.IdealDirectAProof
open Model Model.DirectJob Spec Spec.IdealHierarchy MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable def data (st : ReferenceTable) (olderWord : LogicalKey → Nat)
    (prior : List Bucket) (H : List Rec) : DirectHistoryData where
  KA := ((H ++ DirectMasks.records prior).map Rec.key).toFinset
  KB := ∅
  Base := Unit
  weight _ := 1
  before _ := st
  olderWord _ := olderWord
  chronology _ := H
  priorUnits _ _ := prior
  freshUnits _ _ := []

def freshBlock (oldFamily currentFamily : IdealKey.Family) : Set IdealKey.Coord :=
  familyBlock oldFamily ∪ familyBlock currentFamily

def oldWords (oldFamily currentFamily : IdealKey.Family)
    (fresh : freshBlock oldFamily currentFamily → Word64) : LogicalKey → Nat :=
  fun key => (fresh ⟨.inl (oldFamily, key), Or.inl rfl⟩).val

def currentWords (oldFamily currentFamily : IdealKey.Family)
    (fresh : freshBlock oldFamily currentFamily → Word64) : LogicalKey → Nat :=
  fun key => (fresh ⟨.inl (currentFamily, key), Or.inr rfl⟩).val

theorem data_valid (st : ReferenceTable) (olderWord : LogicalKey → Nat)
    (prior : List Bucket) (H : List Rec) (s : SepGeom) (load : Nat)
    (hH : st.records.Perm (DirectPrefix.winners H))
    (hlen : H.length + (DirectMasks.records prior).length ≤ load * ((s.d - 1) * s.U)) :
    (data st olderWord prior H).ValidFor s load := by
  refine ⟨?_, fun _ => hH, fun _ _ => rfl, ?_, ?_, ?_⟩
  · change (∑ _ : Unit, (1 : ℝ≥0∞)) = 1
    simp
  · intro _ _
    simp [data, DirectMasks.records]
  · exact (List.toFinset_card_le _).trans (by simpa only [List.length_map,
      List.length_append] using hlen)
  · simp [data]

private def pick (oldFamily currentFamily : IdealKey.Family)
    (KA KC : Finset LogicalKey) : KA ⊕ KC → freshBlock oldFamily currentFamily
  | .inl key => ⟨.inl (oldFamily, key.val), Or.inl rfl⟩
  | .inr key => ⟨.inl (currentFamily, key.val), Or.inr rfl⟩

private theorem pick_injective (oldFamily currentFamily : IdealKey.Family)
    (hne : oldFamily ≠ currentFamily) (KA KC : Finset LogicalKey) :
    Function.Injective (pick oldFamily currentFamily KA KC) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext (Prod.mk.inj (Sum.inl.inj h)).2)
    | inr b => exact False.elim (hne (Prod.mk.inj (Sum.inl.inj h)).1)
  | inr a =>
    cases b with
    | inl b => exact False.elim (hne (Prod.mk.inj (Sum.inl.inj h)).1.symm)
    | inr b => exact congrArg Sum.inr (Subtype.ext (Prod.mk.inj (Sum.inl.inj h)).2)

private def read (oldFamily currentFamily : IdealKey.Family)
    (KA KC : Finset LogicalKey) (fresh : freshBlock oldFamily currentFamily → Word64) :
    (KA → Word64) × (KC → Word64) :=
  (fun key => fresh ⟨.inl (oldFamily, key.val), Or.inl rfl⟩,
   fun key => fresh ⟨.inl (currentFamily, key.val), Or.inr rfl⟩)

private theorem read_uniform (oldFamily currentFamily : IdealKey.Family)
    (hne : oldFamily ≠ currentFamily) (KA KC : Finset LogicalKey) :
    (Measure.infinitePi (fun _ : freshBlock oldFamily currentFamily => IdealKey.wordLaw)).map
      (read oldFamily currentFamily KA KC) =
      uniformOn (Set.univ : Set ((KA → Word64) × (KC → Word64))) := by
  let e := Equiv.sumArrowEquivProdArrow KA KC Word64
  have he : read oldFamily currentFamily KA KC =
      e ∘ (fun fresh key => fresh (pick oldFamily currentFamily KA KC key)) := rfl
  rw [he, ← Measure.map_map Measurable.of_discrete (by fun_prop),
    Measure.map_infinitePi_infinitePi_of_inj (pick_injective _ _ hne _ _),
    Measure.infinitePi_eq_pi]
  have hu : Measure.pi (fun _ : KA ⊕ KC => IdealKey.wordLaw) =
      uniformOn (Set.univ : Set (KA ⊕ KC → Word64)) := by
    simpa [IdealKey.wordLaw] using
      (uniformOn_pi (f := fun _ : KA ⊕ KC => (Set.univ : Set Word64))).symm
  rw [hu, HierarchyLevelOneProof.map_uniform_equiv e]

private theorem coupling (oldFamily currentFamily : IdealKey.Family)
    (hne : oldFamily ≠ currentFamily) (p : Geometry) (s : SepGeom)
    (st : ReferenceTable) (olderWord : LogicalKey → Nat) (prior : List Bucket) (H : List Rec) :
    let d := data st olderWord prior H
    let L := d.lawFor p s
    FiniteCoupling
      (Measure.infinitePi (fun _ : freshBlock oldFamily currentFamily => IdealKey.wordLaw))
      L.toFinite (fun fresh =>
        let sampled := read oldFamily currentFamily d.KA (L.KA ∪ L.KB) fresh
        (((), sampled.1), sampled.2)) := by
  let d := data st olderWord prior H
  let L := d.lawFor p s
  change ∀ outcome : (Unit × (d.KA → Word64)) × (↥(L.KA ∪ L.KB) → Word64),
    (Measure.infinitePi (fun _ : freshBlock oldFamily currentFamily => IdealKey.wordLaw))
      {fresh | (((), (read oldFamily currentFamily d.KA (L.KA ∪ L.KB) fresh).1),
        (read oldFamily currentFamily d.KA (L.KA ∪ L.KB) fresh).2) = outcome} ≤
      (1 * (Fintype.card (d.KA → Word64) : ℝ≥0∞)⁻¹) *
        (Fintype.card (↥(L.KA ∪ L.KB) → Word64) : ℝ≥0∞)⁻¹
  intro outcome
  rcases outcome with ⟨⟨hist, old⟩, current⟩
  cases hist
  have he : {fresh | (((), (read oldFamily currentFamily d.KA (L.KA ∪ L.KB) fresh).1),
      (read oldFamily currentFamily d.KA (L.KA ∪ L.KB) fresh).2) = (((), old), current)} =
      read oldFamily currentFamily d.KA (L.KA ∪ L.KB) ⁻¹' {(old, current)} := by
    ext fresh
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
      true_and, Prod.ext_iff]
  change (Measure.infinitePi (fun _ : freshBlock oldFamily currentFamily => IdealKey.wordLaw))
    {fresh | (((), (read oldFamily currentFamily d.KA (L.KA ∪ L.KB) fresh).1),
      (read oldFamily currentFamily d.KA (L.KA ∪ L.KB) fresh).2) = (((), old), current)} ≤ _
  rw [he, ← Measure.map_apply (by unfold read; fun_prop)
    (measurableSet_singleton (old, current)), read_uniform _ _ hne,
    uniformOn_univ, Measure.count_singleton]
  change 1 / (Fintype.card ((d.KA → Word64) × (L.Key → Word64)) : ℝ≥0∞) ≤
    (1 * (Fintype.card (d.KA → Word64) : ℝ≥0∞)⁻¹) *
      (Fintype.card (L.Key → Word64) : ℝ≥0∞)⁻¹
  rw [Fintype.card_prod, Nat.cast_mul, one_div,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _)), one_mul]

/-- Project precisely the finite source keys of the two fresh families. The
actual predecessor may publish or take the unrestricted reference fallback. -/
theorem transport (oldFamily currentFamily : IdealKey.Family)
    (hne : oldFamily ≠ currentFamily) (p g : Geometry) (s : SepGeom)
    (st : ReferenceTable) (olderWord : LogicalKey → Nat) (prior : List Bucket) (H : List Rec)
    (hH : st.records.Perm (DirectPrefix.winners H)) :
    (Measure.infinitePi (fun _ : freshBlock oldFamily currentFamily => IdealKey.wordLaw))
      {fresh | levelOneA g (currentWords oldFamily currentFamily fresh)
        ((referenceStep olderWord st ⟨p, oldWords oldFamily currentFamily fresh, prior⟩).inputs [])} ≤
    ((data st olderWord prior H).lawFor p s).prob (fun hist word =>
      levelOneA g word ((data st olderWord prior H).directFor p hist word)) := by
  let d := data st olderWord prior H
  let L := d.lawFor p s
  apply FiniteCouplingProof.finite_transport_sub _ L.toFinite _
    (coupling oldFamily currentFamily hne p s st olderWord prior H)
    (fun hist word => levelOneA g word (d.directFor p hist word))
  intro fresh hfresh
  let sampled := read oldFamily currentFamily d.KA (L.KA ∪ L.KB) fresh
  have hmem : ∀ x ∈ H ++ DirectMasks.records prior, x.key ∈ d.KA := by
    intro x hx
    exact List.mem_toFinset.mpr (List.mem_map_of_mem hx)
  have hkeys : ∀ x ∈ st.records ++ DirectMasks.records prior, x.key ∈ d.KA := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hmem x (List.mem_append_left _
        ((HierarchyInvariantProof.prefix_sublist H).subset (hH.mem_iff.mp hx)))
    · exact hmem x (List.mem_append_right _ hx)
  have hold : ∀ key ∈ d.KA,
      oldWords oldFamily currentFamily fresh key = d.word sampled.1 key := by
    intro key hk
    simp only [DirectHistoryData.word, dite_eq_left hk]
    rfl
  have hr : runJob p olderWord (oldWords oldFamily currentFamily fresh) (st.inputs prior) =
      runJob p olderWord (d.word sampled.1) (st.inputs prior) :=
    DirectJobWordLocal p olderWord olderWord _ _ (st.inputs prior) (fun _ _ => rfl)
      (fun x hx => hold x.key (hkeys x hx))
  have hstate : referenceStep olderWord st
      ⟨p, oldWords oldFamily currentFamily fresh, prior⟩ = d.stateFor p ((), sampled.1) := by
    change referenceStep olderWord st ⟨p, oldWords oldFamily currentFamily fresh, prior⟩ =
      referenceStep olderWord st ⟨p, d.word sampled.1, prior⟩
    unfold referenceStep
    dsimp only
    rw [hr]
  have hout : ∀ x ∈ (d.stateFor p ((), sampled.1)).records, x.key ∈ d.KA := by
    intro x hx
    have hp := (DirectJobReferenceStep olderWord st ⟨p, d.word sampled.1, prior⟩ H hH).1
    exact hmem x ((HierarchyInvariantProof.prefix_sublist _).subset (hp.mem_iff.mp hx))
  have hcur : ∀ x ∈ (d.stateFor p ((), sampled.1)).records,
      currentWords oldFamily currentFamily fresh x.key = L.wordFn sampled.2 x.key := by
    intro x hx
    have hk : x.key ∈ L.KA ∪ L.KB := Finset.mem_union_left _ (hout x hx)
    simp only [SJobLaw.wordFn, dite_eq_left hk]
    rfl
  change levelOneA g (currentWords oldFamily currentFamily fresh)
    ((referenceStep olderWord st ⟨p, oldWords oldFamily currentFamily fresh, prior⟩).inputs []) at hfresh
  rw [hstate] at hfresh
  obtain ⟨hfit, hwit⟩ := hfresh
  have hw := AdaptiveLevelOneAProof.aWitness_congr g
    (currentWords oldFamily currentFamily fresh) (L.wordFn sampled.2)
    ((d.stateFor p ((), sampled.1)).inputs [])
    (d.directFor p ((), sampled.1) (L.wordFn sampled.2)) rfl rfl hcur
  exact ⟨hfit, hwit.imp hw.1.mp hw.2.mp⟩

end RebuildBound.IdealDirectAProof
