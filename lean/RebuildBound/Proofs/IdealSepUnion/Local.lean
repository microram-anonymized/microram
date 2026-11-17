import RebuildBound.Spec.IdealDirectLocal
import RebuildBound.Proofs.IdealHierarchy
import RebuildBound.Proofs.SCanon
import RebuildBound.Proofs.AdaptiveSepU
import RebuildBound.Proofs.FiniteCoupling

/-! A separated union section reads only its complete key sets. Its physical
B layout may vary with the current family. Compare the excess with canonical
producers at the same keys; a one-point old history suffices for this term.
No old-home independence claim is used or obtained here. -/
namespace RebuildBound.IdealSepUnionProof
open Model Spec Spec.IdealHierarchy Spec.IdealDirect MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Canonical producers with a fixed old-home vector. Only current words are
random; the deliberately trivial old-home density is enough for a union bound. -/
noncomputable def localLaw (g : SepGeom) (KA KB : Finset LogicalKey)
    (old : KA → Fin ((g.d - 1) * g.U)) : SJobLaw g where
  KA := KA
  KB := KB
  W := 64
  Hist := Unit
  weight _ := 1
  aIn _ := (canonicalSepLaw g KA KB 64).aIn old
  wOld _ := (canonicalSepLaw g KA KB 64).wOld old
  bIn _ := (canonicalSepLaw g KA KB 64).bIn old

/-- Restrict exactly the two populations' union. Empty populations and keys
shared between A and B require no exceptional cases. -/
theorem local_bound (family : IdealKey.Family) (g : SepGeom)
    (hg : g.Valid) (hk : g.k < 64) (hC : g.C = 64) (hpages : 1 ≤ g.bTierPages)
    (hcut : min (g.stashPages * g.C) (g.tierPages * g.C) < 256)
    (KA KB : Finset LogicalKey)
    (hloadA : KA.card ≤ 32 * ((g.d - 1) * g.U))
    (hloadB : KB.card ≤ 32 * g.U)
    (input : (familyBlock family → Word64) → SInputs)
    (hA : ∀ fresh, ((input fresh).aAll.map Rec.key).Nodup ∧
      ((input fresh).aAll.map Rec.key).toFinset = KA)
    (hB : ∀ fresh, ((input fresh).bAll.map Rec.key).Nodup ∧
      ((input fresh).bAll.map Rec.key).toFinset = KB) :
    (Measure.infinitePi (fun _ : familyBlock family => IdealKey.wordLaw))
      {fresh | min (g.stashPages * g.C) (g.tierPages * g.C) <
        sHomeExcess g (familyWords family fresh) (input fresh)} ≤ selSepUBound g := by
  classical
  let old : KA → Fin ((g.d - 1) * g.U) := fun _ => ⟨0, SG1Proof.M_pos hg⟩
  let L := localLaw g KA KB old
  have hcanon := SCanonical g KA KB 64 32 hg hpages hk
    (by exact_mod_cast hloadA) (by exact_mod_cast hloadB)
  have hsum : ∑ hist, L.weight hist = 1 := by
    change (∑ _ : Unit, (1 : ℝ≥0∞)) = 1
    simp
  have hL : SInputLaw L 32 (((((g.d - 1) * g.U : Nat) : ℝ≥0)) ^ KA.card) := by
    refine ⟨hsum, ?_, ?_, ?_, hk, ?_, ?_, ?_⟩
    · intro _ w
      exact hcanon.shape old w
    · intro _
      exact hcanon.aKeys old
    · intro _ w
      exact hcanon.bKeys old w
    · exact_mod_cast hloadA
    · exact_mod_cast hloadB
    · exact AdaptiveSepUProof.trivial_density L hsum (SG1Proof.M_pos hg)
  let read : (familyBlock family → Word64) → L.Key → Word64 :=
    familyRead family (KA ∪ KB)
  have hread : Measurable read := by unfold read familyRead; fun_prop
  have huniform : (Measure.infinitePi
      (fun _ : familyBlock family => IdealKey.wordLaw)).map read =
      uniformOn (Set.univ : Set (L.Key → Word64)) := by
    change (Measure.infinitePi (fun _ : familyBlock family => IdealKey.wordLaw)).map
      (familyRead family (KA ∪ KB)) =
      uniformOn (Set.univ : Set (↥(KA ∪ KB) → Word64))
    rw [IdealHierarchyProof.familyRead_uniform]
    simpa [IdealKey.wordLaw] using
      (uniformOn_pi (f := fun _ : ↥(KA ∪ KB) => (Set.univ : Set Word64))).symm
  have hcouple : FiniteCoupling
      (Measure.infinitePi (fun _ : familyBlock family => IdealKey.wordLaw)) L.toFinite
      (fun fresh => ((), read fresh)) := by
    change ∀ outcome : Unit × (L.Key → Word64),
      (Measure.infinitePi (fun _ : familyBlock family => IdealKey.wordLaw))
        {fresh | ((), read fresh) = outcome} ≤
          1 * (Fintype.card (L.Key → Word64) : ℝ≥0∞)⁻¹
    rintro ⟨hist, ws⟩
    cases hist
    have heq : {fresh | ((), read fresh) = ((), ws)} = read ⁻¹' {ws} := by
      ext fresh
      change ((), read fresh) = ((), ws) ↔ read fresh = ws
      exact ⟨fun h => congrArg Prod.snd h, fun h => congrArg (fun w => ((), w)) h⟩
    change (Measure.infinitePi (fun _ : familyBlock family => IdealKey.wordLaw))
      {fresh | ((), read fresh) = ((), ws)} ≤
        1 * (Fintype.card (L.Key → Word64) : ℝ≥0∞)⁻¹
    rw [heq, ← Measure.map_apply hread (measurableSet_singleton ws), huniform,
      uniformOn_univ, Measure.count_singleton]
    simp
  refine (FiniteCouplingProof.finite_transport_sub _ L.toFinite
    (fun fresh => ((), read fresh)) hcouple
    (fun hist w => min (g.stashPages * g.C) (g.tierPages * g.C) <
      sHomeExcess g w (L.inputs hist w)) _ ?_).trans
    (AdaptiveSepUProof.union_bound L hL rfl hg hC hcut)
  intro fresh hfresh
  have heq := AdaptiveSepUProof.sHomeExcess_congr g
    (hA fresh).1 (hB fresh).1 (hL.shape () (read fresh)).aNodup
    (hL.shape () (read fresh)).bNodup
    ((hA fresh).2.trans (hL.aKeys ()).symm)
    ((hB fresh).2.trans (hL.bKeys () (read fresh)).symm) (w₁ := familyWords family fresh)
    (w₂ := L.wordFn (read fresh)) (by
      intro key hkey
      rw [(hA fresh).2, (hB fresh).2] at hkey
      change _ = if hk : key ∈ KA ∪ KB then _ else 0
      rw [dite_eq_left hkey]
      rfl)
  change min (g.stashPages * g.C) (g.tierPages * g.C) <
    sHomeExcess g (L.wordFn (read fresh)) (L.inputs () (L.wordFn (read fresh)))
  exact lt_of_lt_of_eq hfresh heq

end RebuildBound.IdealSepUnionProof
