import RebuildBound.Spec.IdealDirectLocal
import RebuildBound.Proofs.IdealHierarchy
import RebuildBound.Proofs.FiniteCoupling
import RebuildBound.Proofs.AdaptiveLevelOneBU.Basic
import RebuildBound.Proofs.WordLocalDirect
import RebuildBound.Proofs.SelJob

/-! Each outside section has a finite projection onto exactly the keys of its
actual direct input. A one-point history couples that projection to the existing
analytic law, without indexing a finite global universe or counting unused keys. -/
namespace RebuildBound.IdealDirectLocalProof
open Model Model.DirectJob Spec Spec.IdealDirect MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem weight_sum (s : SepGeom) (inp : DirectJob.Inputs) (oldWord : LogicalKey → Nat) :
    ∑ hist, (localLaw s inp oldWord).weight hist = 1 := by
  change (∑ _ : Unit, (1 : ℝ≥0∞)) = 1
  simp

/-- Actual finite reads of the complete family have their exact uniform law. -/
def read (family : IdealKey.Family) (s : SepGeom) (inp : DirectJob.Inputs)
    (oldWord : LogicalKey → Nat) :
    (IdealHierarchy.familyBlock family → Word64) → (localLaw s inp oldWord).Key → Word64 :=
  IdealHierarchy.familyRead family (keysA inp ∪ keysB inp)

theorem read_uniform (family : IdealKey.Family) (s : SepGeom) (inp : DirectJob.Inputs)
    (oldWord : LogicalKey → Nat) :
    (Measure.infinitePi (fun _ : IdealHierarchy.familyBlock family => IdealKey.wordLaw)).map
      (read family s inp oldWord) =
      uniformOn (Set.univ : Set ((localLaw s inp oldWord).Key → Word64)) := by
  change (Measure.infinitePi (fun _ : IdealHierarchy.familyBlock family => IdealKey.wordLaw)).map
    (IdealHierarchy.familyRead family (keysA inp ∪ keysB inp)) =
    uniformOn (Set.univ : Set (↥(keysA inp ∪ keysB inp) → Word64))
  rw [IdealHierarchyProof.familyRead_uniform]
  simpa [IdealKey.wordLaw] using
    (uniformOn_pi (f := fun _ : ↥(keysA inp ∪ keysB inp) => (Set.univ : Set Word64))).symm

theorem coupling (family : IdealKey.Family) (s : SepGeom) (inp : DirectJob.Inputs)
    (oldWord : LogicalKey → Nat) :
    FiniteCoupling
      (Measure.infinitePi (fun _ : IdealHierarchy.familyBlock family => IdealKey.wordLaw))
      (localLaw s inp oldWord).toFinite
      (fun fresh => ((), read family s inp oldWord fresh)) := by
  change ∀ outcome : Unit × ((localLaw s inp oldWord).Key → Word64),
    (Measure.infinitePi (fun _ : IdealHierarchy.familyBlock family => IdealKey.wordLaw))
      {fresh | ((), read family s inp oldWord fresh) = outcome} ≤
      1 * (Fintype.card ((localLaw s inp oldWord).Key → Word64) : ℝ≥0∞)⁻¹
  intro outcome
  rcases outcome with ⟨hist, ws⟩
  cases hist
  have heq : {fresh | ((), read family s inp oldWord fresh) = ((), ws)} =
      read family s inp oldWord ⁻¹' {ws} := by
    ext fresh
    change ((), read family s inp oldWord fresh) = ((), ws) ↔ read family s inp oldWord fresh = ws
    exact ⟨fun h => congrArg Prod.snd h, fun h => congrArg (fun w => ((), w)) h⟩
  change (Measure.infinitePi (fun _ : IdealHierarchy.familyBlock family => IdealKey.wordLaw))
    {fresh | ((), read family s inp oldWord fresh) = ((), ws)} ≤ _
  rw [heq, ← Measure.map_apply (by unfold read IdealHierarchy.familyRead; fun_prop)
    (measurableSet_singleton ws), read_uniform, uniformOn_univ, Measure.count_singleton]
  simp

/-- A word-local event transfers from its actual infinite family section to
its finite analytic law. This is valid for every finite input, including empty
inputs and duplicates. -/
theorem transport (family : IdealKey.Family) (s : SepGeom) (inp : DirectJob.Inputs)
    (oldWord : LogicalKey → Nat) (P : (LogicalKey → Nat) → Prop)
    (hlocal : ∀ w w', (∀ x ∈ inp.aRecords ++ inp.bRecords, w x.key = w' x.key) →
      (P w ↔ P w')) :
    (Measure.infinitePi (fun _ : IdealHierarchy.familyBlock family => IdealKey.wordLaw))
      {fresh | P (familyWords family fresh)} ≤
      (localLaw s inp oldWord).prob (fun _ word => P word) := by
  apply FiniteCouplingProof.finite_transport_sub _ (localLaw s inp oldWord).toFinite
    (fun fresh => ((), read family s inp oldWord fresh)) (coupling family s inp oldWord)
    (fun _ word => P word) _
  intro fresh hfresh
  apply (hlocal _ _ ?_).1 hfresh
  intro x hx
  have hk : x.key ∈ keysA inp ∪ keysB inp := by
    rcases List.mem_append.mp hx with hx | hx
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hx))
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map_of_mem hx))
  simp only [FiniteJobLaw.wordFn]
  split_ifs with hmem
  · rfl
  · exact False.elim (hmem hk)

noncomputable def trivialD (s : SepGeom) (inp : DirectJob.Inputs) : ℝ≥0 :=
  ((((s.d - 1) * s.U : ℕ) : ℝ≥0) ^ (keysA inp).card)

/-- Shape, population and a trivial old density suffice for the current-home
term. This density is not used to claim the tighter early-A estimate. -/
theorem inputLaw (p : Geometry) (s : SepGeom) (load : Nat)
    (hc : ReferenceInputCompatible p s) (hk : s.k < 64) (hd : 2 ≤ s.d)
    (st : ReferenceTable) (ow w : LogicalKey → Nat) (prior fresh : List Bucket) (H : List Rec)
    (hH : st.records.Perm (DirectPrefix.winners H))
    (hlen : H.length + (DirectMasks.records prior).length ≤ load * ((s.d - 1) * s.U))
    (hu : (keysB ((referenceStep ow st ⟨p, w, prior⟩).inputs fresh)).card ≤ load * s.U) :
    SInputLaw (localLaw s ((referenceStep ow st ⟨p, w, prior⟩).inputs fresh) w) load
      (trivialD s ((referenceStep ow st ⟨p, w, prior⟩).inputs fresh)) := by
  classical
  set next := referenceStep ow st ⟨p, w, prior⟩ with hnext
  constructor
  · exact weight_sum _ _ _
  · intro hist hw
    exact DirectJobReferenceInputShapeFor p s hc ow w _ st prior fresh H hH
  · intro hist; rfl
  · intro hist hw
    exact (DirectJobReferenceInputMatch s next fresh).2.2
  · exact hk
  · have hperm := (DirectJobReferenceStep ow st ⟨p, w, prior⟩ H hH).1
    have he : keysA (next.inputs fresh) =
        ((DirectPrefix.winners (H ++ DirectMasks.records prior)).map Rec.key).toFinset :=
      List.toFinset_eq_of_perm _ _ (hperm.map Rec.key)
    have hn : (keysA (next.inputs fresh)).card ≤ load * ((s.d - 1) * s.U) := by
      rw [he]
      refine (List.toFinset_card_le _).trans ?_
      rw [List.length_map]
      exact ((HierarchyInvariantProof.prefix_sublist _).length_le).trans
        (by simpa only [List.length_append] using hlen)
    exact_mod_cast hn
  · exact_mod_cast hu
  · have hM : 0 < (s.d - 1) * s.U := by
      exact Nat.mul_pos (by omega) (by unfold SepGeom.U; positivity)
    exact AdaptiveLevelOneBUProof.trivial_density _ (weight_sum _ _ _) hM

end RebuildBound.IdealDirectLocalProof

namespace RebuildBound
open Model Model.DirectJob Spec Spec.IdealDirect IdealDirectLocalProof
open scoped ENNReal NNReal

theorem IdealDirectLocalB : IdealDirectLocalB_statement := by
  intro family g inp load cut hW hload hcut
  refine (transport family (selectedDirectSep 1) inp (fun _ => 0)
    (fun word => g.bCapacity < bExcess g word inp) ?_).trans ?_
  · intro w w' hw
    rw [AdaptiveLevelOneBUProof.bExcess_congr g w w' inp
      (fun x hx => hw x (List.mem_append_right _ hx))]
  · exact DirectJobBFiniteWords (localLaw (selectedDirectSep 1) inp (fun _ => 0))
      g load (fun _ _ => inp) cut (weight_sum _ _ _) hW (fun _ _ => rfl)
      (by exact_mod_cast hload) hcut

theorem IdealDirectLocalDigitOne : IdealDirectLocalDigitOne_statement := by
  intro family g inp oldWord load cut hg hd hW hload hcut
  refine (transport family (selectedDirectSep 1) inp oldWord
    (fun word => ∃ e, runJob g oldWord word inp = .failed e) ?_).trans ?_
  · intro w w' hw
    rw [DirectJobWordLocal g oldWord oldWord w w' inp (fun _ _ => rfl) hw]
  · exact DirectJobDigitOneFiniteWordsFor (localLaw (selectedDirectSep 1) inp oldWord)
      g load (fun _ _ => inp) cut hg hd (weight_sum _ _ _) hW (fun _ _ => rfl)
      (by exact_mod_cast hload) hcut

theorem IdealDirectLocalUnion : IdealDirectLocalUnion_statement := by
  intro family p g s load cut hc hs hk hd hHomes hhome hcut st ow w prior fresh H hH hlen
  dsimp only
  intro hu
  let inp := (referenceStep ow st ⟨p, w, prior⟩).inputs fresh
  have hLaw : SInputLaw (localLaw s inp w) load (trivialD s inp) :=
    inputLaw p s load hc hk hd st ow w prior fresh H hH hlen hu
  have hm : DirectJobInputMatch (localLaw s inp w) (fun _ _ => inp) :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩
  refine (transport family s inp w (fun word => g.outputCapacity < inp.excess g word) ?_).trans ?_
  · intro word word' hw
    rw [AdaptiveLevelOneBUProof.excess_congr g word word' inp hw]
  · refine (DirectJobUnionFiniteWords (localLaw s inp w) g load (trivialD s inp)
      (fun _ _ => inp) cut hs hLaw hm hc.1 hHomes hhome hcut).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right
    · apply SelJobAux.curDensity_mono s 64 hs.1
      exact_mod_cast SG1Proof.KAB_card_le _ hLaw hs
    · exact G3Proof.Phi_nonneg cut g.outputHomes 64 (by positivity) g.outputCapacity

end RebuildBound
