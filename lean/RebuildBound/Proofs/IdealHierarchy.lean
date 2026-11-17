import RebuildBound.Spec.IdealHierarchy
import RebuildBound.Proofs.IdealKeyLaw
import RebuildBound.Proofs.HierarchyInvariant.Basic
import RebuildBound.Proofs.HierarchyHorizonFree
import RebuildBound.Proofs.HierarchyLevelOne.Uniform
import RebuildBound.Spec.OnlineBase

/-! Canonical routing and dummy tapes for the byte-key hierarchy. Actual reads
use logical keys directly; finite compatibility views restrict the same tape. -/



namespace RebuildBound
open Model Model.Hierarchy Spec Spec.IdealHierarchy
open MeasureTheory ProbabilityTheory

namespace IdealHierarchyProof

/-- Injective finite selections have the uniform function law. -/
theorem selection_uniform {ι : Type} [Fintype ι] (pick : ι → IdealKey.Coord)
    (hpick : Function.Injective pick) :
    IdealKey.tapeLaw.map (fun tape i => tape (pick i)) =
      uniformOn (Set.univ : Set (ι → Word64)) := by
  rw [IdealKeySelection ι pick hpick]
  simpa [IdealKey.wordLaw] using
    (uniformOn_pi (f := fun _ : ι => (Set.univ : Set Word64))).symm

/-- Subtype projection makes every finite family selection injective. -/
theorem family_index_injective (cfg : Config) (N : Nat) :
    Function.Injective (fun p : Coord cfg × KeyIndex N =>
      (Sum.inl (p.1.val, p.2.val) : IdealKey.Coord)) := by
  intro a b h
  have hp := Prod.mk.inj (Sum.inl.inj h)
  exact Prod.ext (Subtype.ext hp.1) (Subtype.ext hp.2)

/-- A fixed finite family restriction has exactly the legacy uniform law. -/
theorem family_uniform (cfg : Config) (N : Nat) :
    IdealKey.tapeLaw.map (familyTape cfg N) =
      uniformOn (Set.univ : Set (FamilyTape cfg N)) := by
  classical
  let pick : Coord cfg × KeyIndex N → IdealKey.Coord :=
    fun p => .inl (p.1.val, p.2.val)
  let e := Equiv.curry (Coord cfg) (KeyIndex N) Word64
  have he : familyTape cfg N = e ∘ (fun tape p => tape (pick p)) := rfl
  rw [he, ← Measure.map_map Measurable.of_discrete (by fun_prop),
    selection_uniform pick (family_index_injective cfg N),
    HierarchyLevelOneProof.map_uniform_equiv e]

/-- Finite real and dummy coordinates remain distinct even at equal numbers. -/
def jointIndex (cfg : Config) (N n m : Nat) :
    (Coord cfg × KeyIndex N) ⊕ (Fin n × Fin m) → IdealKey.Coord
  | .inl p => .inl (p.1.val, p.2.val)
  | .inr p => .inr (p.1.val, p.2.val)

theorem jointIndex_injective (cfg : Config) (N n m : Nat) :
    Function.Injective (jointIndex cfg N n m) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      exact congrArg Sum.inl (family_index_injective cfg N h)
    | inr b => cases h
  | inr a =>
    cases b with
    | inl b => cases h
    | inr b =>
      have hp := Prod.mk.inj (Sum.inr.inj h)
      exact congrArg Sum.inr (Prod.ext (Fin.ext hp.1) (Fin.ext hp.2))

/-- Both finite views are restrictions of a single uniform function selection. -/
theorem joint_uniform (cfg : Config) (N n m : Nat) :
    IdealKey.tapeLaw.map (fun tape => (familyTape cfg N tape, dummyTape n m tape)) =
      uniformOn (Set.univ : Set (FamilyTape cfg N × DummyTape n m)) := by
  classical
  let e := (Equiv.sumArrowEquivProdArrow (Coord cfg × KeyIndex N) (Fin n × Fin m)
      Word64).trans
    (Equiv.prodCongr (Equiv.curry (Coord cfg) (KeyIndex N) Word64)
      (Equiv.curry (Fin n) (Fin m) Word64))
  have he : (fun tape => (familyTape cfg N tape, dummyTape n m tape)) =
      e ∘ (fun tape p => tape (jointIndex cfg N n m p)) := rfl
  rw [he, ← Measure.map_map Measurable.of_discrete (by fun_prop),
    selection_uniform _ (jointIndex_injective cfg N n m),
    HierarchyLevelOneProof.map_uniform_equiv e]

/-- Selecting distinct keys inside the complete family block is still an
injective coordinate restriction, even when the chosen finite set varies
with a separately fixed outside environment. -/
theorem familyRead_uniform (family : IdealKey.Family) (keys : Finset LogicalKey) :
    (Measure.infinitePi (fun _ : familyBlock family => IdealKey.wordLaw)).map
      (familyRead family keys) = Measure.pi (fun _ : keys => IdealKey.wordLaw) := by
  let pick : keys → familyBlock family := fun key => ⟨.inl (family, key.val), rfl⟩
  have hpick : Function.Injective pick := by
    intro a b h
    have hcoord := congrArg Subtype.val h
    exact Subtype.ext (Prod.mk.inj (Sum.inl.inj hcoord)).2
  change (Measure.infinitePi (fun _ : familyBlock family => IdealKey.wordLaw)).map
    (fun tape key => tape (pick key)) = _
  rw [Measure.map_infinitePi_infinitePi_of_inj hpick, Measure.infinitePi_eq_pi]

end IdealHierarchyProof

/-- Actual model words read exact logical keys and retain their 64-bit range. -/
theorem IdealHierarchyWords : IdealHierarchyWords_statement := by
  refine ⟨fun tape level ordinal key => (tape _).isLt,
    fun tape slot table => (tape _).isLt, ?_⟩
  intro cfg tape level ordinal key
  simp only [jobWord, words, Prod.mk.eta]

/-- Adopted copies share their receiver's canonical routing word. -/
theorem IdealHierarchyCarry : IdealHierarchyCarry_statement := by
  intro cfg tape level ordinal h2 hL hb
  exact HierarchyInvariantProof.jobWord_carry cfg (words tape) ordinal h2 hL hb

/-- A longer experiment never resamples a previously read family coordinate. -/
theorem IdealHierarchyHorizon : IdealHierarchyHorizon_statement := by
  intro cfg horizon tape
  exact congrFun (HierarchyHorizonFreeProof.jobWord_horizon cfg horizon) (words tape)

/-- The old finite family interface is a view of the canonical experiment. -/
theorem IdealHierarchyFinite : IdealHierarchyFinite_statement := by
  intro cfg N
  exact ⟨by unfold familyTape; fun_prop,
    IdealHierarchyProof.family_uniform cfg N, fun _ _ _ _ => rfl⟩

/-- Routing and dummy words have the required joint law, from one tape. -/
theorem IdealHierarchyOnline : IdealHierarchyOnline_statement := by
  intro cfg N n m
  refine ⟨⟨by unfold familyTape dummyTape; fun_prop,
    IdealHierarchyProof.joint_uniform cfg N n m, fun _ _ _ _ => rfl⟩, ?_⟩
  intro tape slot table hs ht
  simp [dummyOf, dummyTape, dummy, hs, ht]

/-- The engine's finite byte-key routing observations have the canonical law. -/
theorem IdealHierarchySelected : IdealHierarchySelected_statement := by
  intro cfg level ordinal keys
  have h := IdealKeySelectedKeys Unit (fun _ => keys)
    (familyOf cfg level ordinal) ()
  rw [← h, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

/-- Finite section witnesses can depend on the whole outside environment. -/
theorem IdealHierarchyOutside : IdealHierarchyOutside_statement := by
  intro cfg level ordinal
  dsimp only
  intro event hevent bound hsection
  apply IdealKeyOutsideSections (familyBlock (familyOf cfg level ordinal)) event hevent bound
  intro outside
  obtain ⟨keys, localEvent, hmeas, heq, hbound⟩ := hsection outside
  rw [heq, ← Measure.map_apply (by unfold familyRead; fun_prop) hmeas,
    IdealHierarchyProof.familyRead_uniform]
  exact hbound

end RebuildBound
