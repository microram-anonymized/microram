import RebuildBound.Spec.IdealKeyLaw
import RebuildBound.Spec.OnlineBase

/-! The canonical tape feeds exact logical keys directly to the hierarchy.
Finite restrictions are views of this one experiment; their
numeric bounds restrict only the view, never the canonical key domain. -/
namespace RebuildBound.Spec.IdealHierarchy
open Model Model.Hierarchy

/-- The hierarchy reads the canonical family coordinate of each exact key. -/
def words (tape : IdealKey.Tape) : Words :=
  fun level ordinal key =>
    (tape (.inl ((level, ordinal), key))).val

/-- Dummy words occupy a disjoint tagged domain of the same experiment. -/
def dummy (tape : IdealKey.Tape) (slot table : Nat) : Nat :=
  (tape (.inr (slot, table))).val

/-- Optional finite view. `N` restricts this view, not the tape. -/
def familyTape (cfg : Config) (N : Nat) (tape : IdealKey.Tape) : FamilyTape cfg N :=
  fun family key => tape (.inl (family.val, key.val))

/-- Optional finite dummy view of the same tape. -/
def dummyTape (n m : Nat) (tape : IdealKey.Tape) : DummyTape n m :=
  fun slot table => tape (.inr (slot.val, table.val))

/-- All logical keys of one routing family, excluding every dummy coordinate. -/
def familyBlock (family : IdealKey.Family) : Set IdealKey.Coord
  | .inl (other, _) => other = family
  | .inr _ => False

/-- A finite key read from the complete fresh-family restriction. -/
def familyRead (family : IdealKey.Family) (keys : Finset LogicalKey)
    (tape : familyBlock family → Word64) : keys → Word64 :=
  fun key => tape ⟨.inl (family, key.val), rfl⟩

end RebuildBound.Spec.IdealHierarchy

namespace RebuildBound.Spec
open Model Model.Hierarchy IdealHierarchy MeasureTheory
open scoped ENNReal

/-- Byte-key routing is exact and all routing results remain 64-bit words. -/
def IdealHierarchyWords_statement : Prop :=
  (∀ tape level ordinal key, words tape level ordinal key < 2 ^ 64) ∧
  (∀ tape slot table, dummy tape slot table < 2 ^ 64) ∧
  ∀ cfg tape level ordinal (key : LogicalKey),
    jobWord cfg (words tape) level ordinal key =
      (tape (.inl (familyOf cfg level ordinal, key))).val

/-- Completing carries retain the receiving job's family coordinate. -/
def IdealHierarchyCarry_statement : Prop :=
  ∀ cfg tape level ordinal, 2 ≤ level → level ≤ cfg.levels →
    0 < cfg.fanout (level - 1) →
    jobWord cfg (words tape) (level - 1) (ordinal * cfg.fanout (level - 1)) =
      jobWord cfg (words tape) level ordinal

/-- Increasing the horizon changes no routing coordinates or old reads. -/
def IdealHierarchyHorizon_statement : Prop :=
  ∀ cfg horizon tape,
    jobWord { cfg with horizon := horizon } (words tape) = jobWord cfg (words tape)

/-- Every finite view satisfies the finite family-tape interface (`TapePremises`). -/
def IdealHierarchyFinite_statement : Prop :=
  ∀ cfg N, TapePremises cfg N IdealKey.tapeLaw (familyTape cfg N) words

/-- The finite routing and dummy views are jointly uniform. Dummy
projection agrees with the infinite tape on every included slot and table. -/
def IdealHierarchyOnline_statement : Prop :=
  ∀ cfg N n m,
    OnlineTapePremises cfg N n m IdealKey.tapeLaw
      (familyTape cfg N) (dummyTape n m) words ∧
    ∀ tape slot table, slot < n → table < m →
      dummyOf (dummyTape n m tape) slot table = dummy tape slot table

/-- The actual hierarchy's words at any finite set of distinct byte keys have
independent uniform 64-bit values. There is no numeric bound on those keys. -/
def IdealHierarchySelected_statement : Prop :=
  ∀ cfg level ordinal (keys : Finset LogicalKey),
    IdealKey.tapeLaw.map (fun tape (key : keys) =>
      jobWord cfg (words tape) level ordinal key.val) =
    (MeasureTheory.Measure.pi (fun _ : keys => IdealKey.wordLaw)).map
      (fun ws key => (ws key).val)

/-- Outside-dependent key populations can discharge an event bound on the
actual complementary split of the canonical tape. The event's dependence only
on these selected fresh keys is explicit; hierarchy freshness is not assumed
merely because the coordinate has a family label. -/
def IdealHierarchyOutside_statement : Prop :=
  ∀ cfg level ordinal,
    let family := familyOf cfg level ordinal
    let fresh := familyBlock family
    ∀ event : Set ((↥(freshᶜ) → Word64) × (fresh → Word64)),
    MeasurableSet event → ∀ bound : ℝ≥0∞,
    (∀ outside, ∃ (keys : Finset LogicalKey) (localEvent : Set (keys → Word64)),
      MeasurableSet localEvent ∧
      Prod.mk outside ⁻¹' event = familyRead family keys ⁻¹' localEvent ∧
      (MeasureTheory.Measure.pi (fun _ : keys => IdealKey.wordLaw)) localEvent ≤ bound) →
    IdealKey.tapeLaw
      ((fun tape => ((freshᶜ).domRestrict tape, fresh.domRestrict tape)) ⁻¹' event) ≤ bound

end RebuildBound.Spec
