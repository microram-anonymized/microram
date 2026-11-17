import RebuildBound.Spec.KeyUniverse

/-! Pattern and freshness interfaces for one fixed key universe at arbitrary geometry. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.OnlineBatch

def UniverseOnlinePatternFor (geo : HierarchyGeometry) : Prop :=
  ∀ (U : Finset LogicalKey) g run S n m, UniverseOnlineSetting geo U g run S n m →
    ∀ (words words' : Words) j i, j < n → i < (S j).tables.length →
      Model.Online.isReal geo.cfg geo.shapes g run S words j i =
        Model.Online.isReal geo.cfg geo.shapes g run S words' j i

def UniverseOnlineFreshFor (geo : HierarchyGeometry) : Prop :=
  ∀ (U : Finset LogicalKey) g run S n m, UniverseOnlineSetting geo U g run S n m → ∀ (words : Words),
    (∀ j i, j < n → i < (S j).tables.length →
      Model.Online.isReal geo.cfg geo.shapes g run S words j i = true →
      ∃ c o, (S j).tables[i]? = some c ∧ run.ops[j]? = some o ∧
        familyOf geo.cfg c.1 c.2 ∈ geo.cfg.coordinates ∧ o.record.key ∈ U) ∧
    ∀ j i j' i' c c' o o', j < n → i < m → j' < n → i' < m → (j, i) ≠ (j', i') →
      Model.Online.isReal geo.cfg geo.shapes g run S words j i = true →
      Model.Online.isReal geo.cfg geo.shapes g run S words j' i' = true →
      (S j).tables[i]? = some c → (S j').tables[i']? = some c' →
      run.ops[j]? = some o → run.ops[j']? = some o' →
      (familyOf geo.cfg c.1 c.2, o.record.key) ≠ (familyOf geo.cfg c'.1 c'.2, o'.record.key)

def UniverseBatchPatternFor (geo : HierarchyGeometry) : Prop :=
  ∀ (U : Finset LogicalKey) g run S n m, UniverseBatchSetting geo U g run S n m →
    ∀ (words words' : Words) t i, t < n → i < (slotSchedule (widths run) S t).tables.length →
      Model.OnlineBatch.isReal geo.cfg geo.shapes g run S words t i =
        Model.OnlineBatch.isReal geo.cfg geo.shapes g run S words' t i

def UniverseBatchFreshFor (geo : HierarchyGeometry) : Prop :=
  ∀ (U : Finset LogicalKey) g run S n m, UniverseBatchSetting geo U g run S n m → ∀ (words : Words),
    (∀ t i, t < n → i < (slotSchedule (widths run) S t).tables.length →
      Model.OnlineBatch.isReal geo.cfg geo.shapes g run S words t i = true →
      ∃ c s, (slotSchedule (widths run) S t).tables[i]? = some c ∧ (slots run)[t]? = some s ∧
        familyOf geo.cfg c.1 c.2 ∈ geo.cfg.coordinates ∧ s.record.key ∈ U) ∧
    ∀ t i t' i' c c' s s', t < n → i < m → t' < n → i' < m → (t, i) ≠ (t', i') →
      Model.OnlineBatch.isReal geo.cfg geo.shapes g run S words t i = true →
      Model.OnlineBatch.isReal geo.cfg geo.shapes g run S words t' i' = true →
      (slotSchedule (widths run) S t).tables[i]? = some c →
      (slotSchedule (widths run) S t').tables[i']? = some c' →
      (slots run)[t]? = some s → (slots run)[t']? = some s' →
      (familyOf geo.cfg c.1 c.2, s.record.key) ≠ (familyOf geo.cfg c'.1 c'.2, s'.record.key)

end RebuildBound.Spec
