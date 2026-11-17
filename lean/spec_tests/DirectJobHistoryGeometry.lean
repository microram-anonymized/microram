import RebuildBound.Spec.ConfigurationFamilyDirect
import RebuildBound.Proofs.DirectJobHistoryGeometry
import RebuildBound.Proofs.DirectJobPopulation
import spec_tests.ConfigurationFamilyData

/-! Shared direct-history input laws at every family carry width. These tests
check source applicability, not cycle probabilities or numerical certificates. -/

namespace DirectJobHistoryGeometryTest
open RebuildBound RebuildBound.Model RebuildBound.Model.DirectJob RebuildBound.Spec
open ConfigurationFamilyTest
open scoped ENNReal NNReal

/-- Tests reuse the public direct probability-shape constructor. -/
abbrev sep := RebuildBound.Spec.ConfigurationFamily.Member.directSep

/-- Every later ordinal uses its actual predecessor and exact word widths. -/
theorem familyGeometry : ∀ m ∈ members,
    ∀ d ∈ List.range' 2 ((m.config true).fanout 1 - 1),
      ReferenceInputCompatible (m.direct (d - 1)) (sep m d) ∧
      2 ≤ (sep m d).d ∧ (sep m d).k < 64 ∧
      (sep m d).K + val2 ((sep m d).d - 1) ≤ 64 := by
  decide +kernel

/-- The 512-record selected load is only one of the three family loads. -/
theorem familyLoads : ∀ m ∈ members,
    (m.config true).load * (m.config true).carry1 = 64 * m.r0 ∧
    64 * m.r0 ∈ [128, 256, 512] := by
  decide +kernel

theorem familyLaw (m : Member) (hm : m ∈ members) (d : Nat)
    (hd : d ∈ List.range' 2 ((m.config true).fanout 1 - 1))
    (data : DirectHistoryData) (hv : data.ValidFor (sep m d) 32) :
    SInputLaw (data.lawFor (m.direct (d - 1)) (sep m d)) 32
      ((sep m d).oldDensity 64 data.KA.card) ∧
    DirectJobInputMatch (data.lawFor (m.direct (d - 1)) (sep m d))
      (data.directFor (m.direct (d - 1))) := by
  obtain ⟨hg, hdigit, hk, hp⟩ := familyGeometry m hm d hd
  exact ⟨DirectJobHistoryInputLawFor _ _ hg hdigit hk hp 32 data hv,
    DirectJobHistoryInputMatchFor _ _ 32 data hv⟩

def small : Member := ⟨"L2_r2_D8_2", 2, [2], [1, 1], [1, 1]⟩
def prior : Geometry := small.direct 1
def current : SepGeom := sep small 2

theorem directPool : (small.direct 2).ranges = .direct ∧
    0 < (small.direct 2).poolCapacity ∧ current.U = 4 ∧
    32 * current.U = 128 ∧ current.I = 3 ∧ current.K = 2 := by decide +kernel

/-- A singleton old population and a fresh duplicate/tombstone plus a new key
supply a nonempty source-law witness without assuming successful production. -/
def history : DirectHistoryData where
  KA := {LogicalKey.ofNat 7}
  KB := {LogicalKey.ofNat 7, LogicalKey.ofNat 11}
  Base := Unit
  weight _ := 1
  before _ := ⟨[], []⟩
  olderWord _ _ := 0
  chronology _ := []
  priorUnits _ _ := [[some ⟨LogicalKey.ofNat (7), 70, false⟩]]
  freshUnits _ _ := [[some ⟨LogicalKey.ofNat (7), 0, true⟩, some ⟨LogicalKey.ofNat (11), 110, false⟩]]

theorem historyValid : history.ValidFor current 32 := by
  apply DirectJobHistoryPrefixValidFor history current 32 (fun _ => [])
    (fun _ _ => 0) [] {LogicalKey.ofNat 7}
  · change ∑ _ : Unit, (1 : ℝ≥0∞) = 1
    simp
  · intro base
    exact ⟨rfl, rfl⟩
  · intro base
    exact List.Forall₂.nil
  · intro keys hk
    simp only [List.mem_singleton] at hk
    subst keys
    decide +kernel
  · intro base word
    change ([LogicalKey.ofNat 7] : List LogicalKey).toFinset = {LogicalKey.ofNat 7}
    decide +kernel
  · simp [history, directPopulationUnion]
  · decide +kernel
  · intro hist word
    change ([LogicalKey.ofNat 7, LogicalKey.ofNat 11] : List LogicalKey).toFinset = {LogicalKey.ofNat 7, LogicalKey.ofNat 11}
    decide +kernel
  · decide +kernel
/-- A source fitting the old 512 bound can exceed this actual 128 capacity. -/
theorem rejectsSelectedLoad (data : DirectHistoryData) (hcard : data.KB.card = 129) :
    ¬ data.ValidFor current 32 := by
  intro hv
  have hload := hv.bLoad
  change data.KB.card ≤ 128 at hload
  omega

theorem nonemptyLaw :
    SInputLaw (history.lawFor prior current) 32 (current.oldDensity 64 history.KA.card) ∧
    DirectJobInputMatch (history.lawFor prior current) (history.directFor prior) :=
  ⟨DirectJobHistoryInputLawFor prior current (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) 32 history historyValid,
   DirectJobHistoryInputMatchFor prior current 32 history historyValid⟩

/-- Substituting the old selected producer breaks this actual four-home input. -/
theorem rejectsSelected : ¬ ReferenceInputCompatible (selectedDirectGeometry 1) current := by
  decide +kernel
theorem rejectsHomes : ¬ ReferenceInputCompatible { prior with outputHomes := 8 } current := by
  decide +kernel
theorem rejectsK : ¬ ReferenceInputCompatible { prior with K := 3 } current := by decide +kernel

theorem rejectsDigit : ¬ ReferenceInputCompatible { prior with digit := 2 } current := by decide +kernel

theorem rejectsLanes : ¬ ReferenceInputCompatible prior { current with C := 32 } := by decide +kernel

theorem rejectsBPages : ¬ ReferenceInputCompatible prior { current with bTierPages := 2 } := by
  decide +kernel
end DirectJobHistoryGeometryTest
