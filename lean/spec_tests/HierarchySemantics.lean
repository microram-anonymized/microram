import RebuildBound.Proofs.HierarchyApi
import spec_tests.ConfigurationFamily
import spec_tests.AdaptiveSemantics
import spec_tests.EmptyStart

/-! Public semantic interface regression: every manifest member, both starts,
an outside-family geometry, malformed structural contracts, and the required
empty-history premise. These checks do not extend the numerical claim. -/

namespace HierarchySemanticsTest
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open ConfigurationFamilyTest

/-- Existing finite checks feed the public contract without new enumeration. -/
theorem members_structural (initialized : Bool) (m : Member) (hm : m ∈ members) :
    (m.geometry initialized).Structural :=
  ConfigurationFamilyStructural initialized m hm

/-- All five public exports instantiate at every member, including empty starts. -/
example (initialized : Bool) (m : Member) (hm : m ∈ members) :
    let g := m.geometry initialized
    (OnlineLookupFor g ∧ BatchLookupFor g) ∧
    (UniverseOnlineLookupFor g ∧ UniverseBatchLookupFor g) ∧
    (OnlinePatternFor g ∧ OnlineFreshFor g ∧ OnlineExactFor g ∧ OnlineFailureFor g) ∧
    (BatchPatternFor g ∧ BatchFreshFor g ∧ BatchExactFor g ∧ BatchFailureFor g) ∧
    (UniverseOnlineExactFor g ∧ UniverseOnlineFailureFor g ∧
      UniverseBatchExactFor g ∧ UniverseBatchFailureFor g) ∧
    (AdaptiveExactFor g ∧ AdaptiveFailureFor g) := by
  have h := members_structural initialized m hm
  exact ⟨HierarchyLookup _ h, HierarchyUniverseLookup _ h,
    (HierarchyFixedSemantics _ h).1, (HierarchyFixedSemantics _ h).2,
    HierarchyUniverseSemantics _ h, HierarchyAdaptiveSemantics _ h⟩

/-- The API/flag exports use the same family checks, from both starts. -/
example (initialized : Bool) (m : Member) (hm : m ∈ members) :
    let g := m.geometry initialized
    BatchFoundFor g ∧ FlagSoundnessFor g ∧ BatchApiCorrectnessFor g ∧
      ApiAdmissibleFor g ∧ AdaptiveFlagAdmissibleFor g ∧ AdaptiveApiCorrectnessFor g := by
  have h := members_structural initialized m hm
  exact ⟨HierarchyBatchFound _ h, HierarchyFlagSoundness _ h,
    HierarchyBatchApiCorrectness _ h, HierarchyApiAdmissible _ h,
    HierarchyAdaptiveFlagAdmissible _ h, HierarchyAdaptiveApiCorrectness _ h⟩

/-- The public lookup is exercised by the existing nonempty run witness. -/
example (initialized : Bool) (m : Member) (hm : m ∈ members)
    (words : Words) (dummy : Nat → Nat → Nat) :
    let g := m.geometry initialized
    Probe.decode (Probe.scalar g.cfg g.shapes (onlineFor g) oneReadRun
      (Online.syncSchedule g.cfg) words dummy 0).found = none := by
  have h := ((HierarchyLookup _ (members_structural initialized m hm)).1
    1 (onlineFor (m.geometry initialized)) oneReadRun
    (Online.syncSchedule (m.geometry initialized).cfg) 1 (m.geometry initialized).cfg.levels
    (members_setting initialized m hm) (fun _ => rfl) words dummy 0 oneRead (by decide) rfl rfl).1
  simpa [oneReadRun, Probe.latestValue, DirectPrefix.latest, Probe.decode] using h

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Rejected mutations exercise actual shapes, not just Config.Valid. -/
example : ¬ ({ AdaptiveSemanticsTest.geometry true with
    direct := fun d => { AdaptiveSemanticsTest.direct d with digit := d + 1 } }).Structural := by decide
example : ¬ ({ AdaptiveSemanticsTest.geometry true with
    direct := fun d => { AdaptiveSemanticsTest.direct d with K := 3 } }).Structural := by decide
example : ¬ ({ AdaptiveSemanticsTest.geometry true with
    keyCapacity := 1025 }).Structural := by decide
example : ¬ ({ AdaptiveSemanticsTest.geometry true with
    prep := { (AdaptiveSemanticsTest.geometry true).prep with drainPages := 2 } }).Structural := by decide
example : ¬ ({ AdaptiveSemanticsTest.geometry true with
    init := { (AdaptiveSemanticsTest.geometry true).init with drainPages := 2 } }).Structural := by decide
example : ¬ ({ HierarchyGeometryTest.deep8 with rows := [] }).Structural := by decide
example : ¬ ({ HierarchyGeometryTest.deep8 with rows :=
    (HierarchyGeometryTest.deep8.rows.map fun (p : SepGeom × Nat) => ({ p.1 with bTierPages := 0 }, p.2)) }).Structural := by decide
example : ¬ ({ AdaptiveSemanticsTest.geometry true with
    top := { (AdaptiveSemanticsTest.geometry true).top with bPages := 0 } }).Structural := by decide

/-- A direct producer can be valid on its own yet overfill the top's input tier. -/
def wideDirect (d : Nat) : DirectJob.Geometry :=
  { AdaptiveSemanticsTest.direct d with
    outputCapacity := 128
    insertionCapacity := 128
    copyCapacity := 128 }
example : HierarchyGeometry.DirectCompatible (AdaptiveSemanticsTest.geometry true).cfg wideDirect := by decide
example : ¬ ({ AdaptiveSemanticsTest.geometry true with direct := wideDirect }).Structural := by decide

/-- A valid empty geometry does not license ignoring supplied history.
`OnlineCorrectnessFor` is false here; the empty-start premise
(`initialized = false → run.init = []`) rejects this exact run. -/
example : EmptyStartMismatch.geo.Structural ∧ ¬ OnlineCorrectnessFor EmptyStartMismatch.geo ∧
    ¬ (EmptyStartMismatch.geo.cfg.initialized = false → EmptyStartMismatch.run.init = []) :=
  ⟨⟨(HierarchySemanticsProof.lower_iff _).2 EmptyStartMismatch.valid.1,
      EmptyStartMismatch.valid.2⟩, EmptyStartMismatch.insufficient, by decide⟩

end HierarchySemanticsTest
