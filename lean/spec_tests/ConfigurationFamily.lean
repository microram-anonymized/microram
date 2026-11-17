import spec_tests.ConfigurationFamilyData
import RebuildBound.Proofs.ConfigurationFamilyProbability
import RebuildBound.Proofs.HierarchySemantics
import RebuildBound.Proofs.HierarchyInvariant31
import RebuildBound.Proofs.OnlineCorrectness
import RebuildBound.Proofs.BatchCorrectness.Endpoint
import RebuildBound.Proofs.SyncSchedule
import RebuildBound.Proofs.HierarchyCovering
import RebuildBound.Proofs.TierFit
import RebuildBound.Proofs.HierarchyChunkAssembly.Jobs
import RebuildBound.Proofs.OnlineFresh
import RebuildBound.Proofs.BatchFresh
import RebuildBound.Proofs.OnlinePattern
import RebuildBound.Proofs.BatchPattern
import RebuildBound.Proofs.OnlineExact
import RebuildBound.Proofs.BatchExact

/-! Finite structural instantiation of all planner-family members, from both
starts. Each finite check feeds the existing shared proof; no numerical
certificate or native refinement is asserted by this module. -/

namespace ConfigurationFamilyTest
open RebuildBound RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Spec
open RebuildBound.HierarchyInvariantProof

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

example : members.length = 94 := by decide +kernel

/-- Lower invariants use identical finite contracts at every geometry. -/
theorem members_low (initialized : Bool) : ∀ m ∈ members,
    let g := m.geometry initialized
    LowFacts g.cfg g.rows g.direct := by
  intro m hm
  exact (HierarchySemanticsProof.lower_iff _).1
    (ConfigurationFamilyStructural initialized m hm).1

theorem members_top (initialized : Bool) : ∀ m ∈ members,
    (m.geometry initialized).TopCompatible := by
  intro m hm
  exact (ConfigurationFamilyStructural initialized m hm).2

theorem members_digit (initialized : Bool) : ∀ m ∈ members,
    (m.geometry initialized).cfg.topDigit = (m.geometry initialized).top.D := by
  cases initialized <;> decide +kernel

/-- Fitting-input first-failure coverage, including two-level direct producers. -/
theorem members_covering (initialized : Bool) : ∀ m ∈ members,
    let g := m.geometry initialized
    HierarchyCoveringProof.FactsFor g.cfg g.rows g.top g.prep g.init g.direct :=
  ConfigurationFamilyProbabilityProof.coveringFacts initialized

/-- Finite-window arithmetic reuses the public probability applicability check. -/
theorem members_chunks (initialized : Bool) : ∀ m ∈ members,
    HierarchyChunkArith.ChunkFacts (m.geometry initialized).cfg :=
  ConfigurationFamilyProbabilityProof.chunkFacts initialized

/-- Small arithmetic facts needed by concrete run and schedule witnesses. -/
theorem members_run_facts (initialized : Bool) : ∀ m ∈ members,
    let g := m.geometry initialized
    1 ≤ g.keyCapacity ∧ 64 * (g.cfg.carry1 / 2) = g.cfg.carryPositions 1 ∧
      1 ≤ g.cfg.horizon ∧ (∀ b ∈ g.cfg.fanouts, 0 < b) ∧ 0 < g.cfg.carryPositions 1 := by
  cases initialized <;> decide +kernel

/-- The existing induction establishes each member's reference invariant. -/
theorem members_invariant (initialized : Bool) (m : Member) (hm : m ∈ members) :
    HierarchyInvariantFor (m.geometry initialized) := by
  intro N tr hN hT hU words
  exact contractsFor _ (members_low initialized m hm)
    (TopFacts.of_compatible (members_top initialized m hm)) hN hT hU words

/-- Scalar lookup uses the shared both-start proof and consistent initial history. -/
theorem members_scalar (initialized : Bool) (m : Member) (hm : m ∈ members)
    (N : Nat) (online : Model.Online.OnlineGeom) (run : Model.Online.OnlineRun)
    (S : Model.Online.Schedule) (n width : Nat)
    (hsetting : OnlineSettingFor (m.geometry initialized) N online run S n width)
    (hInit : (m.geometry initialized).cfg.initialized = false → run.init = [])
    (words : Words) (dummy : Nat → Nat → Nat) (j : Nat) (o : Model.Online.Op)
    (hj : j < n) (ho : run.ops[j]? = some o) (hp : o.probes = true) :
    let g := m.geometry initialized
    let result := Model.Probe.scalar g.cfg g.shapes online run S words dummy j
    Model.Probe.decode result.found =
        Model.Probe.latestValue o.record.key (run.init ++ (run.ops.take j).map Model.Online.Op.record) ∧
      ∀ i, result.addresses.getD i 0 = Model.Online.touched g.cfg g.shapes online run S words dummy j i :=
  OnlineCorrectnessProof.correctnessFor_run _ (members_low initialized m hm)
    (TopFacts.of_compatible (members_top initialized m hm)) (members_digit initialized m hm)
    N online run S n width hsetting hInit words dummy j o hj ho hp

/-- Batch lookup uses the same contract, including earlier lanes in a chunk. -/
theorem members_batch (initialized : Bool) (m : Member) (hm : m ∈ members)
    (N : Nat) (online : Model.Online.OnlineGeom) (run : Model.OnlineBatch.BatchRun)
    (S : Model.Online.Schedule) (n width : Nat)
    (hsetting : BatchSettingFor (m.geometry initialized) N online run S n width)
    (hInit : (m.geometry initialized).cfg.initialized = false → run.init = [])
    (words : Words) (dummy : Nat → Nat → Nat) (t : Nat) (slot : Model.OnlineBatch.Slot)
    (ht : t < n) (hs : (Model.OnlineBatch.slots run)[t]? = some slot) (hp : slot.probes = true) :
    let g := m.geometry initialized
    let result := Model.Probe.batch g.cfg g.shapes online run S words dummy t
    Model.Probe.decode result.found = Model.Probe.latestValue slot.record.key
        (run.init ++ ((Model.OnlineBatch.slots run).take t).map Model.OnlineBatch.Slot.record) ∧
      ∀ i, result.addresses.getD i 0 = Model.OnlineBatch.touched g.cfg g.shapes online run S words dummy t i :=
  BatchCorrectnessProof.correctnessFor_run _ (members_low initialized m hm)
    (TopFacts.of_compatible (members_top initialized m hm)) (members_digit initialized m hm)
    N online run S n width hsetting hInit words dummy t slot ht hs hp

theorem members_fresh (initialized : Bool) (m : Member) (hm : m ∈ members) :
    OnlineFreshFor (m.geometry initialized) ∧ BatchFreshFor (m.geometry initialized) :=
  ⟨OnlineFreshProof.freshFor _ (members_low initialized m hm),
    BatchFreshProof.freshFor _ (members_low initialized m hm)⟩

theorem members_exact (initialized : Bool) (m : Member) (hm : m ∈ members) :
    OnlineExactFor (m.geometry initialized) ∧ BatchExactFor (m.geometry initialized) := by
  have F := members_low initialized m hm
  exact ⟨OnlineExactProof.exactFor_of _ (OnlinePatternProof.patternFor _ F) (OnlineFreshProof.freshFor _ F),
    BatchExactProof.exactFor_of _ (BatchPatternProof.patternFor _ F) (BatchFreshProof.freshFor _ F)⟩

theorem members_first_failure (initialized : Bool) (m : Member) (hm : m ∈ members)
    (tr : Trace) (words : Words) :
    let g := m.geometry initialized
    Fails g.cfg g.shapes tr words → ∃ j ∈ g.cfg.potentialJobs, WithinHorizon g.cfg j ∧
      jobTiersFit g.cfg g.shapes tr words j ∧ jobFails g.cfg g.shapes tr words j = true :=
  HierarchyCoveringProof.firstFailureFor _ (members_covering initialized m hm)
    SepTierFit TopTierFit TPTierFit tr words

theorem members_schedule (initialized : Bool) (m : Member) (hm : m ∈ members) (n : Nat) :
    let cfg := (m.geometry initialized).cfg
    SchedulePremises cfg (Model.Online.syncSchedule cfg) n cfg.levels := by
  have hf := members_run_facts initialized m hm
  exact SyncScheduleLemmas.syncSchedule_premises _ hf.2.2.2.1 hf.2.2.2.2 n

open Model.Online

def oneRead : Op := .probe ⟨LogicalKey.ofNat (0), 9, false⟩
def oneReadRun : OnlineRun := ⟨[oneRead], [], fun _ => false⟩
def onlineFor (g : HierarchyGeometry) : OnlineGeom := ⟨64, g.cfg.carry1 / 2⟩

/-- A nonempty run meets the full scalar premises, for every member and start. -/
theorem members_setting (initialized : Bool) (m : Member) (hm : m ∈ members) :
    let g := m.geometry initialized
    OnlineSettingFor g 1 (onlineFor g) oneReadRun (syncSchedule g.cfg) 1 g.cfg.levels := by
  obtain ⟨hN, hgeom, hh, hF, hP⟩ := members_run_facts initialized m hm
  have frozen : (stateAt (onlineFor (m.geometry initialized)) oneReadRun oneReadRun.ops.length).frozen = [] := by
    change (stateAt (⟨64, 2⟩ : OnlineGeom) oneReadRun 1).frozen = []
    decide +kernel
  refine ⟨hN, by decide +kernel, ?_, members_schedule initialized m hm 1⟩
  refine ⟨⟨hgeom, show 0 < 64 by decide +kernel⟩, hh, ?_, ?_, ?_⟩
  · intro o ho
    simp only [oneReadRun, List.mem_singleton] at ho
    subst o
    decide +kernel
  · exact { nodup := by intro i u hu; simp [traceOf, frozen] at hu
            load := by intro i; simp [traceOf, frozen, DirectMasks.records]
            keys := by intro i x hx; simp [traceOf, frozen, DirectMasks.records] at hx
            initNodup := by simp [traceOf, oneReadRun]
            initKeys := by simp [traceOf, oneReadRun] }
  · intro words o _ r _ h
    simp [earlyDrop, traceOf, oneReadRun] at h

/-- The first read returns absence for arbitrary routing and dummy tapes. -/
theorem members_read_absent (initialized : Bool) (m : Member) (hm : m ∈ members)
    (words : Words) (dummy : Nat → Nat → Nat) :
    let g := m.geometry initialized
    Probe.decode (Probe.scalar g.cfg g.shapes (onlineFor g) oneReadRun
      (syncSchedule g.cfg) words dummy 0).found = none := by
  have h := (members_scalar initialized m hm 1 (onlineFor (m.geometry initialized))
    oneReadRun (syncSchedule (m.geometry initialized).cfg) 1 (m.geometry initialized).cfg.levels
    (members_setting initialized m hm) (fun _ => rfl) words dummy 0 oneRead
    (by decide +kernel) rfl rfl).1
  simpa [oneReadRun, Probe.latestValue, DirectPrefix.latest, Probe.decode] using h

end ConfigurationFamilyTest
