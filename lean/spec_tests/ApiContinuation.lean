import RebuildBound.Proofs.ApiContinuation
import spec_tests.ApiStructural

/-! Physical completion witnesses. The independent logical map, exact physical
prefix and arbitrary-tape observations are checked separately. -/
namespace ApiContinuationTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Model.PublicApi
open RebuildBound.Model.ApiContinuation
open ApiTests (codec)
open ApiStructuralTests (geo online missGroups miss_requests miss_valid miss_fit)

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Two misses leave a partial unit; padding really freezes it, at capacity zero
in both start modes, without any finite key-domain assumption. -/
theorem misses_complete (initialized : Bool) (a b : LogicalKey) :
    let groups := complete online.unitEntries 1 (missGroups [a, b])
    let run := ApiExecution.run codec (geo initialized).cfg (geo initialized).shapes online
      (syncSchedule (geo initialized).cfg) [] groups
    ApiRunCorrect (geo initialized) codec online run (syncSchedule (geo initialized).cfg)
      (groups.flatMap Group.lanes) ∧
    ApiTopPopulations (geo initialized) online run ∧
    CompletedApiSnapshot codec online run [⟨a, .read⟩, ⟨b, .read⟩] 1 := by
  have h := ApiIdleLive (geo initialized) (ApiStructuralTests.structural initialized)
    codec online (syncSchedule (geo initialized).cfg) [] (missGroups [a, b]) 2 1
    (by simp [ApiCapacity.InitialStateValid]) rfl (by decide +kernel)
    (by change 2 ≤ 64; decide +kernel) (by change 64 ≤ 2 ^ 32; decide +kernel)
    (miss_valid _) (miss_fit _ 0)
    (SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _)
    (by rw [miss_requests]; exact ApiMissCapacity [a, b])
  exact h

def eraseGroups : List (PublicApi.Group Api.Request) := [.chunk [⟨LogicalKey.ofNat (2 ^ 130), .erase⟩]]
def initial : List Rec := [ApiTests.live (2 ^ 130) 19]
def eraseRun (extra : Nat) : OnlineBatch.BatchRun :=
  ApiExecution.run codec (geo true).cfg (geo true).shapes online
    (syncSchedule (geo true).cfg) initial (extend eraseGroups extra)

theorem erase_complete : CompletedApiSnapshot codec online (eraseRun 63)
    [⟨LogicalKey.ofNat (2 ^ 130), .erase⟩] 1 := by
  exact (ApiIdleComplete (geo true) (ApiStructuralTests.structural true) codec online
    (syncSchedule (geo true).cfg) initial eraseGroups 2 1
    (by simp [geo, AdaptiveSemanticsTest.geometry]) (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro group hg; simp only [eraseGroups, List.mem_singleton] at hg; subst group
        simp [ApiExecution.Valid, Api.Request.probes])
    (by change 0 < 1 ∧ 1 ≤ 64 ∧ True; decide +kernel)
    (SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _)).2

example : (OnlineBatch.stateAt online (eraseRun 63) (eraseRun 63).ops.length).current = [] ∧
    (OnlineBatch.stateAt online (eraseRun 63) (eraseRun 63).ops.length).frozen.length = 1 :=
  ⟨erase_complete.1, erase_complete.2.1⟩

/-- Even a trace cut containing an incomplete group of frozen units now sees
the erase, rather than resurrecting the initialized value. -/
example (n : Nat) (hn : 0 < n) :
    Api.stateOf codec ((eraseRun 63).init ++ (List.range n).flatMap
      (fun i => DirectMasks.records ((OnlineBatch.traceOf online (eraseRun 63)).units i)))
      (LogicalKey.ofNat (2 ^ 130)) = none := by
  have h := erase_complete.2.2 n (by change 1 ≤ n * 2; omega)
  rw [h]
  simp [Api.stateAt, Api.step, Api.nextValue]

/-- The original erase still selects the same complete record and touches the
same buckets, on arbitrary real and dummy tapes. -/
example (words : Words) (dummy : Nat → Nat → Nat) :
    (Probe.batch (geo true).cfg (geo true).shapes online (eraseRun 0)
      (syncSchedule (geo true).cfg) words dummy 0).found =
      (Probe.batch (geo true).cfg (geo true).shapes online (eraseRun 63)
        (syncSchedule (geo true).cfg) words dummy 0).found ∧
    ∀ i, OnlineBatch.touched (geo true).cfg (geo true).shapes online (eraseRun 0)
      (syncSchedule (geo true).cfg) words dummy 0 i =
      OnlineBatch.touched (geo true).cfg (geo true).shapes online (eraseRun 63)
        (syncSchedule (geo true).cfg) words dummy 0 i := by
  have h := ApiIdleObservations codec (geo true).cfg (geo true).shapes online
    (syncSchedule (geo true).cfg) initial eraseGroups 63 2 rfl (by decide +kernel)
    (SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _) words dummy 0
    (by rw [ApiContinuationProof.run_length]; decide +kernel)
  simpa only [eraseRun, extend, idleGroups, List.replicate_zero, List.append_nil] using h

/-- Appending never repartitions the original mixed batch or its duplicates. -/
example (c : Api.Codec) cfg sh g S init :
    let groups : List (PublicApi.Group Api.Request) :=
      [.chunk [⟨LogicalKey.ofNat (7), .erase⟩, ⟨LogicalKey.ofNat (7), .read⟩], .blind ⟨LogicalKey.ofNat (9), .blindWrite 0⟩]
    let before := ApiExecution.run c cfg sh g S init groups
    (ApiExecution.run c cfg sh g S init (extend groups 100)).ops.take before.ops.length =
      before.ops :=
  (ApiIdlePrefix c cfg sh g S init _ 100).1

/-- A target before the supplied requests cannot satisfy the endpoint premise;
the total helper never truncates the original input. -/
example : ¬ (eraseGroups.flatMap Group.lanes).length ≤ 0 * online.unitEntries := by decide +kernel
example : complete online.unitEntries 0 eraseGroups = eraseGroups := by decide +kernel

/-- Idle key zero need not be fresh: padding from a live zero key preserves
that value and still derives all modeled top populations at capacity one. -/
example :
    let geometry := ApiStructuralTests.initialOnlyGeo
    let init := [ApiTests.live 0 19]
    let groups := complete online.unitEntries 1 []
    let run := ApiExecution.run codec geometry.cfg geometry.shapes online
      (syncSchedule geometry.cfg) init groups
    ApiTopPopulations geometry online run ∧ CompletedApiSnapshot codec online run [] 1 := by
  let geometry := ApiStructuralTests.initialOnlyGeo
  have hi : ApiCapacity.InitialStateValid geometry.keyCapacity geometry.cfg.initialized
      [ApiTests.live 0 19] := by
    change ApiCapacity.InitialStateValid 1 true [ApiTests.live 0 19]
    simp [ApiCapacity.InitialStateValid, ApiTests.live]
  have h := ApiIdleLive geometry (by decide +kernel) codec online (syncSchedule geometry.cfg)
    [ApiTests.live 0 19] [] 2 1 hi rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by simp) trivial
    (SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _)
    (ApiInitialCapacity _ _ _ hi codec).2
  exact h.2

end ApiContinuationTests
