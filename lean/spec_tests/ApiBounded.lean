import RebuildBound.Proofs.ApiBounded
import RebuildBound.Proofs.IdealBounded
import spec_tests.IdealProbe
import spec_tests.IdealCapacity

/-! Bounded API transfer regressions: actual requests/slots cannot disappear,
wrong replies are rejected, failure permits arbitrary adapter behavior, and the
canonical numerical endpoints accept adaptive keys and unbounded seed support. -/
namespace ApiBoundedTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Model.PublicApi
open MeasureTheory IdealHierarchy
open ApiTests (codec)
open ApiStructuralTests (geo online)

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The generic transfer applies to this zero-capacity structural geometry,
even though its actual first request inserts a live key. No capacity estimate
is claimed; the inequality charges the actual reference failure event. -/
theorem transfer_without_live_capacity (initialized : Bool)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (w : Ω → Words) (d : Ω → Nat → Nat → Nat)
    (runs : Ω → OnlineBatch.BatchRun) (requests : Ω → List Api.Request)
    (actual : Ω → Nat → Probe.Result)
    (hagree : ∀ ω, ApiBoundedAgreement (geo initialized) codec online
      (syncSchedule (geo initialized).cfg) 2 64 IdealProbeTests.batches []
      (IdealProbeTests.choose initialized) (w ω) (d ω) (runs ω) (requests ω) (actual ω)) :
    μ {ω | ¬ ApiResultsCorrect (geo initialized) codec online (runs ω)
      (syncSchedule (geo initialized).cfg) 2 (w ω) (d ω) (requests ω) (actual ω)} ≤
    μ {ω | Fails (geo initialized).cfg (geo initialized).shapes
      (OnlineBatch.traceOf online (Adaptive.realized (geo initialized).cfg
        (geo initialized).shapes online (syncSchedule (geo initialized).cfg)
        (IdealProbeTests.run initialized) (w ω) (d ω))) (w ω)} := by
  exact (ApiBoundedTransfer (geo initialized) (ApiStructuralTests.structural initialized)
    codec online (syncSchedule (geo initialized).cfg) [] 2 64 IdealProbeTests.batches
    (IdealProbeTests.choose initialized) (fun _ => rfl) (by simp) (by simp) rfl
    (by decide +kernel) (by change 2 ≤ 2 ^ 32; decide +kernel)
    (SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ b ∈ ([2] : List Nat), 0 < b; decide +kernel)
      (by change 0 < 128; decide +kernel) _)
    μ w d runs requests actual hagree).2

example : ¬ ApiCapacity.LiveCapacity (geo true).keyCapacity (Api.stateOf codec []) []
    [⟨[], .write 7⟩, ⟨List.replicate 65 0, .write 7⟩] := by
  intro h
  have hp := h.2 1 (by decide +kernel)
  change 1 ≤ 0 at hp
  omega

def emptyRun : OnlineBatch.BatchRun := ⟨[], [], fun _ => false⟩
def absent : Nat → Probe.Result := fun _ => ⟨none, []⟩

/-- A jointly truncated request/run pair fails its advertised public length;
it cannot make the answer quantifier vacuous. -/
example : ¬ ApiResultsCorrect (geo false) codec online emptyRun
    (syncSchedule (geo false).cfg) 1 (fun _ _ _ => 0) (fun _ _ => 0) [] absent := by
  intro h
  have hlen := h.1
  change 0 = 1 at hlen
  omega

/-- Keeping the request but omitting its slot also fails correctness. -/
example : ¬ ApiResultsCorrect (geo false) codec online emptyRun
    (syncSchedule (geo false).cfg) 1 (fun _ _ _ => 0) (fun _ _ => 0)
    [⟨[], .read⟩] absent := by
  intro h
  have hlen := h.2.1
  change 1 = 0 at hlen
  omega

/-- A present initialized value cannot be replaced by an absent adapter reply.
Both the request and physical run are otherwise the real constructed ones. -/
example (w : Words) (d : Nat → Nat → Nat) :
    ¬ ApiResultsCorrect (geo true) codec online (ApiStructuralTests.initialRun true)
      (syncSchedule (geo true).cfg) 1 w d [⟨LogicalKey.ofNat (2 ^ 130), .read⟩] absent := by
  intro h
  have ht : 0 < (OnlineBatch.slots (ApiStructuralTests.initialRun true)).length := by
    rw [← h.2.1]
    decide +kernel
  let s := (OnlineBatch.slots (ApiStructuralTests.initialRun true))[0]
  have hs : (OnlineBatch.slots (ApiStructuralTests.initialRun true))[0]? = some s :=
    List.getElem?_eq_getElem ht
  have hr := (h.2.2.2 0 ⟨LogicalKey.ofNat (2 ^ 130), .read⟩ s rfl hs).1
  have hg := (((ApiStructuralTests.initialized_read_correct true).2.2 w d).2.2
    0 ⟨LogicalKey.ofNat (2 ^ 130), .read⟩ s rfl hs).1
  have he := hr.trans hg.symm
  change none = Api.value codec (Probe.batch (geo true).cfg (geo true).shapes online
    (ApiStructuralTests.initialRun true) (syncSchedule (geo true).cfg) w d 0).found at he
  rw [ApiStructuralTests.initialized_read_value] at he
  contradiction

/-- The reference result is accepted, including its actual address count. -/
example (w : Words) (d : Nat → Nat → Nat) :
    ApiResultsCorrect (geo true) codec online (ApiStructuralTests.initialRun true)
      (syncSchedule (geo true).cfg) 1 w d [⟨LogicalKey.ofNat (2 ^ 130), .read⟩]
      (Probe.batch (geo true).cfg (geo true).shapes online (ApiStructuralTests.initialRun true)
        (syncSchedule (geo true).cfg) w d) :=
  ApiBoundedProof.results _ _ _ _ _ _ _ _ _ _ rfl
    (ApiStructuralTests.initialized_read_correct true) (fun _ _ => rfl)

/-- This initialized request probes exactly one table. Correct selected records
cannot compensate for omitted or extra addresses, even when every address is zero. -/
theorem wrong_address_count (w : Words) (d : Nat → Nat → Nat)
    (addresses : List Nat) (hlen : addresses.length ≠ 1) :
    ¬ ApiResultsCorrect (geo true) codec online (ApiStructuralTests.initialRun true)
      (syncSchedule (geo true).cfg) 1 w d [⟨LogicalKey.ofNat (2 ^ 130), .read⟩]
      (fun t => { Probe.batch (geo true).cfg (geo true).shapes online
        (ApiStructuralTests.initialRun true) (syncSchedule (geo true).cfg) w d t with
          addresses := addresses }) := by
  intro h
  have ht : 0 < (OnlineBatch.slots (ApiStructuralTests.initialRun true)).length := by
    rw [← h.2.1]
    decide +kernel
  let s := (OnlineBatch.slots (ApiStructuralTests.initialRun true))[0]
  have hs : (OnlineBatch.slots (ApiStructuralTests.initialRun true))[0]? = some s :=
    List.getElem?_eq_getElem ht
  have ha := (h.2.2.2 0 ⟨LogicalKey.ofNat (2 ^ 130), .read⟩ s rfl hs).2.2.1
  exact hlen ha

/-- Zero-padded observations alone cannot distinguish these malformed lists
from the single scheduled zero address; the result contract rejects both. -/
example (i : Nat) : ([] : List Nat).getD i 0 = [0].getD i 0 ∧
    [0, 0].getD i 0 = [0].getD i 0 := by
  cases i with
  | zero => decide +kernel
  | succ i => cases i <;> simp

example : ∀ addresses ∈ [[], [0, 0]],
    ¬ ApiResultsCorrect (geo true) codec online (ApiStructuralTests.initialRun true)
      (syncSchedule (geo true).cfg) 1 (fun _ _ _ => 0) (fun _ _ => 0)
      [⟨LogicalKey.ofNat (2 ^ 130), .read⟩]
      (fun t => { Probe.batch (geo true).cfg (geo true).shapes online
        (ApiStructuralTests.initialRun true) (syncSchedule (geo true).cfg)
        (fun _ _ _ => 0) (fun _ _ => 0) t with addresses := addresses }) := by
  intro addresses hmem
  apply wrong_address_count
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;> decide +kernel

/-- A blind write has no scheduled addresses, including zero addresses. -/
example (w : Words) (d : Nat → Nat → Nat) :
    ¬ ApiResultsCorrect (geo false) codec online
      ⟨[.blind (ApiTests.live 0 7)], [], fun _ => false⟩
      (syncSchedule (geo false).cfg) 1 w d [⟨LogicalKey.ofNat 0, .blindWrite 7⟩]
      (fun _ => ⟨none, [0]⟩) := by
  intro h
  have ha := (h.2.2.2 0 ⟨LogicalKey.ofNat 0, .blindWrite 7⟩
    ⟨0, 0, ApiTests.live 0 7, false⟩ rfl rfl).2.2.1
  contradiction

/-- Initialization really fails on the all-zero tape in the 129-key fixture.
The public shape has one request, and reference execution retains its records. -/
theorem overflow_fails : Fails (geo true).cfg (geo true).shapes
    (OnlineBatch.traceOf online (Adaptive.realized (geo true).cfg (geo true).shapes
      online (syncSchedule (geo true).cfg) IdealProbeOverflowTests.run
      (words (fun _ => 0)) (dummy (fun _ => 0)))) (words (fun _ => 0)) := by
  refine ⟨.initialization, ?_, ?_, ?_⟩
  · exact HierarchyCoveringProof.mem_init rfl
  · decide +kernel
  · decide +kernel

/-- On that actual failure tape, even unrelated requests, physical records and
selected results satisfy the off-failure agreement contract. -/
example (run : OnlineBatch.BatchRun) (requests : List Api.Request)
    (actual : Nat → Probe.Result) :
    ApiBoundedAgreement (geo true) codec online (syncSchedule (geo true).cfg)
      2 64 IdealProbeOverflowTests.batches IdealProbeOverflowTests.initial
      IdealProbeOverflowTests.choose (words (fun _ => 0)) (dummy (fun _ => 0))
      run requests actual := by
  intro hf
  exact False.elim (hf overflow_fails)

/-- Reference execution for a synthetic adapter that discards the entire output
on reference failure. This tests the coupling, not an executable stopping rule. -/
def overflowReference (tape : IdealKey.Tape) :=
  Adaptive.realized (geo true).cfg (geo true).shapes online (syncSchedule (geo true).cfg)
    IdealProbeOverflowTests.run (words tape) (dummy tape)

def overflowRequests (tape : IdealKey.Tape) :=
  (ApiAdaptive.requestGroups
    (ApiLegal.adapt (geo true).cfg (ApiAdaptive.shape IdealProbeOverflowTests.frames)
      (syncSchedule (geo true).cfg) IdealProbeOverflowTests.choose)
    (Adaptive.rowsOf (Adaptive.transcript (geo true).cfg (geo true).shapes online
      (syncSchedule (geo true).cfg) IdealProbeOverflowTests.run 1 (words tape) (dummy tape)) 1)
    IdealProbeOverflowTests.frames).flatMap Group.lanes

def overflowFailed (tape : IdealKey.Tape) : Prop :=
  Fails (geo true).cfg (geo true).shapes (OnlineBatch.traceOf online (overflowReference tape))
    (words tape)

noncomputable def stoppedRun (tape : IdealKey.Tape) : OnlineBatch.BatchRun := by
  classical
  exact if overflowFailed tape then emptyRun else overflowReference tape

noncomputable def stoppedRequests (tape : IdealKey.Tape) : List Api.Request := by
  classical
  exact if overflowFailed tape then [] else overflowRequests tape

noncomputable def stoppedActual (tape : IdealKey.Tape) : Nat → Probe.Result := by
  classical
  exact if overflowFailed tape then absent else
    Probe.batch (geo true).cfg (geo true).shapes online (overflowReference tape)
      (syncSchedule (geo true).cfg) (words tape) (dummy tape)

theorem stopping_agrees (tape : IdealKey.Tape) :
    ApiBoundedAgreement (geo true) codec online (syncSchedule (geo true).cfg)
      2 64 IdealProbeOverflowTests.batches IdealProbeOverflowTests.initial
      IdealProbeOverflowTests.choose (words tape) (dummy tape)
      (stoppedRun tape) (stoppedRequests tape) (stoppedActual tape) := by
  intro hf
  have hfailed : ¬ overflowFailed tape := hf
  simp only [stoppedRun, stoppedRequests, stoppedActual, ite_eq_right hfailed]
  exact ⟨rfl, rfl, fun _ _ => trivial⟩

/-- This is a concrete globally agreeing adapter, with no supplied agreement
hypothesis. Its error event is bounded without conditioning away overflow. -/
theorem stopping_bound :
    IdealKey.tapeLaw {tape | ¬ ApiResultsCorrect (geo true) codec online (stoppedRun tape)
      (syncSchedule (geo true).cfg) 1 (words tape) (dummy tape)
      (stoppedRequests tape) (stoppedActual tape)} ≤ IdealKey.tapeLaw {tape | overflowFailed tape} := by
  exact (ApiBoundedTransfer (geo true) (ApiStructuralTests.structural true) codec online
    (syncSchedule (geo true).cfg) IdealProbeOverflowTests.initial 2 64
    IdealProbeOverflowTests.batches IdealProbeOverflowTests.choose (by decide +kernel)
    IdealProbeOverflowTests.initial_unique (by decide +kernel) rfl (by decide +kernel)
    (by decide +kernel) (SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ b ∈ ([2] : List Nat), 0 < b; decide +kernel)
      (by change 0 < 128; decide +kernel) _)
    IdealKey.tapeLaw words dummy stoppedRun stoppedRequests stoppedActual stopping_agrees).2

/-- Its failure branch is actually reached, and incomplete work is rejected
by the advertised public count rather than accepted as vacuous correctness. -/
example : ¬ ApiResultsCorrect (geo true) codec online (stoppedRun (fun _ => 0))
    (syncSchedule (geo true).cfg) 1 (words (fun _ => 0)) (dummy (fun _ => 0))
    (stoppedRequests (fun _ => 0)) (stoppedActual (fun _ => 0)) := by
  intro h
  have hf : overflowFailed (fun _ => 0) := overflow_fails
  have hlen := h.1
  simp only [stoppedRequests, ite_eq_left hf, List.length_nil] at hlen
  omega

end ApiBoundedTests

namespace IdealBoundedTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.PublicApi MeasureTheory IdealHierarchy
open ApiTests (codec)
open IdealSepUnionTests (member member_valid geo online online_matches)
open ApiStructuralTests (batches)
open IdealTopPrepFamilyTests (frames choose)
open scoped ENNReal

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Both starts inherit the certified numerical bound for actual adapter
answers. The client introduces an empty key and an observation-dependent long key. -/
theorem both_starts (initialized : Bool)
    (runs : IdealKey.Tape → OnlineBatch.BatchRun)
    (requests : IdealKey.Tape → List Api.Request)
    (actual : IdealKey.Tape → Nat → Probe.Result)
    (hagree : ∀ tape, ApiBoundedAgreement (geo initialized) codec online
      (syncSchedule (geo initialized).cfg) 3 64 batches [] (choose _ _ _)
      (words tape) (dummy tape) (runs tape) (requests tape) (actual tape)) :
    IdealKey.tapeLaw {tape | ¬ ApiResultsCorrect (geo initialized) codec online (runs tape)
      (syncSchedule (geo initialized).cfg) 2 (words tape) (dummy tape)
      (requests tape) (actual tape)} ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 64) := by
  have h := IdealApiBounded initialized member member_valid 1 (by decide +kernel)
    codec online (syncSchedule (geo initialized).cfg) [] 3 64 batches (choose _ _ _)
    (by simp [ApiCapacity.InitialStateValid]) (online_matches initialized) (by decide +kernel)
    (by change 2 ≤ 2 ^ 32; decide +kernel)
    (IdealCapacityObservationTests.schedule_valid initialized)
    (IdealCapacityObservationTests.live initialized) runs requests actual hagree
  have hn : Adaptive.slotCount (ApiAdaptive.shape
      (ApiAdaptive.frames 64 online.unitEntries batches)) = 2 := by decide +kernel
  simpa only [geo, hn, Nat.cast_one, one_mul] using h.2

/-- Independent geometric seeds choose keys of every length from 65 upward.
The bound is about the adapter's actual seeded runs, requests and answers. -/
theorem seeded_churn (initialized : Bool)
    (runs : Nat × IdealKey.Tape → OnlineBatch.BatchRun)
    (requests : Nat × IdealKey.Tape → List Api.Request)
    (actual : Nat × IdealKey.Tape → Nat → Probe.Result)
    (hagree : ∀ p, ApiBoundedAgreement (geo initialized) codec online
      (syncSchedule (geo initialized).cfg) 3 1 IdealCapacitySeedTests.batches []
      (IdealCapacitySeedTests.choose initialized p.1)
      (words p.2) (dummy p.2) (runs p) (requests p) (actual p)) :
    (IdealSeedTests.coins.prod IdealKey.tapeLaw) {p | ¬ ApiResultsCorrect (geo initialized)
      codec online (runs p) (syncSchedule (geo initialized).cfg) 2
      (words p.2) (dummy p.2) (requests p) (actual p)} ≤
      ENNReal.ofReal (1 / (2 : ℝ) ^ 64) := by
  have h := IdealSeedBounded Nat IdealSeedTests.coins initialized member member_valid 1
    (by decide +kernel) codec online (syncSchedule (geo initialized).cfg) (fun _ : Nat => [])
    3 1 IdealCapacitySeedTests.batches (IdealCapacitySeedTests.choose initialized)
    (fun _ => by simp [ApiCapacity.InitialStateValid]) (online_matches initialized)
    (by decide +kernel) (by change 2 ≤ 2 ^ 32; decide +kernel)
    (IdealCapacityObservationTests.schedule_valid initialized)
    (fun seed _ => by
      change ApiCapacity.LiveCapacity (geo initialized).keyCapacity (Api.stateOf codec []) []
        [⟨IdealSeedTests.key seed, .write seed⟩, ⟨IdealSeedTests.key seed, .erase⟩]
      have hc := ApiChurnCapacity [IdealSeedTests.key seed] seed
      exact ⟨hc.1, fun k hk => (hc.2 k hk).trans
        (by cases initialized <;> decide +kernel)⟩) runs requests actual hagree
  have hn : Adaptive.slotCount (ApiAdaptive.shape
      (ApiAdaptive.frames 1 online.unitEntries IdealCapacitySeedTests.batches)) = 2 := by
    decide +kernel
  simpa only [geo, hn, Nat.cast_one, one_mul] using h.2

example (dictionary : Finset LogicalKey) :
    ∃ seed, (IdealCapacitySeedTests.choose true seed 0 0 (fun t => Fin.elim0 t) 0).1 ∉ dictionary ∧
      0 < IdealSeedTests.coins {seed} := IdealSeedTests.no_dictionary dictionary

end IdealBoundedTests
