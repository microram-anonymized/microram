import RebuildBound.Proofs.ApiStructural
import spec_tests.ApiExecution

/-! Request-level non-vacuity without a historical key universe. The actual
constructor, rather than a supplied flag or lookup promise, feeds both the
correctness and population theorems. All results hold on arbitrary tapes. -/
namespace ApiStructuralTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Model.PublicApi
open RebuildBound.Model.ApiCapacity
open ApiTests (codec)

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Shape checks permit a declared live capacity of zero. Physical dimensions
are unchanged, and are deliberately independent of the requested key values. -/
def geo (initialized : Bool) : HierarchyGeometry :=
  { AdaptiveSemanticsTest.geometry initialized with keyCapacity := 0 }
abbrev online := AdaptiveSemanticsTest.online

theorem structural (initialized : Bool) : (geo initialized).Structural := by
  cases initialized <;> decide +kernel

def missGroups (keys : List LogicalKey) : List (PublicApi.Group Api.Request) :=
  keys.map fun key => .chunk [⟨key, .read⟩]

theorem miss_requests (keys : List LogicalKey) :
    (missGroups keys).flatMap Group.lanes = keys.map fun key => (⟨key, .read⟩ : Api.Request) := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simp only [missGroups, List.map_cons, List.flatMap_cons, Group.lanes,
      List.singleton_append, List.map_cons] at ih ⊢; exact congrArg (List.cons _) ih

theorem miss_valid (keys : List LogicalKey) : ∀ group ∈ missGroups keys, ApiExecution.Valid group := by
  intro group hgroup
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp hgroup
  simp [ApiExecution.Valid, Api.Request.probes]

theorem miss_fit (keys : List LogicalKey) (position : Nat) :
    GroupsFit online.unitEntries position (missGroups keys) := by
  induction keys generalizing position with
  | nil => trivial
  | cons key keys ih =>
    refine ⟨by simp [Group.lanes], ?_, ih _⟩
    change 1 ≤ 64 - position % 64
    have := Nat.mod_lt position (by decide +kernel : 0 < 64)
    omega

def misses (initialized : Bool) (keys : List LogicalKey) : OnlineBatch.BatchRun :=
  ApiExecution.run codec (geo initialized).cfg (geo initialized).shapes online
    (syncSchedule (geo initialized).cfg) [] (missGroups keys)

/-- Arbitrarily many misses remain admissible at zero live capacity; keys are
neither restricted in width nor required to form a capacity-sized dictionary. -/
theorem misses_both_starts (initialized : Bool) (keys : List LogicalKey)
    (hlen : keys.length ≤ 2 ^ 32) :
    ApiRunCorrect (geo initialized) codec online (misses initialized keys)
      (syncSchedule (geo initialized).cfg) (keys.map fun key => ⟨key, .read⟩) ∧
    ApiTopPopulations (geo initialized) online (misses initialized keys) := by
  have h := ApiExecutionLive (geo initialized) (structural initialized) codec online
    (syncSchedule (geo initialized).cfg) [] (missGroups keys) 2
  rw [miss_requests] at h
  apply h
  · simp [InitialStateValid]
  · rfl
  · decide +kernel
  · change (keys.map fun key => (⟨key, .read⟩ : Api.Request)).length ≤ 2 ^ 32
    simpa only [List.length_map] using hlen
  · exact miss_valid keys
  · exact miss_fit keys 0
  · exact SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ b ∈ ([2] : List Nat), 0 < b; decide +kernel)
      (by change 0 < 128; decide +kernel) _
  · exact ApiMissCapacity keys

def wideKeys : List LogicalKey :=
  (List.range 256).map fun i => LogicalKey.ofNat (2 ^ 130 + i)

example : wideKeys.length > (geo false).keyCapacity := by decide +kernel
example : ∀ key ∈ wideKeys, 2 ^ 64 < LogicalKey.toNat key := by
  intro key hkey
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hkey
  rw [LogicalKey.toNat_ofNat]
  have : 2 ^ 64 < (2 ^ 130 : Nat) := by decide +kernel
  omega
example : wideKeys.Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro a b hab
  have hn := congrArg LogicalKey.toNat hab
  simp only [LogicalKey.toNat_ofNat] at hn
  omega

/-- All 256 input positions are real execution slots, so four 64-position
units are complete. No evaluation of the expensive physical constructor occurs. -/
theorem wide_cut (initialized : Bool) :
    4 ≤ (OnlineBatch.stateAt online (misses initialized wideKeys)
      (misses initialized wideKeys).ops.length).frozen.length := by
  let run := misses initialized wideKeys
  have hI := BatchFreshProof.inv_stateAt online run (by decide +kernel) run.ops.length le_rfl
  have hi := ((misses_both_starts initialized wideKeys (by decide +kernel)).1.2.2
    (fun _ _ _ => 0) (fun _ _ => 0)).1
  have hlen : (OnlineBatch.slots run).length = 256 := by
    rw [← hi.length]
    simp [wideKeys]
  have hs := hI.len
  rw [BatchFreshProof.fs_length, hlen] at hs
  have hc := hI.cur
  change _ * 64 + _ = 256 at hs
  change _ < 64 at hc
  change 4 ≤ (OnlineBatch.stateAt online run run.ops.length).frozen.length
  omega

/-- An actual finish one ordinal beyond the seed has all three job populations
bounded by zero, for either start and every routing tape. -/
theorem top_finish (initialized : Bool) (words : Words) :
    let run := misses initialized wideKeys
    let v := (geo initialized).cfg.seed (geo initialized).cfg.levels + 1
    (prepInputsAt (geo initialized).cfg (geo initialized).shapes
      (OnlineBatch.traceOf online run) words v).aAll.length = 0 ∧
    (finishInputsAt (geo initialized).cfg (geo initialized).shapes
      (OnlineBatch.traceOf online run) words v).aAll.length = 0 ∧
    (finishInputsAt (geo initialized).cfg (geo initialized).shapes
      (OnlineBatch.traceOf online run) words v).live.length = 0 := by
  have h := (misses_both_starts initialized wideKeys (by decide +kernel)).2.2 words
    ((geo initialized).cfg.seed (geo initialized).cfg.levels + 1) (by omega)
    (by cases initialized <;> decide +kernel)
  obtain ⟨ha, hb, hc⟩ := h
  exact ⟨Nat.eq_zero_of_le_zero ha, Nat.eq_zero_of_le_zero hb, Nat.eq_zero_of_le_zero hc⟩

/-- Every potential top ordinal is covered even when the finite run is too
short to freeze one unit. Empty future inputs do not add logical requests. -/
theorem every_miss_top (initialized : Bool) (keys : List LogicalKey)
    (hlen : keys.length ≤ 2 ^ 32) (words : Words) (v : Nat)
    (hv : (geo initialized).cfg.seed (geo initialized).cfg.levels < v)
    (hvh : v ≤ (geo initialized).cfg.seed (geo initialized).cfg.levels +
      (geo initialized).cfg.ordinals (geo initialized).cfg.levels) :
    (prepInputsAt (geo initialized).cfg (geo initialized).shapes
      (OnlineBatch.traceOf online (misses initialized keys)) words v).aAll.length = 0 ∧
    (finishInputsAt (geo initialized).cfg (geo initialized).shapes
      (OnlineBatch.traceOf online (misses initialized keys)) words v).aAll.length = 0 ∧
    (finishInputsAt (geo initialized).cfg (geo initialized).shapes
      (OnlineBatch.traceOf online (misses initialized keys)) words v).live.length = 0 := by
  obtain ⟨ha, hb, hc⟩ := (misses_both_starts initialized keys hlen).2.2 words v hv hvh
  exact ⟨Nat.eq_zero_of_le_zero ha, Nat.eq_zero_of_le_zero hb, Nat.eq_zero_of_le_zero hc⟩

/-- The two-miss run really has no frozen unit; this is a strict extension of
what the former complete-cut population theorem could instantiate. -/
theorem short_run_no_frozen (initialized : Bool) :
    (OnlineBatch.stateAt online (misses initialized [LogicalKey.ofNat (2 ^ 130), LogicalKey.ofNat (2 ^ 131)])
      (misses initialized [LogicalKey.ofNat (2 ^ 130), LogicalKey.ofNat (2 ^ 131)]).ops.length).frozen.length = 0 := by
  let run := misses initialized [LogicalKey.ofNat (2 ^ 130), LogicalKey.ofNat (2 ^ 131)]
  have hI := BatchFreshProof.inv_stateAt online run (by decide +kernel) run.ops.length le_rfl
  have hi := ((misses_both_starts initialized [LogicalKey.ofNat (2 ^ 130), LogicalKey.ofNat (2 ^ 131)] (by decide +kernel)).1.2.2
    (fun _ _ _ => 0) (fun _ _ => 0)).1
  have he := hI.len
  rw [BatchFreshProof.fs_length, ← hi.length] at he
  change _ * 64 + _ = 2 at he
  change (OnlineBatch.stateAt online run run.ops.length).frozen.length = 0
  omega

example (initialized : Bool) (words : Words) :
    (finishInputsAt (geo initialized).cfg (geo initialized).shapes
      (OnlineBatch.traceOf online (misses initialized [LogicalKey.ofNat (2 ^ 130), LogicalKey.ofNat (2 ^ 131)])) words
      ((geo initialized).cfg.seed (geo initialized).cfg.levels + 1)).live.length = 0 := by
  exact (every_miss_top initialized _ (by decide +kernel) words _ (by omega)
    (by cases initialized <;> decide +kernel)).2.2

/-- Correctness continues unconditionally even when a request violates the
separate logical capacity contract. -/
def inserts : List (PublicApi.Group Api.Request) :=
  [.blind ⟨LogicalKey.ofNat (2 ^ 130), .blindWrite 10⟩, .blind ⟨LogicalKey.ofNat (2 ^ 130 + 1), .blindWrite 20⟩]

theorem overcapacity_correct (initialized : Bool) :
    ApiRunCorrect (geo initialized) codec online
      (ApiExecution.run codec (geo initialized).cfg (geo initialized).shapes online
        (syncSchedule (geo initialized).cfg) [] inserts)
      (syncSchedule (geo initialized).cfg) (inserts.flatMap Group.lanes) := by
  apply ApiExecutionStructural (geo initialized) (structural initialized) codec online
    (syncSchedule (geo initialized).cfg) [] inserts 2
  · intro _; rfl
  · simp
  · simp
  · rfl
  · decide +kernel
  · change 2 ≤ 2 ^ 32
    decide +kernel
  · intro group hgroup
    simp [inserts] at hgroup
    rcases hgroup with rfl | rfl <;> rfl
  · exact SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ b ∈ ([2] : List Nat), 0 < b; decide +kernel)
      (by change 0 < 128; decide +kernel) _

example : ¬ LiveCapacity 0 (Api.stateOf codec []) [] (inserts.flatMap Group.lanes) := by
  intro h
  have hc := h.2 1 (by decide +kernel)
  have hlen : (ApiCapacity.supportAt (Api.stateOf codec []) []
      (inserts.flatMap Group.lanes) 1).length = 1 := by decide +kernel
  rw [hlen] at hc
  omega

/-- Nonempty initialized input uses an exact key beyond 64 bits. It needs only
its actual record count, independently of the declared live capacity. -/
def initial (initialized : Bool) : List Rec :=
  if initialized then [ApiTests.live (2 ^ 130) 19] else []
def initialRun (initialized : Bool) : OnlineBatch.BatchRun :=
  ApiExecution.run codec (geo initialized).cfg (geo initialized).shapes online
    (syncSchedule (geo initialized).cfg) (initial initialized) (missGroups [LogicalKey.ofNat (2 ^ 130)])

theorem initialized_read_correct (initialized : Bool) :
    ApiRunCorrect (geo initialized) codec online (initialRun initialized)
      (syncSchedule (geo initialized).cfg) [⟨LogicalKey.ofNat (2 ^ 130), .read⟩] := by
  apply ApiExecutionStructural (geo initialized) (structural initialized) codec online
    (syncSchedule (geo initialized).cfg) (initial initialized) (missGroups [LogicalKey.ofNat (2 ^ 130)]) 2
  · intro h
    change initialized = false at h
    simp [initial, h]
  · cases initialized <;> simp [initial]
  · cases initialized <;> decide +kernel
  · rfl
  · decide +kernel
  · change 1 ≤ 2 ^ 32
    decide +kernel
  · exact miss_valid _
  · exact SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ b ∈ ([2] : List Nat), 0 < b; decide +kernel)
      (by change 0 < 128; decide +kernel) _

/-- The first physical probe returns the supplied live value on every tape. -/
theorem initialized_read_value (initialized : Bool) (words : Words) (dummy : Nat → Nat → Nat) :
    Api.value codec (Probe.batch (geo initialized).cfg (geo initialized).shapes online
      (initialRun initialized) (syncSchedule (geo initialized).cfg) words dummy 0).found =
      if initialized then some 19 else none := by
  obtain ⟨hi, hc⟩ := (initialized_read_correct initialized).2.2 words dummy
  have ht : 0 < (OnlineBatch.slots (initialRun initialized)).length := by
    rw [← hi.length]
    decide +kernel
  let s := (OnlineBatch.slots (initialRun initialized))[0]
  have hs : (OnlineBatch.slots (initialRun initialized))[0]? = some s :=
    List.getElem?_eq_getElem ht
  have hr := (hc.2 0 ⟨LogicalKey.ofNat (2 ^ 130), .read⟩ s rfl hs).1
  change Api.value codec (Probe.batch _ _ _ _ _ words dummy 0).found =
    Api.stateOf codec (initial initialized) (LogicalKey.ofNat (2 ^ 130)) at hr
  exact hr.trans (by cases initialized <;> decide +kernel)

/-- A nonempty initial map with no requests has no frozen units, but every
modeled top job still inherits the initialization capacity. -/
def initialOnlyGeo : HierarchyGeometry :=
  { AdaptiveSemanticsTest.geometry true with keyCapacity := 1 }
def initialOnlyRun : OnlineBatch.BatchRun :=
  ApiExecution.run codec initialOnlyGeo.cfg initialOnlyGeo.shapes online
    (syncSchedule initialOnlyGeo.cfg) [ApiTests.live (2 ^ 130) 19] []

theorem initial_only_populations : ApiTopPopulations initialOnlyGeo online initialOnlyRun := by
  have hinit : InitialStateValid initialOnlyGeo.keyCapacity initialOnlyGeo.cfg.initialized
      [ApiTests.live (2 ^ 130) 19] := by
    change InitialStateValid 1 true [ApiTests.live (2 ^ 130) 19]
    simp [InitialStateValid, ApiTests.live]
  exact (ApiExecutionLive initialOnlyGeo (by decide +kernel) codec online
    (syncSchedule initialOnlyGeo.cfg) [ApiTests.live (2 ^ 130) 19] [] 2 hinit
    rfl (by decide +kernel) (by decide +kernel) (by simp) trivial
    (SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ b ∈ ([2] : List Nat), 0 < b; decide +kernel)
      (by change 0 < 128; decide +kernel) _)
    (ApiInitialCapacity _ _ _ hinit codec).2).2

example : RequesterCuts.traceCutSlots online initialOnlyRun 1 = 0 := by decide +kernel

/-- The second public batch sees earlier observations and chooses a new key.
The arbitrary Nat rows are the current intermediate observation interface. -/
def batches : List ApiAdaptive.Batch :=
  [⟨false, [⟨.read, true, false⟩]⟩, ⟨false, [⟨.read, true, false⟩]⟩]
def chooseAt (base : Nat) : ApiAdaptive.Chooser 2 := fun _ rows _ =>
  (LogicalKey.ofNat (base + (rows.getLastD (fun _ => 0)) 0), 0)
abbrev choose := chooseAt (2 ^ 130)
def frames := ApiAdaptive.frames 64 online.unitEntries batches

theorem adaptive_requests_at (base : Nat) (rows : List (Fin 2 → Nat)) :
    (ApiAdaptive.requestGroups (chooseAt base) rows frames).flatMap Group.lanes =
      [⟨LogicalKey.ofNat (base), .read⟩, ⟨LogicalKey.ofNat (base + (rows.take 1).getLastD (fun _ => 0) 0), .read⟩] := by
  rfl

theorem adaptive_requests (rows : List (Fin 2 → Nat)) :
    (ApiAdaptive.requestGroups choose rows frames).flatMap Group.lanes =
      [⟨LogicalKey.ofNat (2 ^ 130), .read⟩, ⟨LogicalKey.ofNat (2 ^ 130 + (rows.take 1).getLastD (fun _ => 0) 0), .read⟩] :=
  adaptive_requests_at (2 ^ 130) rows

/-- Every branch satisfies zero live capacity, without collecting its keys
with those of any other branch. -/
theorem adaptive_both_starts (initialized : Bool) (words : Words) (dummy : Nat → Nat → Nat) :
    let a := ApiAdaptive.run codec (geo initialized).cfg (geo initialized).shapes online
      (syncSchedule (geo initialized).cfg) [] frames choose
    let t := Adaptive.transcript (geo initialized).cfg (geo initialized).shapes online
      (syncSchedule (geo initialized).cfg) a 2 words dummy
    let qs := (ApiAdaptive.requestGroups choose (Adaptive.rowsOf t 2) frames).flatMap Group.lanes
    let realized := Adaptive.realized (geo initialized).cfg (geo initialized).shapes online
      (syncSchedule (geo initialized).cfg) a words dummy
    ApiRunCorrect (geo initialized) codec online realized
      (syncSchedule (geo initialized).cfg) qs ∧ ApiTopPopulations (geo initialized) online realized := by
  refine ApiAdaptiveLive (geo initialized) (structural initialized) codec online
    (syncSchedule (geo initialized).cfg) [] 2 64 batches choose
    ?_ rfl (by decide +kernel) ?_ ?_ ?_ words dummy
  · simp [InitialStateValid]
  · change 2 ≤ 2 ^ 32
    decide +kernel
  · exact SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ b ∈ ([2] : List Nat), 0 < b; decide +kernel)
      (by change 0 < 128; decide +kernel) _
  · intro t
    change LiveCapacity 0 (Api.stateOf codec []) []
      ((ApiAdaptive.requestGroups choose (Adaptive.rowsOf t 2) frames).flatMap Group.lanes)
    rw [adaptive_requests]
    exact ApiMissCapacity [LogicalKey.ofNat (2 ^ 130),
      LogicalKey.ofNat (2 ^ 130 + ((Adaptive.rowsOf t 2).take 1).getLastD (fun _ => 0) 0)]

/-- No fixed numeric upper bound covers all keys on candidate branches. The
second request really depends on an earlier row, not on a future one. -/
theorem candidate_unbounded (bound : Nat) : ∃ t : Fin 2 → Fin 2 → Nat,
    ∃ q ∈ (ApiAdaptive.requestGroups choose (Adaptive.rowsOf t 2) frames).flatMap Group.lanes,
      bound < LogicalKey.toNat q.key := by
  refine ⟨(fun _ _ => bound + 1), ⟨LogicalKey.ofNat (2 ^ 130 + (bound + 1)), .read⟩, ?_, ?_⟩
  · rw [adaptive_requests]
    simp [Adaptive.rowsOf, List.range_succ]
  · simp only [LogicalKey.toNat_ofNat]
    omega

/-- In particular there is no single finite dictionary containing the keys on
all candidate branches of this capacity-zero client. -/
example : ¬ ∃ U : Finset LogicalKey, ∀ (t : Fin 2 → Fin 2 → Nat) q,
    q ∈ (ApiAdaptive.requestGroups choose (Adaptive.rowsOf t 2) frames).flatMap Group.lanes →
      q.key ∈ U := by
  rintro ⟨U, hU⟩
  obtain ⟨t, q, hq, hbound⟩ := candidate_unbounded (U.sup LogicalKey.toNat)
  have hle : LogicalKey.toNat q.key ≤ U.sup LogicalKey.toNat := Finset.le_sup (f := LogicalKey.toNat) (hU t q hq)
  omega

end ApiStructuralTests
