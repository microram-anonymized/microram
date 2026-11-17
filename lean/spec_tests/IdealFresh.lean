import RebuildBound.Proofs.IdealFresh
import spec_tests.ApiStructural

/-! Tests of `IdealApiFresh` on the adaptive two-read client of
`spec_tests/ApiStructural.lean`, whose second key is computed from the bucket
the first read touched. The premises are discharged for both starts and every
word function and dummy tape. Under one word function the two requests have
different keys and both probe the same table really; under the all-zero words
they repeat one key, and the second probe of that key is a dummy. -/
namespace IdealFreshTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Model.PublicApi
open ApiTests (codec)
open ApiStructuralTests (geo online batches choose frames structural)

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The conclusion of `IdealApiFresh_statement` for one realized run with `n`
slots and plans of at most `m` tables. -/
def FreshRun (geo : HierarchyGeometry) (g : OnlineGeom) (S : Schedule) (words : Words)
    (run : OnlineBatch.BatchRun) (n m : Nat) : Prop :=
  ∀ t i t' i' c₁ c₂ s₁ s₂, t < n → i < m → t' < n → i' < m → (t, i) ≠ (t', i') →
    OnlineBatch.isReal geo.cfg geo.shapes g run S words t i = true →
    OnlineBatch.isReal geo.cfg geo.shapes g run S words t' i' = true →
    (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables[i]? = some c₁ →
    (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t').tables[i']? = some c₂ →
    (OnlineBatch.slots run)[t]? = some s₁ → (OnlineBatch.slots run)[t']? = some s₂ →
    (familyOf geo.cfg c₁.1 c₁.2, s₁.record.key) ≠ (familyOf geo.cfg c₂.1 c₂.2, s₂.record.key)

abbrev schedule (initialized : Bool) : Schedule := syncSchedule (geo initialized).cfg

def adaptiveRun (initialized : Bool) : Adaptive.AdaptiveRun 2 :=
  ApiAdaptive.run codec (geo initialized).cfg (geo initialized).shapes online
    (schedule initialized) [] frames choose

def realized (initialized : Bool) (words : Words) (dummy : Nat → Nat → Nat) :
    OnlineBatch.BatchRun :=
  Adaptive.realized (geo initialized).cfg (geo initialized).shapes online
    (schedule initialized) (adaptiveRun initialized) words dummy

example : Adaptive.slotCount (ApiAdaptive.shape frames) = 2 := by decide +kernel

/-- Non-vacuity of the premises: every premise is discharged on the adaptive
run, for both starts. The freshness conclusion then holds for every word
function and dummy tape. -/
theorem adaptive_fresh (initialized : Bool) (words : Words) (dummy : Nat → Nat → Nat) :
    FreshRun (geo initialized) online (schedule initialized) words
      (realized initialized words dummy) 2 2 :=
  IdealApiFresh (geo initialized) (structural initialized) codec online
    (schedule initialized) [] 2 64 batches choose
    (fun _ => rfl) (by simp) (by simp) rfl (by decide +kernel)
    (by change 2 ≤ 2 ^ 32; decide +kernel)
    (SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ b ∈ ([2] : List Nat), 0 < b; decide +kernel)
      (by change 0 < 128; decide +kernel) _)
    words dummy

/-- Word functions for the concrete probes: all ones and all zeros. -/
def ones : Words := fun _ _ _ => 1
def zeros : Words := fun _ _ _ => 0
def noDummy : Nat → Nat → Nat := fun _ _ => 0

/-- Under `ones` the first read touches bucket one, so the second key is the
first plus one. Both slots probe and use the plan of the top table `(2, 0)`. -/
example : (OnlineBatch.slots (realized false ones noDummy)).map
      (fun s => (s.op, s.lane, s.record.key, s.probes)) =
    [(0, 0, LogicalKey.ofNat (2 ^ 130), true), (1, 0, LogicalKey.ofNat (2 ^ 130 + 1), true)] ∧
    (OnlineBatch.slotSchedule (OnlineBatch.widths (realized false ones noDummy))
      (schedule false) 0).tables = [(2, 0)] ∧
    (OnlineBatch.slotSchedule (OnlineBatch.widths (realized false ones noDummy))
      (schedule false) 1).tables = [(2, 0)] := by
  decide +kernel

/-- Non-vacuity of the conclusion's hypotheses: two different probes, `(0, 0)`
and `(1, 0)`, are both real, with their table entries and slots present, so the
theorem applies to them. They probe the same table under different keys. -/
theorem two_real_probes : ∃ c₁ c₂ s₁ s₂,
    OnlineBatch.isReal (geo false).cfg (geo false).shapes online
      (realized false ones noDummy) (schedule false) ones 0 0 = true ∧
    OnlineBatch.isReal (geo false).cfg (geo false).shapes online
      (realized false ones noDummy) (schedule false) ones 1 0 = true ∧
    (OnlineBatch.slotSchedule (OnlineBatch.widths (realized false ones noDummy))
      (schedule false) 0).tables[0]? = some c₁ ∧
    (OnlineBatch.slotSchedule (OnlineBatch.widths (realized false ones noDummy))
      (schedule false) 1).tables[0]? = some c₂ ∧
    (OnlineBatch.slots (realized false ones noDummy))[0]? = some s₁ ∧
    (OnlineBatch.slots (realized false ones noDummy))[1]? = some s₂ ∧
    c₁ = c₂ ∧ s₁.record.key ≠ s₂.record.key ∧
    (familyOf (geo false).cfg c₁.1 c₁.2, s₁.record.key) ≠
      (familyOf (geo false).cfg c₂.1 c₂.2, s₂.record.key) := by
  have hr₁ : OnlineBatch.isReal (geo false).cfg (geo false).shapes online
      (realized false ones noDummy) (schedule false) ones 0 0 = true := by decide +kernel
  have hr₂ : OnlineBatch.isReal (geo false).cfg (geo false).shapes online
      (realized false ones noDummy) (schedule false) ones 1 0 = true := by decide +kernel
  have hc₁ : (OnlineBatch.slotSchedule (OnlineBatch.widths (realized false ones noDummy))
      (schedule false) 0).tables[0]? = some (2, 0) := by decide +kernel
  have hc₂ : (OnlineBatch.slotSchedule (OnlineBatch.widths (realized false ones noDummy))
      (schedule false) 1).tables[0]? = some (2, 0) := by decide +kernel
  have hs₁ : ((OnlineBatch.slots (realized false ones noDummy))[0]?).isSome = true := by
    decide +kernel
  have hs₂ : ((OnlineBatch.slots (realized false ones noDummy))[1]?).isSome = true := by
    decide +kernel
  obtain ⟨s₁, hs₁⟩ := Option.isSome_iff_exists.mp hs₁
  obtain ⟨s₂, hs₂⟩ := Option.isSome_iff_exists.mp hs₂
  have hk : (OnlineBatch.slots (realized false ones noDummy)).map (fun s => s.record.key) =
      [LogicalKey.ofNat (2 ^ 130), LogicalKey.ofNat (2 ^ 130 + 1)] := by decide +kernel
  have hk₁ : s₁.record.key = LogicalKey.ofNat (2 ^ 130) := by
    have h := congrArg (fun l => l[0]?) hk
    simp only [List.getElem?_map, hs₁, Option.map_some] at h
    exact Option.some.inj h
  have hk₂ : s₂.record.key = LogicalKey.ofNat (2 ^ 130 + 1) := by
    have h := congrArg (fun l => l[1]?) hk
    simp only [List.getElem?_map, hs₂, Option.map_some] at h
    exact Option.some.inj h
  refine ⟨(2, 0), (2, 0), s₁, s₂, hr₁, hr₂, hc₁, hc₂, hs₁, hs₂, rfl, ?_, ?_⟩
  · rw [hk₁, hk₂]
    decide +kernel
  · exact adaptive_fresh false ones noDummy 0 0 1 0 (2, 0) (2, 0) s₁ s₂
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hr₁ hr₂ hc₁ hc₂ hs₁ hs₂

/-- Under `zeros` the first read touches bucket zero, so the second request
repeats the first key against the same table. The first probe is real and the
second is a dummy, as the theorem requires. -/
example : (OnlineBatch.slots (realized false zeros noDummy)).map (fun s => s.record.key) =
      [LogicalKey.ofNat (2 ^ 130), LogicalKey.ofNat (2 ^ 130)] ∧
    (OnlineBatch.slotSchedule (OnlineBatch.widths (realized false zeros noDummy))
      (schedule false) 0).tables = [(2, 0)] ∧
    (OnlineBatch.slotSchedule (OnlineBatch.widths (realized false zeros noDummy))
      (schedule false) 1).tables = [(2, 0)] ∧
    OnlineBatch.isReal (geo false).cfg (geo false).shapes online
      (realized false zeros noDummy) (schedule false) zeros 0 0 = true ∧
    OnlineBatch.isReal (geo false).cfg (geo false).shapes online
      (realized false zeros noDummy) (schedule false) zeros 1 0 = false := by
  decide +kernel

/-- The informal sentence: under the theorem's premises, two different
probes with the same key whose tables have the same hash family are not both
real. -/
theorem not_both_real : ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ (c : Api.Codec) g S init m width batches,
    let fs := ApiAdaptive.frames width g.unitEntries batches
    ∀ choose : ApiAdaptive.Chooser m,
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    (geo.cfg.initialized = false → init = []) →
    (init.map Rec.key).Nodup → init.length ≤ geo.init.C / 2 * geo.init.T →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    ∀ (words : Words) (dummy : Nat → Nat → Nat),
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs choose
    let run := Adaptive.realized geo.cfg geo.shapes g S a words dummy
    ∀ t i t' i' c₁ c₂ s₁ s₂, t < n → i < m → t' < n → i' < m → (t, i) ≠ (t', i') →
      (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables[i]? = some c₁ →
      (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t').tables[i']? = some c₂ →
      (OnlineBatch.slots run)[t]? = some s₁ → (OnlineBatch.slots run)[t']? = some s₂ →
      s₁.record.key = s₂.record.key →
      familyOf geo.cfg c₁.1 c₁.2 = familyOf geo.cfg c₂.1 c₂.2 →
      ¬ (OnlineBatch.isReal geo.cfg geo.shapes g run S words t i = true ∧
        OnlineBatch.isReal geo.cfg geo.shapes g run S words t' i' = true) := by
  intro geo hgeo c g S init m width batches fs choose n hInit hinit hLen hg hE hhor hS
    words dummy a run t i t' i' c₁ c₂ s₁ s₂ ht hi ht' hi' hne hc₁ hc₂ hs₁ hs₂ hkey hfam hreal
  exact IdealApiFresh geo hgeo c g S init m width batches choose hInit hinit hLen hg hE hhor hS
    words dummy t i t' i' c₁ c₂ s₁ s₂ ht hi ht' hi' hne hreal.1 hreal.2 hc₁ hc₂ hs₁ hs₂
    (by rw [hfam, hkey])

end IdealFreshTests
