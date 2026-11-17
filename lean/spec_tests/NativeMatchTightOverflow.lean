import RebuildBound.Proofs.NativeMatchTightOverflow
import spec_tests.IdealCapacity

/-! The refined overflow budget read as a real number, the tight capacity
theorem on the concrete adaptive run of `IdealCapacityTests.both_starts`,
the two registered theorems combined into one bound, the same bound for runs
limited to `h * 2^31` accesses with initial records counted, and a member
whose budget is close to that bound. -/
namespace IdealCapacityTightTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.PublicApi
open MeasureTheory IdealHierarchy IdealDirect
open ApiTests (codec)
open IdealSepUnionTests (member member_valid geo online online_matches)
open ApiStructuralTests (batches)
open IdealTopPrepFamilyTests (frames choose run)
open scoped ENNReal

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- `2^-65.5`, squared, is `2^-131`. -/
theorem threshold_mul_self :
    (2 : ℝ) ^ (-(131 : ℝ) / 2) * (2 : ℝ) ^ (-(131 : ℝ) / 2) = 1 / 2 ^ 131 := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [show -(131 : ℝ) / 2 + -(131 : ℝ) / 2 = -((131 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]

/-- The square encoding of `NativeMatchTightOverflow` means that every
member's refined overflow budget, as a real number, is below
`2^-65.5 = (2 : ℝ) ^ (-131 / 2)`. -/
theorem budget_lt (m : ConfigurationFamily.Member) (hm : m ∈ ConfigurationFamily.members) :
    ((NativeMatchTightBudget.exposureBudget m : ℚ) : ℝ) < (2 : ℝ) ^ (-(131 : ℝ) / 2) := by
  obtain ⟨_, hsq⟩ := NativeMatchTightOverflow m hm
  have hsq' : ((NativeMatchTightBudget.exposureBudget m : ℚ) : ℝ) *
      ((NativeMatchTightBudget.exposureBudget m : ℚ) : ℝ) <
      (2 : ℝ) ^ (-(131 : ℝ) / 2) * (2 : ℝ) ^ (-(131 : ℝ) / 2) := by
    rw [threshold_mul_self]
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr hsq
  exact lt_of_mul_self_lt_mul_self₀ (by positivity) hsq'

/-- The same bound in `ℝ≥0∞`, the form used by the capacity theorems. -/
theorem budget_lt_ennreal (m : ConfigurationFamily.Member)
    (hm : m ∈ ConfigurationFamily.members) :
    ENNReal.ofReal (NativeMatchTightBudget.exposureBudget m : ℝ) <
      ENNReal.ofReal ((2 : ℝ) ^ (-(131 : ℝ) / 2)) :=
  (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (budget_lt m hm)

/-- The tight capacity theorem accepts the concrete adaptive run of
`IdealCapacityTests.both_starts` (an empty first key, then an
observation-dependent key longer than 64 bytes, from either start, `h = 1`).
Every premise is discharged, and the overflow probability of that run is below
`2^-65.5`. -/
theorem both_starts (initialized : Bool) :
    IdealKey.tapeLaw {tape | Fails (geo initialized).cfg (geo initialized).shapes
      (trace (geo initialized).cfg (geo initialized).shapes online
        (syncSchedule (geo initialized).cfg) (run initialized) tape) (words tape)} <
      ENNReal.ofReal ((2 : ℝ) ^ (-(131 : ℝ) / 2)) := by
  have h := IdealCapacityTight initialized member member_valid 1 (by decide +kernel)
    codec online (syncSchedule (geo initialized).cfg) [] 3 64 batches (choose _ _ _)
    (by simp [ApiCapacity.InitialStateValid]) (online_matches initialized) (by decide +kernel)
    (by change 2 ≤ 2 ^ 32; decide +kernel)
    (IdealCapacityObservationTests.schedule_valid initialized)
    (IdealCapacityObservationTests.live initialized)
  have h' : IdealKey.tapeLaw {tape | Fails (geo initialized).cfg (geo initialized).shapes
      (trace (geo initialized).cfg (geo initialized).shapes online
        (syncSchedule (geo initialized).cfg) (run initialized) tape) (words tape)} ≤
      ENNReal.ofReal (NativeMatchTightBudget.exposureBudget member : ℝ) := by
    simpa only [geo, run, frames, Nat.cast_one, one_mul] using h
  exact h'.trans_lt (budget_lt_ennreal member member_valid)

/-- Under exactly the premises of `IdealCapacityTight_statement`, which are
those of `IdealCapacity_statement`, the overflow probability is below
`h * 2^-65.5`. A window is `2^32` accesses, and initial records are not
counted. Derived from `IdealCapacityTight` and `NativeMatchTightOverflow`
only. -/
theorem capacity_lt :
    ∀ (initialized : Bool) (member : ConfigurationFamily.Member),
      member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
      let geo := (member.geometry initialized).chunk h
      ∀ (c : Api.Codec) g S init m width batches,
      let fs := ApiAdaptive.frames width g.unitEntries batches
      ∀ choose : ApiLegal.Chooser geo.cfg (ApiAdaptive.shape fs) S m,
      let n := Adaptive.slotCount (ApiAdaptive.shape fs)
      let compiled := ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose
      ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized init →
      g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
      0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
      (∀ t : ApiLegal.Prefix geo.cfg (ApiAdaptive.shape fs) S m n,
        ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c init) (init.map Rec.key)
          ((ApiAdaptive.requestGroups compiled (Adaptive.rowsOf (ApiLegal.erase t) n) fs).flatMap
            PublicApi.Group.lanes)) →
      let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled
      IdealKey.tapeLaw {tape | Fails geo.cfg geo.shapes
        (trace geo.cfg geo.shapes g S a tape) (words tape)} <
        (h : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(131 : ℝ) / 2)) := by
  intro initialized member hm h hh geo c g S init m width batches fs choose n compiled
    hinit hgeom hE hn hS hcap a
  have hb := IdealCapacityTight initialized member hm h hh c g S init m width batches
    choose hinit hgeom hE hn hS hcap
  have hz : (h : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  exact hb.trans_lt (ENNReal.mul_lt_mul_right hz (by finiteness) (budget_lt_ennreal member hm))

/-- The same bound for a run that initializes `I` records and makes `n`
accesses with `I + n ≤ h * 2^31`: such a run is within the horizon of `h`
windows. -/
theorem capacity_lt_counting_initial :
    ∀ (initialized : Bool) (member : ConfigurationFamily.Member),
      member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
      let geo := (member.geometry initialized).chunk h
      ∀ (c : Api.Codec) g S init m width batches,
      let fs := ApiAdaptive.frames width g.unitEntries batches
      ∀ choose : ApiLegal.Chooser geo.cfg (ApiAdaptive.shape fs) S m,
      let n := Adaptive.slotCount (ApiAdaptive.shape fs)
      let compiled := ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose
      ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized init →
      g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
      0 < g.unitEntries → init.length + n ≤ h * 2 ^ 31 → SchedulePremises geo.cfg S n m →
      (∀ t : ApiLegal.Prefix geo.cfg (ApiAdaptive.shape fs) S m n,
        ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c init) (init.map Rec.key)
          ((ApiAdaptive.requestGroups compiled (Adaptive.rowsOf (ApiLegal.erase t) n) fs).flatMap
            PublicApi.Group.lanes)) →
      let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled
      IdealKey.tapeLaw {tape | Fails geo.cfg geo.shapes
        (trace geo.cfg geo.shapes g S a tape) (words tape)} <
        (h : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(131 : ℝ) / 2)) := by
  intro initialized member hm h hh geo c g S init m width batches fs choose n compiled
    hinit hgeom hE hn hS hcap a
  have hhor : n ≤ geo.cfg.horizon := by
    change n ≤ h * 2 ^ 32
    omega
  exact capacity_lt initialized member hm h hh c g S init m width batches choose
    hinit hgeom hE hhor hS hcap

/-- The member with the largest refined budget. -/
def largest : ConfigurationFamily.Member :=
  ⟨"L8_r2_D8_8.8.8.8.8.8.8", 2, [8, 8, 8, 8, 8, 8, 8], [1, 1, 1, 1, 2, 2, 2, 3],
    [1, 1, 1, 1, 2, 2, 2, 4]⟩

theorem largest_valid : largest ∈ ConfigurationFamily.members := by
  simp [largest, ConfigurationFamily.members]

/-- The bound `2^-65.5` is not slack: the largest budget `x` (about
`0.3417 * 2^-64`) satisfies `x * x > 0.81 * 2^-131`, so it is above
`0.9 * 2^-65.5`, and in particular above `2^-66`. -/
theorem not_slack : ∃ m ∈ ConfigurationFamily.members,
    81 / (100 * 2 ^ 131) <
      NativeMatchTightBudget.exposureBudget m * NativeMatchTightBudget.exposureBudget m ∧
    1 / 2 ^ 132 <
      NativeMatchTightBudget.exposureBudget m * NativeMatchTightBudget.exposureBudget m := by
  refine ⟨largest, largest_valid, ?_⟩
  decide +kernel

end IdealCapacityTightTests
