import RebuildBound.Proofs.IdealDirectA
import spec_tests.IdealDirect

/-! Two-family A regressions: exact long keys, nonempty reference fallback,
and actual certified direct/DFS jobs from either start. -/
namespace IdealDirectATests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.DirectJob MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Two concrete family members exercise both A distribution plans. -/
def member (dfs : Bool) : ConfigurationFamily.Member :=
  if dfs then ⟨"L2_r4_D8_2", 4, [2], [1, 1], [1, 1]⟩
  else ⟨"L2_r2_D8_2", 2, [2], [1, 1], [1, 1]⟩

theorem member_valid (dfs : Bool) : member dfs ∈ ConfigurationFamily.members := by
  cases dfs
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

example : ((member false).direct 2).ranges = .direct := by decide +kernel
example : ∃ i r p, ((member true).direct 2).ranges = .dfs i r p := by
  exact ⟨0, 4, 320, by decide +kernel⟩

def geo (initialized dfs : Bool) : HierarchyGeometry :=
  ((member dfs).geometry initialized).chunk 1

def online (dfs : Bool) : Online.OnlineGeom := ⟨32 * (2 * (member dfs).r0), 1⟩
def client (dfs : Bool) : Adaptive.AdaptiveRun 1 :=
  ⟨[.chunk (online dfs).unitEntries, .chunk (online dfs).unitEntries], [],
    fun _ => false, fun _ i => ⟨List.replicate (65 + i) 0, i, false⟩⟩

def schedule (initialized dfs : Bool) : Online.Schedule := fun _ =>
  if initialized then ⟨(geo initialized dfs).cfg.seed 1, [(2, 8)]⟩ else ⟨0, []⟩

theorem online_matches (initialized dfs : Bool) :
    (online dfs).unitEntries * (online dfs).unitsPerPrefix =
      (geo initialized dfs).cfg.carryPositions 1 := by
  cases initialized <;> cases dfs <;> rfl

theorem online_positive (dfs : Bool) : 0 < (online dfs).unitEntries := by
  cases dfs <;> decide +kernel

theorem schedule_valid (initialized dfs : Bool) :
    SchedulePremises (geo initialized dfs).cfg (schedule initialized dfs)
      (Adaptive.slotCount (client dfs).shape) 1 := by
  cases initialized <;> cases dfs <;> constructor
  all_goals intro j hj
  all_goals first
    | intro c hc; simp [schedule] at hc; subst c; decide +kernel
    | simp [schedule, geo, member, ConfigurationFamily.Member.geometry,
        ConfigurationFamily.Member.config, HierarchyGeometry.chunk, chunkConfig,
        Config.seed, Config.carryPositions, Config.carry, Config.levels,
        Online.pos, Online.Tiles, Online.window]

/-- The inherited overflow example has 66 exact distinct byte strings,
including the empty string, a zero byte and a 65-byte zero string. -/
example : (IdealDirectTests.overflowRecords.map Rec.key).Nodup ∧
    (IdealDirectTests.overflowRecords[0]!).key = [] ∧
    (IdealDirectTests.overflowRecords[1]!).key = [0] ∧
    (IdealDirectTests.overflowRecords[65]!).key = List.replicate 65 0 := by
  decide +kernel

/-- Give the succeeding A tier enough space to expose a range overflow after
its predecessor failed. This deliberately nonstandard geometry tests fallback,
not a small-error numerical certificate. -/
def fallbackNext : DirectJob.Geometry :=
  { IdealDirectTests.unionGeometry with aTierCapacity := 66, ranges := .dfs 0 1 66 }

def fallbackInput : DirectJob.Inputs :=
  (referenceStep (fun _ => 0) (.ofOutput emptyOutput)
    ⟨IdealDirectTests.overflowGeometry, (fun _ => 0),
      [IdealDirectTests.overflowRecords.map some]⟩).inputs []

example : fallbackInput.aRecords.length = 66 ∧ fallbackInput.bRecords = [] := by
  decide +kernel

example : levelOneA fallbackNext (fun _ => 0) fallbackInput := by
  constructor
  · decide +kernel
  · right
    refine ⟨⟨⟨.distributeA, .dfs 1 0, 1⟩, 66, 64⟩, ?_, by decide +kernel⟩
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The two-family transport includes the same nonempty overflowing
predecessor. It does not condition on its successful publication. -/
example :
    (Measure.infinitePi (fun _ : IdealDirectAProof.freshBlock (1, 1) (2, 1) =>
      IdealKey.wordLaw))
      {fresh | levelOneA fallbackNext (IdealDirectAProof.currentWords (1, 1) (2, 1) fresh)
        ((referenceStep (fun _ => 0) (.ofOutput emptyOutput)
          ⟨IdealDirectTests.overflowGeometry, IdealDirectAProof.oldWords (1, 1) (2, 1) fresh,
            [IdealDirectTests.overflowRecords.map some]⟩).inputs [])} ≤
      ((IdealDirectAProof.data (.ofOutput emptyOutput) (fun _ => 0)
          [IdealDirectTests.overflowRecords.map some] []).lawFor
        IdealDirectTests.overflowGeometry IdealDirectTests.unionSep).prob
          (fun hist word => levelOneA fallbackNext word
            ((IdealDirectAProof.data (.ofOutput emptyOutput) (fun _ => 0)
              [IdealDirectTests.overflowRecords.map some] []).directFor
                IdealDirectTests.overflowGeometry hist word)) := by
  exact IdealDirectAProof.transport (1, 1) (2, 1) (by decide +kernel)
    IdealDirectTests.overflowGeometry fallbackNext IdealDirectTests.unionSep
    (.ofOutput emptyOutput) (fun _ => 0) [IdealDirectTests.overflowRecords.map some] []
    (by exact List.Perm.refl [])

/-- With no records, both families restrict to the empty finite population. -/
example (s : SepGeom) :
    (IdealDirectAProof.data (.ofOutput emptyOutput) (fun _ => 0) [] []).ValidFor s 0 := by
  apply IdealDirectAProof.data_valid
  · exact List.Perm.refl []
  · simp [DirectMasks.records]

/-- Reusing the family forces diagonal reads even for a previously unseen
65-byte key; distinct families must not be silently identified. -/
example (family : IdealKey.Family)
    (fresh : IdealDirectAProof.freshBlock family family → Word64) :
    IdealDirectAProof.oldWords family family fresh (List.replicate 65 0) =
      IdealDirectAProof.currentWords family family fresh (List.replicate 65 0) := rfl

/-- Distinct families really have positive off-diagonal mass. A finite
cylinder avoids drawing conclusions from a single probability-zero tape. -/
example : 0 < IdealKey.tapeLaw {tape |
    tape (.inl ((1, 1), List.replicate 65 0)) = 0 ∧
      tape (.inl ((2, 1), List.replicate 65 0)) = 1} := by
  let old : IdealKey.Coord := .inl ((1, 1), List.replicate 65 0)
  let current : IdealKey.Coord := .inl ((2, 1), List.replicate 65 0)
  let coordinates : Finset IdealKey.Coord := {old, current}
  let representative : IdealKey.Tape := fun c => if c = current then 1 else 0
  have hpositive : 0 < IdealKey.tapeLaw
      (coordinates.restrict ⁻¹' {coordinates.restrict representative}) := by
    rw [← Measure.map_apply (Finset.measurable_restrict coordinates)
      (measurableSet_singleton _), (IdealKeyRestriction coordinates).2]
    exact pos_iff_ne_zero.mpr (by
      simp [uniformOn_eq_zero_iff Set.finite_univ])
  apply hpositive.trans_le
  apply measure_mono
  intro tape htape
  have ho := congrFun htape ⟨old, by simp [coordinates]⟩
  have hc := congrFun htape ⟨current, by simp [coordinates]⟩
  exact ⟨ho.trans (by simp [representative, old, current]),
    hc.trans (by simp [representative])⟩

/-- The actual early-A theorem applies to nonempty long-key runs, both
range plans and both initialized/empty starts. -/
example (initialized dfs : Bool) :
    IdealKey.tapeLaw {tape | levelOneA ((geo initialized dfs).shapes.direct 2)
      (jobWord (geo initialized dfs).cfg (IdealHierarchy.words tape) 1
        ((geo initialized dfs).cfg.seed 1 + 2))
      (IdealDirect.inputs (geo initialized dfs).cfg (geo initialized dfs).shapes
        (online dfs) (schedule initialized dfs) (client dfs)
        ((geo initialized dfs).cfg.seed 1 + 2) tape)} ≤
      ConfigurationFamily.directABound (member dfs) 2 := by
  have hd : (geo initialized dfs).cfg.digitAt 1 ((geo initialized dfs).cfg.seed 1 + 2) = 2 := by
    cases initialized <;> cases dfs <;> decide +kernel
  have bound := IdealDirectA initialized (member dfs) (member_valid dfs) 1
    (online dfs) (schedule initialized dfs) 1 (client dfs) (online_matches initialized dfs)
    (online_positive dfs) (schedule_valid initialized dfs)
    ((geo initialized dfs).cfg.seed 1 + 2)
    (by change (geo initialized dfs).cfg.seed 1 < _; omega)
    (by change 2 ≤ (geo initialized dfs).cfg.digitAt 1 _; rw [hd])
  change IdealKey.tapeLaw _ ≤ ConfigurationFamily.directABound (member dfs)
    ((geo initialized dfs).cfg.digitAt 1 ((geo initialized dfs).cfg.seed 1 + 2)) at bound
  have hd' := hd
  dsimp only [geo] at hd'
  simpa only [geo, hd'] using bound

/-- Both branches of complete direct first-failure composition instantiate
on the actual run. Membership is proved arithmetically, without enumerating
its large public potential-job inventory. -/
example (initialized dfs : Bool) (digit : Fin 2) :
    IdealKey.tapeLaw {tape |
      JobFailsFirst (geo initialized dfs).cfg (geo initialized dfs).shapes
        (IdealDirect.trace (geo initialized dfs).cfg (geo initialized dfs).shapes
          (online dfs) (schedule initialized dfs) (client dfs) tape)
        (IdealHierarchy.words tape)
        (.ordinary 1 ((geo initialized dfs).cfg.seed 1 + (digit.val + 1)))} ≤
      ConfigurationFamily.directBound (member dfs) (digit.val + 1) := by
  have hd : (geo initialized dfs).cfg.digitAt 1
      ((geo initialized dfs).cfg.seed 1 + (digit.val + 1)) = digit.val + 1 := by
    fin_cases digit <;> cases initialized <;> cases dfs <;> decide +kernel
  have hmem : JobId.ordinary 1 ((geo initialized dfs).cfg.seed 1 + (digit.val + 1)) ∈
      (geo initialized dfs).cfg.potentialJobs := by
    apply HierarchyCoveringProof.mem_ordinary.mpr
    fin_cases digit <;> cases initialized <;> cases dfs <;> decide +kernel
  have bound := IdealDirectFirstFailure initialized (member dfs) (member_valid dfs) 1
    (online dfs) (schedule initialized dfs) 1 (client dfs) (online_matches initialized dfs)
    (online_positive dfs) (schedule_valid initialized dfs)
    ((geo initialized dfs).cfg.seed 1 + (digit.val + 1)) hmem
  change IdealKey.tapeLaw _ ≤ ConfigurationFamily.directBound (member dfs)
    ((geo initialized dfs).cfg.digitAt 1
      ((geo initialized dfs).cfg.seed 1 + (digit.val + 1))) at bound
  rw [hd] at bound
  simpa only [geo] using bound

end IdealDirectATests
