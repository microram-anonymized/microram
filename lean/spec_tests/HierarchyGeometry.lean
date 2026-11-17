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
import RebuildBound.Oracle.HierarchyDiff

/-! Structural pilots for explicit direct geometry. These instantiate the same
induction at two levels (r0=2/4), a different depth (r0=8), and the
31 control, from both starts. Lookup requires initialization records to
agree with the selected start; freshness and exact laws use existing premises.
No capacity probability is asserted. -/

open RebuildBound RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Spec
open RebuildBound.HierarchyInvariantProof

namespace HierarchyGeometryTest

/-- One-page pilot shapes; not a new general native shape constructor. -/
def direct (K d : Nat) : DirectJob.Geometry :=
  let base : DirectJob.Geometry :=
    ⟨K, d, d * 2 ^ K, 64, if d = 1 then 0 else 64, 64, 64, 64, 64, .direct⟩
  if base.outputHomes ≤ 8 ∨ base.poolCapacity = 0 then base else
    let bits := routedRangeBits (ceilLog2 base.outputHomes) (base.poolCapacity / 64)
    { base with ranges := .dfs (ceilLog2 base.outputHomes - bits) bits base.poolCapacity }

def pilot (K : Nat) (fanouts : List Nat) (initialized : Bool := true) : HierarchyGeometry :=
  let cfg : Config := ⟨fanouts, 2 ^ K, 8, 32, 2 ^ 32, initialized⟩
  let k := (cfg.carry cfg.levels).log2
  let top : TopGeom := ⟨64, k, 3, 3, k, true, 1, 1, 1, 1⟩
  let bits := routedRangeBits (k + 3) (k + 3)
  let prep : TPGeom := ⟨64, k + 3, 1, 1, 1, bits, k + 3 - bits, true⟩
  ⟨cfg, separatedRows cfg (fun _ => 1) (fun _ => 1), top, prep, prep,
    32 * top.T, direct K⟩

def two2 := pilot 2 [2]
def two4 := pilot 3 [2]
def deep8 := pilot 4 [2, 8]

example : two2.cfg.levels = 2 ∧ two2.rows = [] ∧ two2.keyCapacity = 2 ^ 11 := by decide
example : two4.cfg.levels = 2 ∧ two4.rows = [] ∧ two4.keyCapacity = 2 ^ 12 := by decide
example : deep8.cfg.levels = 3 ∧ deep8.keyCapacity = 2 ^ 16 := by decide
example : (two2.direct 2).ranges = .direct ∧ 0 < (two2.direct 2).poolCapacity := by decide

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The same finite checks cover both starts, including the existing 31 control. -/
def pilots (initialized : Bool) : List HierarchyGeometry :=
  [pilot 2 [2] initialized, pilot 3 [2] initialized, pilot 4 [2, 8] initialized,
    { geometry31 with cfg := { config31 with initialized := initialized } }]

theorem pilots_low (initialized : Bool) : ∀ g ∈ pilots initialized, LowFacts g.cfg g.rows g.direct := by
  cases initialized <;> intro g hg <;>
    simp only [pilots, List.mem_cons, List.not_mem_nil, or_false] at hg <;>
    rcases hg with rfl | rfl | rfl | rfl <;>
    exact lowFacts_of _ _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem pilots_top (initialized : Bool) : ∀ g ∈ pilots initialized, g.TopCompatible := by
  cases initialized <;> intro g hg <;>
    simp only [pilots, List.mem_cons, List.not_mem_nil, or_false] at hg <;>
    rcases hg with rfl | rfl | rfl | rfl <;> decide +kernel

theorem pilots_digit (initialized : Bool) : ∀ g ∈ pilots initialized, g.cfg.topDigit = g.top.D := by
  cases initialized <;> intro g hg <;>
    simp only [pilots, List.mem_cons, List.not_mem_nil, or_false] at hg <;>
    rcases hg with rfl | rfl | rfl | rfl <;> rfl

/-- The full structural induction is shared across shapes and starts. -/
example (initialized : Bool) : ∀ g ∈ pilots initialized, HierarchyInvariantFor g := by
  intro g hg N tr hN hT hU words
  exact contractsFor g (pilots_low initialized g hg)
    (TopFacts.of_compatible (pilots_top initialized g hg)) hN hT hU words

/-- The existing initialized scalar/batch statement interfaces remain usable. -/
example : ∀ g ∈ pilots true, OnlineCorrectnessFor g ∧ BatchCorrectnessFor g := by
  intro g hg
  have h : 0 < g.cfg.seed g.cfg.levels := by
    simp only [pilots, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> decide
  exact ⟨OnlineCorrectnessProof.correctnessFor g (pilots_low true g hg)
      (TopFacts.of_compatible (pilots_top true g hg)) (pilots_digit true g hg) h,
    BatchCorrectnessProof.correctnessFor g (pilots_low true g hg)
      (TopFacts.of_compatible (pilots_top true g hg)) (pilots_digit true g hg) h⟩

/-- Scalar lookup from either start, with an explicit consistent initial history. -/
example (initialized : Bool) (g : HierarchyGeometry) (hg : g ∈ pilots initialized)
    (N : Nat) (online : Model.Online.OnlineGeom) (run : Model.Online.OnlineRun)
    (S : Model.Online.Schedule) (n m : Nat) (hsetting : OnlineSettingFor g N online run S n m)
    (hInit : g.cfg.initialized = false → run.init = [])
    (words : Words) (dummy : Nat → Nat → Nat) (j : Nat) (o : Model.Online.Op)
    (hj : j < n) (ho : run.ops[j]? = some o) (hp : o.probes = true) :
    let result := Model.Probe.scalar g.cfg g.shapes online run S words dummy j
    Model.Probe.decode result.found =
        Model.Probe.latestValue o.record.key (run.init ++ (run.ops.take j).map Model.Online.Op.record) ∧
      ∀ i, result.addresses.getD i 0 = Model.Online.touched g.cfg g.shapes online run S words dummy j i :=
  OnlineCorrectnessProof.correctnessFor_run g (pilots_low initialized g hg)
    (TopFacts.of_compatible (pilots_top initialized g hg)) (pilots_digit initialized g hg)
    N online run S n m hsetting hInit words dummy j o hj ho hp

/-- The same history base case serves batch lookup, including earlier chunk lanes. -/
example (initialized : Bool) (g : HierarchyGeometry) (hg : g ∈ pilots initialized)
    (N : Nat) (online : Model.Online.OnlineGeom) (run : Model.OnlineBatch.BatchRun)
    (S : Model.Online.Schedule) (n m : Nat) (hsetting : BatchSettingFor g N online run S n m)
    (hInit : g.cfg.initialized = false → run.init = [])
    (words : Words) (dummy : Nat → Nat → Nat) (t : Nat) (slot : Model.OnlineBatch.Slot)
    (ht : t < n) (hs : (Model.OnlineBatch.slots run)[t]? = some slot) (hp : slot.probes = true) :
    let result := Model.Probe.batch g.cfg g.shapes online run S words dummy t
    Model.Probe.decode result.found = Model.Probe.latestValue slot.record.key
        (run.init ++ ((Model.OnlineBatch.slots run).take t).map Model.OnlineBatch.Slot.record) ∧
      ∀ i, result.addresses.getD i 0 = Model.OnlineBatch.touched g.cfg g.shapes online run S words dummy t i :=
  BatchCorrectnessProof.correctnessFor_run g (pilots_low initialized g hg)
    (TopFacts.of_compatible (pilots_top initialized g hg)) (pilots_digit initialized g hg)
    N online run S n m hsetting hInit words dummy t slot ht hs hp

/-- Empty windows still have fresh family words: oneTop rules out duplicate tops. -/
example (initialized : Bool) : ∀ g ∈ pilots initialized, OnlineFreshFor g ∧ BatchFreshFor g := by
  intro g hg
  exact ⟨OnlineFreshProof.freshFor g (pilots_low initialized g hg),
    BatchFreshProof.freshFor g (pilots_low initialized g hg)⟩

/-- Fixed-run exact privacy uses no numerical capacity certificates. -/
example (initialized : Bool) : ∀ g ∈ pilots initialized, OnlineExactFor g ∧ BatchExactFor g := by
  intro g hg
  have F := pilots_low initialized g hg
  exact ⟨OnlineExactProof.exactFor_of g (OnlinePatternProof.patternFor g F) (OnlineFreshProof.freshFor g F),
    BatchExactProof.exactFor_of g (BatchPatternProof.patternFor g F) (BatchFreshProof.freshFor g F)⟩

/-- Non-vacuous schedule witnesses, at arbitrary run lengths and both starts. -/
example (initialized : Bool) (n : Nat) : ∀ g ∈ pilots initialized,
    SchedulePremises g.cfg (Model.Online.syncSchedule g.cfg) n g.cfg.levels := by
  cases initialized <;> intro g hg <;>
    simp only [pilots, List.mem_cons, List.not_mem_nil, or_false] at hg <;>
    rcases hg with rfl | rfl | rfl | rfl <;>
    exact SyncScheduleLemmas.syncSchedule_premises _ (by decide) (by decide) n

/-- The first-failure producer contract covers the same shapes and both starts. -/
theorem pilots_covering (initialized : Bool) : ∀ g ∈ pilots initialized,
    HierarchyCoveringProof.FactsFor g.cfg g.rows g.top g.prep g.init g.direct := by
  cases initialized <;> intro g hg <;>
    simp only [pilots, List.mem_cons, List.not_mem_nil, or_false] at hg <;>
    rcases hg with rfl | rfl | rfl | rfl <;> constructor <;> decide +kernel

example (initialized : Bool) : ∀ g ∈ pilots initialized, ∀ tr words,
    Fails g.cfg g.shapes tr words → ∃ j ∈ g.cfg.potentialJobs, WithinHorizon g.cfg j ∧
      jobTiersFit g.cfg g.shapes tr words j ∧ jobFails g.cfg g.shapes tr words j = true := by
  intro g hg tr words hfail
  exact HierarchyCoveringProof.firstFailureFor g (pilots_covering initialized g hg)
    SepTierFit TopTierFit TPTierFit tr words hfail

example : ¬ HierarchyCoveringProof.FactsFor two2.cfg two2.rows two2.top two2.prep two2.init
    (fun d => { two2.direct d with outputCapacity := 128 }) := by
  intro F
  have h := F.topB
  change 128 ≤ 64 at h
  omega

/-- Chunk arithmetic and initialization membership work for both starts. -/
theorem pilots_chunks (initialized : Bool) : ∀ g ∈ pilots initialized,
    HierarchyChunkArith.ChunkFacts g.cfg := by
  cases initialized <;> intro g hg <;>
    simp only [pilots, List.mem_cons, List.not_mem_nil, or_false] at hg <;>
    rcases hg with rfl | rfl | rfl | rfl <;> constructor <;> decide +kernel

example (initialized : Bool) (g : HierarchyGeometry) (hg : g ∈ pilots initialized)
    (k : Nat) (j : JobId) (hj : j ∈ g.cfg.potentialJobs) :
    HierarchyChunkAssemblyProof.shift g.cfg k j ∈ (chunkConfig g.cfg (k + 1)).potentialJobs :=
  HierarchyChunkAssemblyProof.shift_mem (pilots_chunks initialized g hg) hj

-- Wrong carry width, digit, output width, routing or capacity must be rejected.
example : ¬ HierarchyGeometry.DirectCompatible two2.cfg selectedDirectGeometry := by decide
example : ¬ HierarchyGeometry.DirectCompatible two2.cfg
    (fun d => { two2.direct d with digit := 1 }) := by decide
example : ¬ HierarchyGeometry.DirectCompatible two2.cfg
    (fun d => { two2.direct d with outputHomes := 16 }) := by decide
example : ¬ HierarchyGeometry.DirectCompatible two4.cfg
    (fun d => { two4.direct d with ranges := .direct }) := by decide
example : ¬ HierarchyGeometry.DirectCompatible two2.cfg
    (fun d => { two2.direct d with copyCapacity := 32 }) := by decide

-- Two levels require no separated row. A deeper missing row has no capacity.
example : two2.incomingTopCapacity = some 64 := by decide
example : ({ deep8 with rows := [] } : HierarchyGeometry).incomingTopCapacity = none := by decide
example : ¬ ({ deep8 with rows := [] } : HierarchyGeometry).TopCompatible := by decide
example : ¬ ({ two2 with top := { two2.top with bPages := 0 } } :
    HierarchyGeometry).TopCompatible := by decide
example : ¬ ({ two2 with direct := fun d => { two2.direct d with outputCapacity := 128 } } :
    HierarchyGeometry).TopCompatible := by decide

-- Legacy and 31 execution and failure definitions are unchanged, symbolically.
example (cfg : Config) (rows : List (SepGeom × Nat)) :
    (HierarchyGeometry.selected cfg rows).shapes = hierarchyShapes cfg rows := rfl
example : geometry31.shapes =
    hierarchyShapesWith config31 separated31 top31 prep31 init31 := rfl
example (tr : Trace) (words : Words) (ℓ v : Nat) :
    table config31 geometry31.shapes tr words ℓ v =
      table config31 (hierarchyShapesWith config31 separated31 top31 prep31 init31) tr words ℓ v := rfl
example (tr : Trace) (words : Words) :
    Fails config31 geometry31.shapes tr words =
      Fails config31 (hierarchyShapesWith config31 separated31 top31 prep31 init31) tr words := rfl

/-- Compare the two-level pilots against an existing native replay fixture.
The initialized flag and horizon belong to the replay, not the shape check. -/
def checkNative (j : Lean.Json) : Except String Unit := do
  let cfg ← RebuildBound.Oracle.objField j "fixture" "config"
  let (native, _, _, _, _) ← RebuildBound.Oracle.HierarchyDiff.parseConfig cfg
  let g ← match native.carry1 with
    | 4 => pure two2
    | 8 => pure two4
    | _ => throw "not a two-level pilot carry"
  unless { native with horizon := g.cfg.horizon, initialized := g.cfg.initialized } == g.cfg do
    throw "configuration"
  let sh ← RebuildBound.Oracle.objField j "fixture" "shapes"
  let ds ← (← RebuildBound.Oracle.arrField sh "shapes" "direct").toList.mapM
    RebuildBound.Oracle.DirectJob.parseGeometry
  unless ds == [g.direct 1, g.direct 2] do throw "direct shapes"
  let sep ← (← RebuildBound.Oracle.arrField sh "shapes" "sep").toList.mapM
    RebuildBound.Oracle.HierarchyDiff.parseSep
  unless sep == [] do throw "separated rows"
  unless (← RebuildBound.Oracle.HierarchyDiff.parseTop
      (← RebuildBound.Oracle.objField sh "shapes" "top")) == g.top do throw "top shape"
  for (name, expected) in [("prep", g.prep), ("init", g.init)] do
    unless (← RebuildBound.Oracle.HierarchyDiff.parsePrep
        (← RebuildBound.Oracle.objField sh "shapes" name)) == expected do throw s!"{name} shape"

end HierarchyGeometryTest

def main (paths : List String) : IO UInt32 := do
  if paths.isEmpty then
    IO.eprintln "expected native two-level replay fixture paths"
    return 2
  for path in paths do
    let raw ← IO.FS.readFile path
    match Lean.Json.parse raw >>= HierarchyGeometryTest.checkNative with
    | .error e => IO.eprintln s!"FAIL: {path}: {e}"; return 1
    | .ok _ => pure ()
  IO.println s!"PASS: {paths.length} native two-level configuration/shape fixtures"
  return 0
