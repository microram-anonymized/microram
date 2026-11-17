import RebuildBound.Spec.IdealDirect
import RebuildBound.Spec.HierarchyChunkBase
import RebuildBound.Spec.IdealProbe
import RebuildBound.Spec.ApiSeed
import RebuildBound.Spec.G3
import RebuildBound.Spec.HierarchyStructure
import RebuildBound.Spec.DirectJobARoute
import RebuildBound.Spec.DirectJobCycleBounds
import RebuildBound.Spec.DirectJobHistoryGeometry

namespace RebuildBound.Spec.IdealGeometry
open Model Model.DirectJob Model.Hierarchy
open scoped ENNReal

/-- Finite arithmetic checks for an arbitrary direct probability shape. -/
def DirectFacts (geo : HierarchyGeometry) (sep : Nat → SepGeom) (d : Nat) : Prop :=
  let g := geo.direct d
  let s := sep d
  g.Valid ∧ g.digit = d ∧ g.K ≤ 64 ∧ g.U = geo.cfg.carry1 ∧
    g.bCapacity < 256 ∧ g.outputCapacity < 256 ∧
    (2 ≤ d →
      ReferenceInputCompatible (geo.direct (d - 1)) s ∧ s.Valid ∧ s.d = d ∧
      s.U = geo.cfg.carry1 ∧ s.k < 64 ∧ s.K + val2 (s.d - 1) ≤ 64 ∧
      0 < (s.d - 1) / 2 ^ val2 (s.d - 1) ∧ s.C = 64 ∧
      s.stashPages * s.C < 256 ∧ g.outputHomes = s.N ∧
      s.K = g.K ∧ s.e = val2 g.digit ∧ s.r = g.digit / 2 ^ val2 g.digit ∧
      g.routeCapacity = s.stashPages * s.C ∧ g.radixCapacity = s.stashPages * s.C ∧
      (g.ranges ≠ .direct → g.aTierCapacity = s.aTierPages * s.C ∧
        g.ranges = .dfs s.I s.rangeBits (s.poolPages * s.C) ∧ s.I < s.K))

/-- Applicability uses the actual direct cycle and local probability rows,
without a family membership or supplied probability premise. -/
def DirectAnalytic (geo : HierarchyGeometry) (sep : Nat → SepGeom) : Prop :=
  DirectCycleGeometry geo.direct (geo.cfg.fanout 1) ∧
    ∀ d, 1 ≤ d → d ≤ geo.cfg.fanout 1 → DirectFacts geo sep d

noncomputable def directABound (geo : HierarchyGeometry) (sep : Nat → SepGeom)
    (d : Nat) : ℝ≥0∞ :=
  if (geo.direct d).ranges = .direct then selRest (sep d) else selSepBound (sep d)

noncomputable def directBBound (geo : HierarchyGeometry) (d : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal (Phi 256 (geo.direct d).U 64 32 (geo.direct d).bCapacity)

noncomputable def directUBound (geo : HierarchyGeometry) (sep : Nat → SepGeom)
    (d : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal ((sep d).curDensity 64 (32 * (sep d).N) *
    Phi 256 (geo.direct d).outputHomes 64 32 (geo.direct d).outputCapacity)

noncomputable def directBound (geo : HierarchyGeometry) (sep : Nat → SepGeom)
    (d : Nat) : ℝ≥0∞ :=
  if d = 1 then directBBound geo d
  else directBBound geo d + directABound geo sep d + directUBound geo sep d


/-- Word-width and cutoff checks for a separated row. -/
def SepAnalytic (row : SepGeom) : Prop :=
  row.k < 64 ∧ row.K + val2 (row.d - 1) ≤ 64 ∧
    0 < (row.d - 1) / 2 ^ val2 (row.d - 1) ∧
    row.I < row.K ∧ row.stashPages * row.C < 256

/-- Analytic parameters do not depend on the requests, keys or random tape.
Lower jobs use the existing cutoff 256; top cutoffs are explicit. -/
structure Parameters where
  directSep : Nat → SepGeom
  initK1 : Nat
  initK2 : Nat
  prepK1 : Nat
  prepK2 : Nat
  finishK1 : Nat
  finishK2 : Nat

/-- Applicability consists solely of geometry and arithmetic conditions.
In particular, it contains no population or probability assumption. -/
structure Analytic (geo : HierarchyGeometry) (p : Parameters) : Prop where
  direct : DirectAnalytic geo p.directSep
  separated : ∀ level < geo.cfg.levels, 2 ≤ level →
    ∀ d < geo.cfg.fanout level + 1, 2 ≤ d → ∀ row,
      geo.cfg.sepRow geo.rows level d = some row → SepAnalytic row
  initWidth : geo.init.k ≤ 64
  initDfs : geo.init.dfs = true → geo.init.I + 1 < geo.init.k
  initRoute : geo.init.stashPages * geo.init.C < p.initK1
  initDrain : geo.init.drainPages * geo.init.C < p.initK2
  prepWidth : geo.prep.k ≤ 64
  prepDfs : geo.prep.dfs = true → geo.prep.I + 1 < geo.prep.k
  prepRoute : geo.prep.stashPages * geo.prep.C < p.prepK1
  prepDrain : geo.prep.drainPages * geo.prep.C < p.prepK2
  finishWidth : geo.top.k + geo.top.e ≤ 64
  finishRoute : geo.top.C < p.finishK1
  finishDrain : min geo.top.SMerge geo.top.STier < p.finishK2

/-- Product of fanouts below a level; independent of the execution horizon. -/
def period (cfg : Config) (level : Nat) : Nat :=
  (cfg.fanouts.take (level - 1)).foldr (· * ·) 1

/-- Finite arithmetic and tier links used by least-first-failure coverage.
The level bound belongs to the existing serialized job ordering. -/
structure Coverage (geo : HierarchyGeometry) : Prop where
  levels_ge : 2 ≤ geo.cfg.levels
  levels_le : geo.cfg.levels ≤ 14
  fanout_ge : ∀ level < geo.cfg.levels, 1 ≤ level → 2 ≤ geo.cfg.fanout level
  seed_dvd : geo.cfg.seed 1 % geo.cfg.fanout 1 = 0
  seed_succ : ∀ level < geo.cfg.levels, 1 ≤ level →
    geo.cfg.seed level = geo.cfg.seed (level + 1) * geo.cfg.fanout level
  per_one : period geo.cfg 1 = 1
  per_succ : ∀ level < geo.cfg.levels, 1 ≤ level →
    period geo.cfg (level + 1) = period geo.cfg level * geo.cfg.fanout level
  per_pos : ∀ level < geo.cfg.levels + 1, 0 < period geo.cfg level
  horizon : ∀ level < geo.cfg.levels, 1 ≤ level →
    (geo.cfg.seed 1 + geo.cfg.ordinals 1) / period geo.cfg level ≤
      geo.cfg.seed level + geo.cfg.ordinals level
  rowA : ∀ level < geo.cfg.levels, 2 ≤ level →
    ∀ d < geo.cfg.fanout level + 1, 3 ≤ d →
      (geo.shapes.sep level (d - 1)).tierPages * (geo.shapes.sep level (d - 1)).C ≤
        (geo.shapes.sep level d).aTierPages * (geo.shapes.sep level d).C
  rowCarry : ∀ level < geo.cfg.levels, 3 ≤ level →
    (geo.shapes.sep (level - 1) (geo.cfg.fanout (level - 1))).tierPages *
        (geo.shapes.sep (level - 1) (geo.cfg.fanout (level - 1))).C ≤
      (geo.shapes.sep level 2).aTierPages * (geo.shapes.sep level 2).C
  rowOne : 2 < geo.cfg.levels → (geo.direct (geo.cfg.fanout 1)).outputCapacity ≤
    (geo.shapes.sep 2 2).aTierPages * (geo.shapes.sep 2 2).C
  topB : (if geo.cfg.levels = 2 then (geo.direct (geo.cfg.fanout 1)).outputCapacity else
    (geo.shapes.sep (geo.cfg.levels - 1) (geo.cfg.fanout (geo.cfg.levels - 1))).tierPages *
      (geo.shapes.sep (geo.cfg.levels - 1) (geo.cfg.fanout (geo.cfg.levels - 1))).C) ≤ geo.top.SB
  initPrep : geo.init.drainPages * geo.init.C ≤ geo.prep.aTierPages * geo.prep.C
  topPrep : geo.top.STier ≤ geo.prep.aTierPages * geo.prep.C
  prepTop : geo.prep.drainPages * geo.prep.C ≤ geo.top.SR

/-- Optional arithmetic for reusing one window's exposure budget at any
positive number of windows. It asserts no numerical error target. -/
structure WindowArithmetic (cfg : Config) : Prop where
  horizon : cfg.horizon = 2 ^ 32
  levels_ge : 2 ≤ cfg.levels
  dvd : ∀ level < cfg.levels + 1, 1 ≤ level → cfg.carryPositions level ∣ 2 ^ 32
  seed_succ : ∀ level < cfg.levels, 1 ≤ level →
    cfg.seed level = cfg.fanout level * cfg.seed (level + 1)
  scale : ∀ level < cfg.levels, 1 ≤ level →
    cfg.ordinals level - 1 = cfg.fanout level * (cfg.ordinals (level + 1) - 1)
  seed : ∀ level < cfg.levels + 1, 1 ≤ level →
    cfg.seed level * period cfg level = cfg.seed 1
  ords : ∀ level < cfg.levels + 1, 1 ≤ level →
    cfg.ordinals 1 - 1 = (cfg.ordinals level - 1) * period cfg level
  per_pos : ∀ level < cfg.levels + 1, 1 ≤ level → 1 ≤ period cfg level
  per_top : 2 ≤ period cfg cfg.levels
  fanout_pos : 0 < cfg.fanout 1

/-- Analytic budgets for the actual shapes. Missing separated rows retain
budget one; structural applicability establishes required rows exist. -/
noncomputable def classBudget (geo : HierarchyGeometry) (p : Parameters) : JobClass → ℝ≥0∞
  | .ordinary level d => if level = 1 then directBound geo p.directSep d else
      if d = 1 then 0 else ((geo.cfg.sepRow geo.rows level d).map selSepBound).getD 1
  | .topFinish => ENNReal.ofReal (topFinishBound geo.top.C geo.top.SR geo.top.rho geo.top.I
      geo.top.T (min geo.top.SMerge geo.top.STier) p.finishK1 p.finishK2 32)
  | .topPrepare => tpBound geo.prep 32 1 p.prepK1 p.prepK2
  | .initialization => tpBound geo.init 32 1 p.initK1 p.initK2

end RebuildBound.Spec.IdealGeometry

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online IdealHierarchy IdealDirect MeasureTheory
open scoped ENNReal

/-- Arbitrary valid geometry at its declared horizon. The supplied error
certificate is arithmetic; all actual job probabilities and populations are derived. -/
def IdealGeometryCapacity_statement : Prop :=
  ∀ (geo : HierarchyGeometry) (p : IdealGeometry.Parameters),
    geo.Structural → geo.cfg.Valid → IdealGeometry.Coverage geo →
    IdealGeometry.Analytic geo p → ∀ error : ℝ≥0∞,
    geo.cfg.exposureSum (IdealGeometry.classBudget geo p) ≤ error →
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
      (trace geo.cfg geo.shapes g S a tape) (words tape)} ≤ error

/-- A base window's analytic exposure certificate scales to h windows of
2^32 accesses. Geometry validity alone implies no particular error target. -/
def IdealGeometryWindows_statement : Prop :=
  ∀ (base : HierarchyGeometry) (p : IdealGeometry.Parameters),
    base.Structural → base.cfg.Valid → IdealGeometry.Coverage base →
    IdealGeometry.Analytic base p → IdealGeometry.WindowArithmetic base.cfg →
    ∀ error : ℝ≥0∞, base.cfg.exposureSum (IdealGeometry.classBudget base p) ≤ error →
    ∀ h, 1 ≤ h → let geo := base.chunk h
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
      (trace geo.cfg geo.shapes g S a tape) (words tape)} ≤ (h : ℝ≥0∞) * error

/-- Correctness, exact reference simulation and the explicit analytic capacity
budget concern one actual request-derived run on the canonical tape. -/
def IdealGeometryApi_statement : Prop :=
  ∀ (geo : HierarchyGeometry) (p : IdealGeometry.Parameters),
    geo.Structural → geo.cfg.Valid → IdealGeometry.Coverage geo →
    IdealGeometry.Analytic geo p → ∀ error : ℝ≥0∞,
    geo.cfg.exposureSum (IdealGeometry.classBudget geo p) ≤ error →
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
    let observe := fun tape => Adaptive.transcript geo.cfg geo.shapes g S a n
      (words tape) (dummy tape)
    (∀ tape, let qs := (ApiAdaptive.requestGroups compiled
        (Adaptive.rowsOf (observe tape) n) fs).flatMap PublicApi.Group.lanes
      ApiRunCorrect geo c g (Adaptive.realized geo.cfg geo.shapes g S a
        (words tape) (dummy tape)) S qs) ∧
    Measurable observe ∧
    IdealKey.tapeLaw.map observe =
      simLaw geo.cfg (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape fs)) S)
        (Adaptive.shapePattern (ApiAdaptive.shape fs)) n m ∧
    IdealKey.tapeLaw {tape | Fails geo.cfg geo.shapes
      (trace geo.cfg geo.shapes g S a tape) (words tape)} ≤
      error

/-- Independent countable private seeds may have unbounded support and
seed-dependent initialization, under one public geometry and analytic certificate. -/
def IdealGeometrySeedCapacity_statement : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] [Countable Seed] [MeasurableSingletonClass Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (geo : HierarchyGeometry) (p : IdealGeometry.Parameters),
    geo.Structural → geo.cfg.Valid → IdealGeometry.Coverage geo →
    IdealGeometry.Analytic geo p → ∀ error : ℝ≥0∞,
    geo.cfg.exposureSum (IdealGeometry.classBudget geo p) ≤ error →
    ∀ (c : Api.Codec) g S (init : Seed → List Rec) m width batches,
    let fs := ApiAdaptive.frames width g.unitEntries batches
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    ∀ choose : Seed → ApiLegal.Chooser geo.cfg (ApiAdaptive.shape fs) S m,
    (∀ seed, ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized (init seed)) →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    (∀ seed (t : ApiLegal.Prefix geo.cfg (ApiAdaptive.shape fs) S m n),
      ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c (init seed)) ((init seed).map Rec.key)
        ((ApiAdaptive.requestGroups (ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S (choose seed))
          (Adaptive.rowsOf (ApiLegal.erase t) n) fs).flatMap PublicApi.Group.lanes)) →
    (μ.prod IdealKey.tapeLaw)
      (ApiSeed.failure c geo.cfg geo.shapes g S init m width batches choose) ≤
        error

/-- Explicit off-failure observation agreement transfers the generic error
bound without conditioning the canonical experiment on success. -/
def IdealGeometryOblivious_statement : Prop :=
  ∀ (geo : HierarchyGeometry) (p : IdealGeometry.Parameters),
    geo.Structural → geo.cfg.Valid → IdealGeometry.Coverage geo →
    IdealGeometry.Analytic geo p → ∀ error : ℝ≥0∞,
    geo.cfg.exposureSum (IdealGeometry.classBudget geo p) ≤ error →
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
    let reference := fun tape => Adaptive.transcript geo.cfg geo.shapes g S a n
      (words tape) (dummy tape)
    let simulator := simLaw geo.cfg
      (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape fs)) S)
      (Adaptive.shapePattern (ApiAdaptive.shape fs)) n m
    ∀ (Value : Type) [MeasurableSpace Value]
      (observed : IdealKey.Tape → Value) (encode : (Fin n → Fin m → Nat) → Value),
    Measurable observed → Measurable encode →
    (∀ tape, ¬ Fails geo.cfg geo.shapes (trace geo.cfg geo.shapes g S a tape) (words tape) →
      observed tape = encode (reference tape)) →
    ∀ event : Set Value, MeasurableSet event →
    IdealKey.tapeLaw (observed ⁻¹' event) ≤ simulator.map encode event +
        error ∧
      simulator.map encode event ≤ IdealKey.tapeLaw (observed ⁻¹' event) +
        error

end RebuildBound.Spec
