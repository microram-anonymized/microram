import RebuildBound.Spec.IdealDirectFresh
import RebuildBound.Spec.IdealDirectLocal

/-! Direct level-one probability on the actual adaptive canonical tape. The
requester supplies the input populations from public widths. No universe,
encoded key range, live-capacity assumption, supplied local probability law,
or successful-execution condition occurs in these current-family bounds.
The A term and later-digit complete failure bounds remain separate. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy IdealHierarchy IdealDirect MeasureTheory
open scoped ENNReal NNReal

/-- The actual B overflow term, including arbitrary earlier reference failures. -/
def IdealDirectB_statement : Prop :=
  ∀ cfg sh g S m (a : Adaptive.AdaptiveRun m), ExposureGeometry cfg →
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg S (Adaptive.slotCount a.shape) m →
    ∀ ordinal, cfg.seed 1 < ordinal → ∀ cut,
    (sh.direct (cfg.digitAt 1 ordinal)).K ≤ 64 →
    (sh.direct (cfg.digitAt 1 ordinal)).U = cfg.carry1 →
    (sh.direct (cfg.digitAt 1 ordinal)).bCapacity < cut →
    IdealKey.tapeLaw {tape |
      (sh.direct (cfg.digitAt 1 ordinal)).bCapacity <
        DirectJob.bExcess (sh.direct (cfg.digitAt 1 ordinal))
          (jobWord cfg (words tape) 1 ordinal) (inputs cfg sh g S a ordinal tape)} ≤
      ENNReal.ofReal (Phi cut (sh.direct (cfg.digitAt 1 ordinal)).U 64 cfg.load
        (sh.direct (cfg.digitAt 1 ordinal)).bCapacity)

/-- Complete first-digit job failure, including the raw rejection branch.
Actual requester uniqueness and the empty predecessor rule exclude rejection;
the theorem does not condition on prior jobs succeeding. -/
def IdealDirectDigitOne_statement : Prop :=
  ∀ cfg sh g S m (a : Adaptive.AdaptiveRun m), ExposureGeometry cfg →
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg S (Adaptive.slotCount a.shape) m →
    ∀ ordinal, cfg.seed 1 < ordinal → cfg.digitAt 1 ordinal = 1 → ∀ cut,
    (sh.direct 1).Valid → (sh.direct 1).digit = 1 → (sh.direct 1).K ≤ 64 →
    (sh.direct 1).U = cfg.carry1 → (sh.direct 1).bCapacity < cut →
    IdealKey.tapeLaw {tape |
      jobFails cfg sh (trace cfg sh g S a tape) (words tape) (.ordinary 1 ordinal) = true} ≤
      ENNReal.ofReal (Phi cut (sh.direct 1).U 64 cfg.load (sh.direct 1).bCapacity)

/-- The actual union overflow term at later digits. Chronological reference
populations supply the local shape and counts; the current-home rounding
density remains in the analytic budget. This supplies no old-home A law. -/
def IdealDirectUnion_statement : Prop :=
  ∀ cfg sh g S m (a : Adaptive.AdaptiveRun m), ExposureGeometry cfg →
    2 ≤ cfg.levels → 0 < cfg.fanout 1 → cfg.seed 1 % cfg.fanout 1 = 0 →
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg S (Adaptive.slotCount a.shape) m →
    ∀ ordinal, cfg.seed 1 < ordinal → 2 ≤ cfg.digitAt 1 ordinal →
    ∀ (s : SepGeom) cut,
    ReferenceInputCompatible (sh.direct (cfg.digitAt 1 ordinal - 1)) s →
    s.Valid → s.k < 64 → s.d = cfg.digitAt 1 ordinal → s.U = cfg.carry1 →
    (sh.direct (cfg.digitAt 1 ordinal)).outputHomes = s.N →
    (∀ word, (sh.direct (cfg.digitAt 1 ordinal)).home word = s.homeOf word) →
    (sh.direct (cfg.digitAt 1 ordinal)).outputCapacity < cut →
    IdealKey.tapeLaw {tape |
      (sh.direct (cfg.digitAt 1 ordinal)).outputCapacity <
        (inputs cfg sh g S a ordinal tape).excess (sh.direct (cfg.digitAt 1 ordinal))
          (jobWord cfg (words tape) 1 ordinal)} ≤
      ENNReal.ofReal (s.curDensity 64 (cfg.load * s.N) *
        Phi cut (sh.direct (cfg.digitAt 1 ordinal)).outputHomes 64 cfg.load
          (sh.direct (cfg.digitAt 1 ordinal)).outputCapacity)

end RebuildBound.Spec
