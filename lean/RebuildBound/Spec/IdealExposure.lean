import RebuildBound.Spec.IdealHierarchy
import RebuildBound.Spec.Model.Adaptive
import RebuildBound.Spec.HierarchyStructure

/-! Actual adaptive hierarchy exposure on the canonical product tape. These
contracts concern input chronology, including reference overflow continuations;
they do not assume a finite key universe or a successful execution. -/
namespace RebuildBound.Spec.IdealHierarchy
open Model Model.Hierarchy

/-- The public time arithmetic used to place a family after its input prefix. -/
structure ExposureGeometry (cfg : Config) : Prop where
  seed : ∀ level, 1 ≤ level → level < cfg.levels →
    cfg.seed level = cfg.fanout level * cfg.seed (level + 1)
  product : ∀ level, 1 ≤ level → level < cfg.levels →
    time cfg (level + 1) 1 = time cfg level 1 * cfg.fanout level
  positive : ∀ level, 1 ≤ level → level ≤ cfg.levels → 0 < time cfg level 1

/-- Holding dummy words and all strictly earlier families fixed holds the
completed input units fixed through the cutoff. The cutoff family itself may
change at every key, including keys not previously requested. -/
def ExposureCausal (cfg : Config) (trace : IdealKey.Tape → Trace) : Prop :=
  (∀ x y, (trace x).init = (trace y).init ∧ (trace x).unsh = (trace y).unsh) ∧
  ∀ (cutoff : Nat) (x y : IdealKey.Tape),
    (∀ family key, time cfg family.1 family.2 < cutoff →
      x (.inl (family, key)) = y (.inl (family, key))) →
    (∀ slot entry, x (.inr (slot, entry)) = y (.inr (slot, entry))) →
    ∀ i, cfg.seed 1 + i + 1 ≤ cutoff → (trace x).units i = (trace y).units i

end RebuildBound.Spec.IdealHierarchy

namespace RebuildBound.Spec
open Model Model.Hierarchy IdealHierarchy

/-- Existing structural geometries discharge the public time arithmetic. -/
def IdealExposureGeometry_statement : Prop :=
  ∀ geo : HierarchyGeometry, geo.Structural → ExposureGeometry geo.cfg

/-- The actual interaction has exposure causality for arbitrary adaptive
clients, with no capacity, flag, key-range or real-probe-pattern hypothesis. -/
def IdealAdaptiveExposure_statement : Prop :=
  ∀ cfg sh g S m (a : Adaptive.AdaptiveRun m), ExposureGeometry cfg →
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg S (Adaptive.slotCount a.shape) m →
    ExposureCausal cfg (fun tape => OnlineBatch.traceOf g
      (Adaptive.realized cfg sh g S a (words tape) (dummy tape)))

/-- Resampling a whole routing family cannot change the realized input prefix
through that family's time. Agreement is on its complete outside environment,
not merely on previously encountered keys. -/
def IdealAdaptiveFamilyFresh_statement : Prop :=
  ∀ cfg sh g S m (a : Adaptive.AdaptiveRun m), ExposureGeometry cfg →
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg S (Adaptive.slotCount a.shape) m →
    ∀ (family : IdealKey.Family) (x y : IdealKey.Tape),
    (∀ coordinate, coordinate ∉ familyBlock family → x coordinate = y coordinate) →
    ∀ i, cfg.seed 1 + i + 1 ≤ time cfg family.1 family.2 →
      (OnlineBatch.traceOf g (Adaptive.realized cfg sh g S a (words x) (dummy x))).units i =
        (OnlineBatch.traceOf g (Adaptive.realized cfg sh g S a (words y) (dummy y))).units i

end RebuildBound.Spec
