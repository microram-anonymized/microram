import RebuildBound.Spec.NativeMatch.Production
import RebuildBound.Spec.HierarchyStructure

/-! First local-routing support interfaces. Complete native messages retain the
family fields, and a successfully filled physical probe plan exposes each
family only inside a bounded interval. These statements do not construct a
sparse reader or certify its family populations or pair count. In particular,
capacity diagnostics over the certificate horizon are not native reads here. -/
namespace RebuildBound.Spec.NativeRoutingFamilySupport
open Model Model.Hierarchy

/-- A geometry-only upper bound for every non-top window's width. It contains
no horizon, access count, key identity, or routing outcome. -/
def NonTopWidth (cfg : Config) (width : Nat) : Prop :=
  ∀ level, 1 ≤ level → level < cfg.levels →
    cfg.fanout level * cfg.carryPositions level ≤ width

/-- The common window end of coordinates forwarded to the terminal family. -/
def familyEnd (cfg : Config) (level ordinal : Nat) : Nat :=
  let family := familyOf cfg level ordinal
  family.2 * cfg.carryPositions family.1

end RebuildBound.Spec.NativeRoutingFamilySupport

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online NativeNormalize NativeRouting NativeRoutingCoupling.Coordinates
open NativeRoutingFamilySupport NativeMatchPhysical

/-- Equal complete real messages retain equal counter and level fields as well
as equal fingerprints. Different families therefore never alias even when
normalization collides. The existing coordinate theorem keeps its old type. -/
def NativeRoutingRealCodeFamily_statement : Prop :=
  ∀ (stored : Tape 128) (counter counter' : Counter) (level level' : Level)
    (key key' : LogicalKey),
  nativeCode stored (.real counter level key) = nativeCode stored (.real counter' level' key') ↔
    counter = counter' ∧ level = level' ∧ stored key = stored key'

/-- Tiling and the existing one-top premise bound the consumed frontier above
any still-probed table. No ordering between successive snapshots is assumed. -/
def NativeRoutingPlanFrontier_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.LowerCompatible →
  ∀ (schedule : Schedule) (n m width : Nat),
    SchedulePremises geo.cfg schedule n m → NonTopWidth geo.cfg width →
  ∀ t, t < n → ∀ coordinate ∈ (schedule t).tables,
    (schedule t).consumed * geo.cfg.carryPositions 1 ≤
      familyEnd geo.cfg coordinate.1 coordinate.2 + (schedule t).tables.length * width

/-- The actual successful FillDensePrefix guard and requester position
arithmetic bound an operation start less than three prefixes past consumed.
The strict endpoint includes the current partial unit. -/
def NativeRoutingRingPosition_statement : Prop :=
  ∀ (r0 consumed flushes current position : Nat), 0 < r0 → current < 64 →
    position = flushes * 64 + current →
  ∀ units, fillDenseUnits r0 2 consumed flushes = some units →
    position < consumed * (64 * r0) + 3 * (64 * r0)

/-- Each actual probing slot lies in one bounded interval for its terminal
family, including batches, the zero-width empty top, blind stretches and
nonmonotone snapshots. The physical allocation bounds the table count.
The run has internal frames of at most 64 lanes; no user batch bound is added.
A production-Context instantiation and family-population count remain separate. -/
def NativeRoutingProbeInterval_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.LowerCompatible →
  ∀ (g : OnlineGeom) (run : OnlineBatch.BatchRun) (slots n m width : Nat)
    (snapshots : Nat → Snapshot slots),
    g.unitEntries = 64 → 0 < g.unitsPerPrefix →
    64 * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    (∀ op ∈ run.ops, op.lanes.length ≤ 64) →
    SchedulePremises geo.cfg (physicalSchedule geo.cfg snapshots) n m →
    NonTopWidth geo.cfg width → ready g run snapshots n = true →
  ∀ t, t < n → ∀ slot, (OnlineBatch.slots run)[t]? = some slot → slot.probes = true →
  ∀ coordinate ∈ (physicalSchedule geo.cfg snapshots
      (OnlineBatch.chunkStart (OnlineBatch.widths run) t)).tables,
    familyEnd geo.cfg coordinate.1 coordinate.2 ≤ pos geo.cfg t ∧
      pos geo.cfg t < familyEnd geo.cfg coordinate.1 coordinate.2 +
        slots * width + 3 * geo.cfg.carryPositions 1 + 64

end RebuildBound.Spec
