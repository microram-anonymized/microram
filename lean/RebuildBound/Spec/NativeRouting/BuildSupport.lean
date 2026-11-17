import RebuildBound.Spec.NativeRouting.LocalTable
import RebuildBound.Spec.NativeRouting.FamilyExposure
import RebuildBound.Spec.NativeMatch.ExactCounts

/-! Completed-table routing support, counted using actual issued lanes. The
inventory is chosen from the canonical logical execution without a stored
fingerprint argument. Repeated reconstruction shares the same finite support.
This package covers completed table construction; it does not schedule API
frames or account for speculative preparation of an incomplete future table. -/
namespace RebuildBound.Spec.NativeRoutingBuildSupport
open Model Model.Hierarchy Model.Online NativeMatchProduction NativeMatchExactCounts

/-- Public completed coordinates, including the seeded base at every level.
The bounds use the actual charged-lane count, never the certificate horizon. -/
def completedCoordinates (cfg : Config) (q : Nat) : Finset (Nat × Nat) :=
  (Finset.Icc 1 cfg.levels).biUnion fun level =>
    (Finset.Icc (cfg.seed level) (cfg.seed level + q / cfg.carryPositions level)).image
      fun ordinal => (level, ordinal)

/-- Current job inputs and its own output keys. Own output keys cover the
next level-one ordinal's old-home reads. Initialization is included only at
the seeded top. No preparation-output or future diagnostic reads are needed. -/
def coordinateKeys (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words)
    (level ordinal : Nat) : List LogicalKey :=
  (if cfg.seed level < ordinal then
    (table cfg sh tr words level (ordinal - 1)).records.map Rec.key ++
      (if level = 1 then (DirectMasks.records (tr.units (ordinal - cfg.seed 1 - 1))).map Rec.key
        else (carryOf cfg sh tr words level ordinal).records.map Rec.key)
    else []) ++
    (table cfg sh tr words level ordinal).records.map Rec.key ++
    (if level = cfg.levels ∧ ordinal = cfg.seed level ∧ cfg.initialized = true then
      tr.init.map Rec.key else [])

noncomputable def familyCoordinates (cfg : Config) (q : Nat) (family : IdealKey.Family) :
    Finset (Nat × Nat) := by
  classical
  exact (completedCoordinates cfg q).filter fun c => familyOf cfg c.1 c.2 = family

noncomputable def buildKeys {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (family : IdealKey.Family) : Finset LogicalKey := by
  classical
  exact (familyCoordinates ctx.geo.cfg ctx.accesses family).biUnion fun c =>
    (coordinateKeys ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape))
      (IdealHierarchy.words tape) c.1 c.2).toFinset

noncomputable def buildOrdinals (cfg : Config) (q level : Nat) : Finset Nat := by
  classical
  exact ((completedCoordinates cfg q).image fun c => familyOf cfg c.1 c.2).filterMap
    (fun family => if family.1 = level then some family.2 else none)
    (by intro a b value ha hb; simp_all; exact Prod.ext (by omega) (by omega))

/-- A deliberately conservative logical-input population allowance. It covers
reference overflow continuations and retained records without physical caps. -/
def coordinateAllowance (member : ConfigurationFamily.Member) : Nat :=
  3 * maxRecords member + 64 * member.r0 + (member.geometry false).keyCapacity

def buildAllowance (member : ConfigurationFamily.Member) : Nat :=
  (member.config false).levels * coordinateAllowance member

end RebuildBound.Spec.NativeRoutingBuildSupport

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online NativeMatchProduction NativeRoutingActual
open NativeRoutingLocalTable NativeRoutingBuildSupport

/-- A terminal family has at most one contributing completed coordinate at
each level: equality of families retains the endpoint, and carry sizes are
positive. -/
def NativeRoutingBuildFamilyCoordinates_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members →
    ∀ family, (familyCoordinates ctx.geo.cfg ctx.accesses family).card ≤ ctx.geo.cfg.levels

/-- Deduplicated construction keys per family have a geometry-only bound on
every canonical routing outcome. Capacity/ring success is not assumed. -/
def NativeRoutingBuildKeysBound_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ tape family, (buildKeys ctx tape family).card ≤ buildAllowance member

/-- Completed construction and all recursive dependency families have
actual-q ordinal bounds, including initialization. -/
def NativeRoutingBuildOrdinalsBound_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members →
    ∀ level, 1 ≤ level → level ≤ ctx.geo.cfg.levels →
      buildOrdinals ctx.geo.cfg ctx.accesses level ⊆ Finset.Icc (ctx.geo.cfg.seed level)
        (ctx.geo.cfg.seed level + ctx.accesses / ctx.geo.cfg.carryPositions level) ∧
      (buildOrdinals ctx.geo.cfg ctx.accesses level).card ≤
        1 + ctx.accesses / ctx.geo.cfg.carryPositions level

/-- Every real read of the sparse completed-table program lies in the
canonical family support. Dummy reads never occur in this table program.
Base requests below the seed are admitted and resolve to the seeded family. -/
def NativeRoutingBuildReadsCovered_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ tape level ordinal, 1 ≤ level → level ≤ ctx.geo.cfg.levels →
      ordinal ≤ ctx.geo.cfg.seed level + ctx.accesses / ctx.geo.cfg.carryPositions level →
    ∀ read ∈ ReadTree.reads tape
      (tableProgram ctx.geo.cfg ctx.geo.shapes (OnlineBatch.traceOf ctx.unit (ctx.run tape))
        level ordinal),
      ∃ family key, read.1 = Sum.inl (family, key) ∧ key ∈ buildKeys ctx tape family

end RebuildBound.Spec
