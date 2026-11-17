import RebuildBound.Proofs.NativeRoutingBuildSupport
import RebuildBound.Proofs.NativeRoutingLocalTable

/-! Completed support uses actual accesses, includes initialization once at its
seeded family, and charges full 64-slot requester units. -/
namespace RebuildBound.NativeRoutingBuildSupportTests
open Model Model.Hierarchy Spec NativeRoutingBuildSupport

private def cfg : Config := ⟨[4], 2, 8, 32, 128, false⟩

/-- With no issued lanes, only the seeded coordinate at each level is allowed. -/
example : completedCoordinates cfg 0 = {(1, 0), (2, 0)} := by
  decide +kernel

/-- The first completed lower prefix is exposed at 64 charged positions,
not at a certificate-horizon boundary. -/
example : completedCoordinates cfg 63 = {(1, 0), (2, 0)} ∧
    completedCoordinates cfg 64 = {(1, 0), (1, 1), (2, 0)} := by
  decide +kernel

/-- Extending only the certificate horizon changes no candidate coordinate. -/
example (config : Config) (q horizon : Nat) :
    completedCoordinates { config with horizon := horizon } q =
      completedCoordinates config q := rfl

/-- Lower seeded bases contribute no arbitrary future-unit keys. -/
example (sh : Shapes) (trace : Trace) (words : Words) :
    coordinateKeys cfg sh trace words 1 0 = [] := by
  simp [coordinateKeys, HierarchyLocalityProof.table_eq, base, cfg, Config.seed, Config.levels,
    Model.DirectJob.emptyOutput, Output.records, Bucket.recs]

/-- Initialization input is present at the seeded top, even when its output
has no retained records. It must not disappear from the construction charge. -/
example (sh : Shapes) (trace : Trace) (words : Words) (record : Rec)
    (hr : record ∈ trace.init) :
    record.key ∈ coordinateKeys { cfg with initialized := true } sh trace words 2
      (({ cfg with initialized := true } : Config).seed 2) := by
  apply List.mem_append_right
  simp only [show (2 : Nat) = ({ cfg with initialized := true } : Config).levels by rfl,
    and_self, ite_true]
  exact List.mem_map.mpr ⟨record, hr, rfl⟩

/-- Repeated family reconstruction is deduplicated by a finite set of keys. -/
example (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : NativeMatchProduction.Context member initialized h) (tape : IdealKey.Tape)
    (family : IdealKey.Family) :
    buildKeys ctx tape family ∪ buildKeys ctx tape family = buildKeys ctx tape family :=
  Finset.union_self _

/-- The fresh-input coefficient accounts for every 64-slot unit, including
retained tombstones. -/
example (member : ConfigurationFamily.Member) :
    coordinateAllowance member = 3 * NativeMatchExactCounts.maxRecords member +
      64 * member.r0 + (member.geometry false).keyCapacity := rfl

/-- Build and probe supports can be combined under the original ring guard;
there is no capacity-success premise or dependence on historical key count. -/
example (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : NativeMatchProduction.Context member initialized h)
    (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid) (tape : IdealKey.Tape)
    (hr : NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true)
    (family : IdealKey.Family) :
    (buildKeys ctx tape family ∪ NativeRoutingFamilyExposure.probeKeys ctx tape family).card ≤
      buildAllowance member + NativeRoutingFamilyExposure.probeSpan member initialized := by
  have hp := NativeRoutingProbeKeysBound member initialized h ctx hm hv tape hr family
  exact Finset.card_union_le _ _ |>.trans
    (Nat.add_le_add (NativeRoutingBuildKeysBound member initialized h ctx hm hv tape family)
      (hp.1.trans hp.2))

/- Independent kernel arithmetic across all 94 geometries. These are support
components, not a combined routing-pair or endpoint certificate. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
example : ∀ member ∈ ConfigurationFamily.members,
    8320 ≤ coordinateAllowance member ∧ coordinateAllowance member ≤ 8589935104 ∧
    16640 ≤ buildAllowance member ∧ buildAllowance member ≤ 77309412480 := by
  decide +kernel

end RebuildBound.NativeRoutingBuildSupportTests
