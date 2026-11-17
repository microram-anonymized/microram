import RebuildBound.Proofs.HierarchyInvariant
import RebuildBound.Spec.HierarchyChunk

/-!
# HierarchyInvariantChunks

`HierarchyInvariant` at every chunk horizon. The generic argument
`HierarchyInvariantProof.contracts` holds at any configuration with `Facts`
(it bounds the loads by the trace premises and `N ≤ 2^27`, for every potential
job, whatever the horizon). The facts do not read the horizon: every field but
the separated rows is definitionally the same at `{cfg with horizon := H}`,
and the rows are by `HierarchyHorizonFree`.
-/

namespace RebuildBound.HierarchyInvariantProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Spec

/-- The facts transfer to any horizon. -/
theorem facts_horizon (hF : HierarchyHorizonFree_statement) {cfg : Config}
    {rows : List (SepGeom × Nat)} (F : Facts cfg rows) (H : Nat) :
    Facts { cfg with horizon := H } rows where
  init := F.init
  levels2 := F.levels2
  load := F.load
  carry1 := F.carry1
  fan := F.fan
  seed := F.seed
  carrySucc := F.carrySucc
  carryPow := F.carryPow
  carryTop := F.carryTop
  rows ℓ d a b c e := by
    rw [(hF cfg H rows).2.1]
    exact F.rows ℓ d a b c e

end RebuildBound.HierarchyInvariantProof

open RebuildBound.HierarchyInvariantProof in
/-- **HierarchyInvariantChunks.** -/
theorem RebuildBound.HierarchyInvariantChunks :
    RebuildBound.Spec.HierarchyInvariantChunks_statement := by
  intro hF h _
  exact ⟨fun N tr hN hT hU words =>
      contracts (facts_horizon hF uniformFacts (h * 2 ^ 32)) hN hT hU words,
    fun N tr hN hT hU words =>
      contracts (facts_horizon hF halfFanoutFacts (h * 2 ^ 32)) hN hT hU words⟩
