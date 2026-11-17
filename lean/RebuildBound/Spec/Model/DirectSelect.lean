import RebuildBound.Spec.Model.DirectB
/-! Logical source-order selection using unique source-lane occurrence indices,
not record keys. Payloads (including tombstones) can be recovered by an index
map. `homes` groups surviving indices in home order, stably within each home.
The drain preserves source order; grouped dropped suffixes preserve home order.
This specification does not extract native cached-home comparisons, pdep,
eight-source chunks, mutable masks or checked writes in
`src/oram/rebuild/cpu_byteslice_dense_select.hpp`. -/
namespace RebuildBound.Model.DirectSelect

def drain (cap : Nat) (source : List Nat) (homes : List (List Nat)) : List Nat :=
  source.filter (fun i => i ∈ DirectB.residual cap homes)

/-- Exact occurrence coverage and stable within-home grouping. -/
def Grouped (source : List Nat) (homes : List (List Nat)) : Prop :=
  source.Nodup ∧ homes.flatten.Perm source ∧
    ∀ xs ∈ homes, xs.Sublist source
end RebuildBound.Model.DirectSelect
