import RebuildBound.Spec.Model.DirectAddresses
import RebuildBound.Spec.Model.DirectCache
import RebuildBound.Spec.Model.DirectScan

/-! Compose the abstract source-address bridge with scalar byte-cache selection.
The cache reads the original source payload, at the address of a dense survivor.
The default bytes on an invalid/empty lookup are excluded by the proved index
bounds. This is an executable reference cache, not native storage extraction. -/
namespace RebuildBound.Model.DirectSourceCache

/-- Reference byte cache at a survivor's original unit/lane address. -/
def cache (word : LogicalKey → Nat) (bits : Nat) (units masked : List Bucket)
    (i j : Nat) : Nat :=
  ((DirectAddresses.lookup units (DirectAddresses.address masked i)).map
    (fun r => DirectCache.cached word bits r j)).getD 0

/-- Source-order candidate chunks from original source-cache bytes. Earlier
clears are represented by the caller's chosen chunks; listed indices use a true
remaining bit. The correspondence theorem requires valid survivor indices. -/
def candidates (compare : DirectMasks.Comparison) (bits : Nat)
    (word : LogicalKey → Nat) (units : List Bucket) (home : Nat)
    (chunks : List (List Nat)) : List (List Nat) :=
  chunks.map (fun chunk => chunk.filter (fun i =>
    DirectCache.candidate bits (cache word bits units (DirectMasks.run compare [] units) i)
      true home))

end RebuildBound.Model.DirectSourceCache
