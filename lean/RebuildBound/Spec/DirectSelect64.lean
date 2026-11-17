import RebuildBound.Spec.Model.DirectSelect64
import RebuildBound.Spec.Model.DirectDrain

namespace RebuildBound.Spec
open Model Model.DirectSelect64

/-- `pdep` of a low mask selects the lowest set lanes, for every count. -/
def DirectSelect64Pdep_statement : Prop :=
  ∀ (k : Nat) (m : BitVec 64),
    lanes (pdep (DirectCache64.lowMask k) m) = (lanes m).take k

/-- One home: the destination holds the scan's selected addresses in its
lowest lanes, its mask is exactly those lanes, and every source loses exactly
its selected lanes. -/
def DirectSelect64Home_statement : Prop :=
  ∀ (homeMask : Nat → Nat → BitVec 64) (remaining : List (BitVec 64)) (h : Nat),
    let st := selectHome homeMask remaining h
    let sel := selected homeMask remaining h
    st.dest = (List.range 64).map (fun d => sel[d]?) ∧
    lanes st.occupied = List.range sel.length ∧
    addresses st.remaining = (addresses remaining).map (List.filter (· ∉ sel))

/-- Distinct homes with disjoint lane masks do not interfere: each home's
output is its selection on the initial masks, and the sources lose exactly
the union of the selected addresses. -/
def DirectSelect64Homes_statement : Prop :=
  ∀ (homeMask : Nat → Nat → BitVec 64) (remaining : List (BitVec 64)) (homes : List Nat),
    homes.Nodup →
    (∀ s h h', h ∈ homes → h' ∈ homes → h ≠ h' → homeMask s h &&& homeMask s h' = 0) →
    (selectHomes homeMask remaining homes).2 =
      homes.map (fun h => ((selectHome homeMask remaining h).dest,
        (selectHome homeMask remaining h).occupied)) ∧
    addresses (selectHomes homeMask remaining homes).1 =
      (addresses remaining).map
        (List.filter (· ∉ homes.flatMap (selected homeMask remaining)))

/-- The drain's checks are the checked append of the remaining addresses,
source by source. -/
def DirectSelect64Drain_statement : Prop :=
  ∀ (capacity : Nat) (masks : List (BitVec 64)),
    drainCount capacity masks =
      (DirectDrain.run capacity [] (addresses masks)).map List.length

end RebuildBound.Spec
