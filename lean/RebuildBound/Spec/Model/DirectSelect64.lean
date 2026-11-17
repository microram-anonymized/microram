import RebuildBound.Spec.Model.DirectCache64
import RebuildBound.Spec.Model.DirectScan
import RebuildBound.Spec.Model.DirectDrain

/-! Lane-level semantics of `SelectDenseHomesRange` and the capacity checks of
`DrainDenseRemainderRange` (`src/oram/rebuild/cpu_byteslice_dense_select.hpp`).

Sources are the flat prefix buckets; an address is (source bucket, lane).
For each home, every source in order offers `remaining & homeMask`; `alloc`
candidates go, by `_pdep_u64`, from the lowest candidate lanes into the
lowest free destination lanes, and leave the remaining mask. `place` is the
lane semantics of `BuildMergeIndex(used, taken)` followed by the masked
`permutex2var` with the running occupancy as keep mask. The native loop
handles sources in chunks of `kDenseSelectChunk` only to reuse destination
lines; that byte-level batching is not modelled.

`homeMask s h` is the source's candidate mask at home `h` for an all-ones
remaining mask; by `DirectCache64Clear` the native `DenseHomeCandidates` is
`remaining &&& homeMask s h` with `homeMask s h :=
DirectCache64.candidates bits storage s (BitVec.allOnes 64) (BitVec.ofNat 64 h)`
for homes `h < 2^bits` (the cache compares only the low `bits` bits). Byte storage, SIMD
instruction semantics and the residual stash's internal permutation remain native.
-/
namespace RebuildBound.Model.DirectSelect64

abbrev Address := Nat × Nat

/-- A 64-lane mask from its lane bits. -/
def ofLanes (f : Nat → Bool) : BitVec 64 :=
  (BitVec.ofBoolListLE ((List.range 64).map f)).setWidth 64

/-- Set lanes in ascending order. -/
def lanes (m : BitVec 64) : List Nat := (List.range 64).filter m.getLsbD

/-- `_pdep_u64`: the `i`-th set lane of `mask` receives bit `i` of `src`. -/
def pdep (src mask : BitVec 64) : BitVec 64 :=
  ofLanes fun lane => mask.getLsbD lane && src.getLsbD ((List.range lane).countP mask.getLsbD)

/-- Each source's set lanes as addresses, keeping source boundaries. -/
def addresses (masks : List (BitVec 64)) : List (List Address) :=
  masks.mapIdx fun s m => (lanes m).map (s, ·)

/-- Destination lanes in `used` take source `s`'s lanes in `taken` in
ascending order; lanes outside `keep` are cleared; others keep their content. -/
def place (dest : List (Option Address)) (s : Nat) (used taken keep : BitVec 64) :
    List (Option Address) :=
  (List.range 64).map fun d =>
    if !keep.getLsbD d then none
    else if used.getLsbD d then ((lanes taken)[(lanes used).idxOf d]?).map (s, ·)
    else dest.getD d none

structure HomeState where
  occupied : BitVec 64
  dest : List (Option Address)
  remaining : List (BitVec 64)

/-- One source of one home. -/
def sourceStep (homeMask : Nat → BitVec 64) (st : HomeState) (s : Nat) : HomeState :=
  let cand := st.remaining.getD s 0 &&& homeMask s
  let alloc := min (lanes cand).length (64 - (lanes st.occupied).length)
  let used := pdep (DirectCache64.lowMask alloc) (~~~st.occupied)
  let taken := pdep (DirectCache64.lowMask alloc) cand
  { occupied := st.occupied ||| used
    dest := place st.dest s used taken (st.occupied ||| used)
    remaining := st.remaining.modify s (· &&& ~~~taken) }

/-- One home: every source in order, from an empty destination. -/
def selectHome (homeMask : Nat → Nat → BitVec 64) (remaining : List (BitVec 64))
    (h : Nat) : HomeState :=
  (List.range remaining.length).foldl (sourceStep (homeMask · h))
    ⟨0, List.replicate 64 none, remaining⟩

/-- Homes in order (a task's range, or several tasks): the final remaining
masks and, per home, its destination lanes and mask. -/
def selectHomes (homeMask : Nat → Nat → BitVec 64) (remaining : List (BitVec 64))
    (homes : List Nat) : List (BitVec 64) × List (List (Option Address) × BitVec 64) :=
  homes.foldl (fun acc h =>
    let st := selectHome homeMask acc.1 h
    (st.remaining, acc.2 ++ [(st.dest, st.occupied)])) (remaining, [])

/-- Reference: the logical scan of one home's candidate addresses. -/
def selected (homeMask : Nat → Nat → BitVec 64) (remaining : List (BitVec 64))
    (h : Nat) : List Address :=
  (DirectScan.run 64
    (addresses (remaining.mapIdx fun s m => m &&& homeMask s h))).selected

/-- The drain's capacity checks: count plus popcount against the capacity,
source by source; `none` is the declared failure. -/
def drainCount (capacity : Nat) (masks : List (BitVec 64)) : Option Nat :=
  masks.foldl (fun acc m => acc.bind fun count =>
    if count + (lanes m).length ≤ capacity then some (count + (lanes m).length) else none)
    (some 0)

end RebuildBound.Model.DirectSelect64
