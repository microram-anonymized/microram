import RebuildBound.Spec.DirectSelect64
/-! Small-instance evaluation of the DirectSelect64 statements:
`lake env lean spec_tests/DirectSelect64.lean` (every `#guard` must pass). -/
open RebuildBound RebuildBound.Model RebuildBound.Model.DirectSelect64

-- Disjoint lane masks per home (a lane's home is a hash mod 3).
def hm (s h : Nat) : BitVec 64 := ofLanes fun l => (s * 7 + l * 5 + l / 9) % 3 == h
def rem : List (BitVec 64) :=
  [0xFFFFFFFFFFFFFFFF, 0xF0F0FFFF0F0FFFFF, 0xFFFFFFFFFFFF0000, 0x7FFFFFFFFFFFFFFE,
   0xFFFFFFFF, 0x0123456789ABCDEF]

#guard [0x0, 0x1, 0x8000000000000000, 0xF0F0F0F0F0F0F0F0, 0x0123456789ABCDEF].all fun (m : BitVec 64) =>
  (List.range 70).all fun k => lanes (pdep (DirectCache64.lowMask k) m) == (lanes m).take k

-- at least one home overflows 64 lanes
#guard (List.range 3).any fun h =>
  64 < ((addresses (rem.mapIdx fun s m => m &&& hm s h)).flatten).length

#guard (List.range 3).all fun h =>
  let st := selectHome hm rem h
  let sel := selected hm rem h
  st.dest == (List.range 64).map (fun d => sel[d]?) &&
  lanes st.occupied == List.range sel.length &&
  addresses st.remaining == (addresses rem).map (List.filter (· ∉ sel))

#guard
  let homes := [2, 0, 1]
  (selectHomes hm rem homes).2 ==
      homes.map (fun h => ((selectHome hm rem h).dest, (selectHome hm rem h).occupied)) &&
  addresses (selectHomes hm rem homes).1 ==
      (addresses rem).map (List.filter (· ∉ homes.flatMap (selected hm rem)))

-- a repeated home is not independent (why `homes.Nodup` is needed)
#guard (selectHomes hm rem [0, 0]).2 !=
  [0, 0].map (fun h => ((selectHome hm rem h).dest, (selectHome hm rem h).occupied))

#guard (List.range 400).all fun c =>
  drainCount c rem == (DirectDrain.run c [] (addresses rem)).map List.length
