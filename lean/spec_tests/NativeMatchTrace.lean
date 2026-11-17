import RebuildBound.Spec.NativeMatch.Trace

set_option maxRecDepth 4000

namespace RebuildBound.NativeMatchTraceTests
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace

def key (n : Nat) : LogicalKey := LogicalKey.ofNat n
def record (n : Nat) : Rec := ⟨key n,n,false⟩
def one (n : Nat) : Page := (fun _ => record n,1)
def sparse : Page :=
  (fun i => if i = 9 then record 1 else if i = 63 then record 2 else record 99,
   ((1 : Mask) <<< 9) ||| ((1 : Mask) <<< 63))

/-- The second source sees only subjects surviving the first source's clear;
dummy payloads never enter the comparison list, including at the last lane. -/
example : (poolTrace [one 1,one 2] [sparse]).map Event.comparison =
    [(key 1,[key 1]),(key 2,[key 1]),(key 2,[key 2])] := by
  decide +kernel

example : ((poolExact [one 1] [sparse]).getD 0 (one 0)).2 = (1 : Mask) <<< 63 := by
  decide +kernel

def prefixData (page : Nat) : DirectMask64.Payload :=
  fun _ => if page = 2 then record 2 else record 1

/-- The later prefix pair whose older mask was cleared emits no subjects. -/
example : (prefixTrace prefixData 1 [1,1,1] [0,1,2]).map Event.comparison =
    [(key 1,[key 1]),(key 1,[key 2])] := by
  decide +kernel

/-- Clearing the first destination does not consume the retained source. -/
example : (fixedTrace (one 1) [one 1,one 1] [0,1]).map Event.comparison =
    [(key 1,[key 1]),(key 1,[key 1])] := by
  decide +kernel
example : (fixedExact (one 1) [one 1,one 1] [0,1]).map Prod.snd = [0,0] := by
  decide +kernel

/-- Both class directions read the same pre-state. This deliberately includes
a repeated B key to distinguish simultaneous masks from sequential clearing. -/
example : (classExact (one 1) (fun _ => record 1,3) 1 2).1.2 = 0 ∧
    (classExact (one 1) (fun _ => record 1,3) 1 2).2.2 = 2 := by
  decide +kernel

/-- A later physical A group compares against keys inserted by the earlier
group of the same source; regrouping the current compacted list would lose this. -/
example : (groupedOfferEvents (Bucket.empty 64) (fun _ => true) [one 1,one 2]).map
    Event.comparison = [(key 1,[]),(key 2,[key 1])] := by
  decide +kernel

/-- Empty partners retain a zero-weight subject event; empty subjects emit none. -/
example : (pairEvents .resolveALeaf (one 1).1 (one 2).1 0 1).map Event.comparison =
    [(key 2,[])] := by decide +kernel
example : pairEvents .resolveBTier (one 1).1 (one 2).1 1 0 = [] := by decide +kernel

end RebuildBound.NativeMatchTraceTests
