import RebuildBound.Spec.NativeMatch.DenseTrace
import RebuildBound.Spec.Model.DirectJobBridge
import RebuildBound.Spec.Model.SepContract
import RebuildBound.Spec.Model.TopContract
import RebuildBound.Spec.IdealFailure

/-! Exact-prestate matching writers around the existing finish transitions.
Ghost pages retain original grouping and masks. Capacity guards and probability
bounds are separate; these definitions do not receive stored-key values. -/
namespace RebuildBound.Spec.NativeMatchJobTrace
open Model NativeMatch NativeMatch.Lanes NativeMatchTrace

/-- Erasure is the existing finish state. The extra field retains original
physical group boundaries of every A leaf throughout the exact writer run. -/
structure FinishGhost where
  state : SFin
  groups : List (List Page)

def offerAExact (g : SepGeom) (word : LogicalKey → Nat) (ci : Nat)
    (ghost : FinishGhost) : FinishGhost :=
  let R := ci / 2 ^ g.I
  let result := groupedOfferExact (ghost.state.main.getD ci [])
    (fun r => sHome g word r == ci) (ghost.groups.getD R [])
  ⟨sOfferA g word ci ghost.state, ghost.groups.set R result.2⟩

def offerANative (stored : LogicalKey → Stored) (g : SepGeom)
    (word : LogicalKey → Nat) (ci : Nat) (ghost : FinishGhost) : FinishGhost :=
  let R := ci / 2 ^ g.I
  let result := offerAGroupsNative stored g word ci ghost.state (ghost.groups.getD R [])
  ⟨result.1, ghost.groups.set R result.2⟩

def offerAEvents (g : SepGeom) (word : LogicalKey → Nat) (ci : Nat)
    (ghost : FinishGhost) : List Event :=
  groupedOfferEvents (ghost.state.main.getD ci []) (fun r => sHome g word r == ci)
    (ghost.groups.getD (ci / 2 ^ g.I) [])

def offerBExact (g : SepGeom) (word : LogicalKey → Nat) (ci : Nat)
    (ghost : FinishGhost) : FinishGhost :=
  ⟨sOfferB g word ci ghost.state, ghost.groups⟩

def offerBNative (stored : LogicalKey → Stored) (g : SepGeom)
    (word : LogicalKey → Nat) (ci : Nat) (ghost : FinishGhost) : FinishGhost :=
  ⟨(List.range ghost.state.bcopy.length).foldl
    (NativeMatchTrace.offerBNative stored g word ci) ghost.state, ghost.groups⟩

def offerBEvents (g : SepGeom) (word : LogicalKey → Nat) (ci : Nat)
    (ghost : FinishGhost) : List Event :=
  eventsOf (sOfferPage g word ci) (NativeMatchTrace.offerBEvents g word ci)
    ghost.state (List.range ghost.state.bcopy.length)

/-- The source bucket is read before all destination clears. -/
def clearExact (g : SepGeom) (Bi : Bucket) (i : Nat) (ghost : FinishGhost) : FinishGhost :=
  let main := (List.range g.d).foldl
    (fun main q => main.set (i + q * g.U)
      ((main.getD (i + q * g.U) []).clear (fun key => Bi.keys.contains key))) ghost.state.main
  ⟨{ ghost.state with main := main }, ghost.groups⟩

def clearNative (stored : LogicalKey → Stored) (g : SepGeom) (Bi : Bucket)
    (i : Nat) (ghost : FinishGhost) : FinishGhost :=
  let main := (fixedNative stored (Page.ofBucket Bi)
    (ghost.state.main.map Page.ofBucket) ((List.range g.d).map (fun q => i + q * g.U))).map Page.bucket
  ⟨{ ghost.state with main := main }, ghost.groups⟩

def clearEvents (g : SepGeom) (Bi : Bucket) (i : Nat) (ghost : FinishGhost) : List Event :=
  fixedTrace (Page.ofBucket Bi) (ghost.state.main.map Page.ofBucket)
    ((List.range g.d).map (fun q => i + q * g.U))

/-- Literal nonmatching prefix of one existing sInsertBucket way: fill, retain
shed identities, and append/check the stash at the last way before offers. -/
def wayBase (g : SepGeom) (word : LogicalKey → Nat) (Bi : Bucket) (i : Nat)
    (acc : FinishGhost × List Rec) (q : Nat) : FinishGhost × List Rec :=
  let ci := i + q * g.U
  let f := fill (acc.1.state.main.getD ci [])
    (Bi.recs.filter (fun x => g.wayOf (word x.key) == q))
  let sheds := acc.2 ++ f.2
  let state := { acc.1.state with main := acc.1.state.main.set ci f.1 }
  let state := if q + 1 = g.d then
      let ins := state.ins ++ sheds
      { state with ins := ins, trace := state.trace ++ [(.insertion, ins.length)] }
    else state
  (⟨state,acc.1.groups⟩,sheds)

def wayExact (g : SepGeom) (word : LogicalKey → Nat) (Bi : Bucket) (i : Nat)
    (acc : FinishGhost × List Rec) (q : Nat) : FinishGhost × List Rec :=
  let base := wayBase g word Bi i acc q
  (offerBExact g word (i + q * g.U) (offerAExact g word (i + q * g.U) base.1),base.2)

def wayNative (stored : LogicalKey → Stored) (g : SepGeom) (word : LogicalKey → Nat)
    (Bi : Bucket) (i : Nat) (acc : FinishGhost × List Rec) (q : Nat) : FinishGhost × List Rec :=
  let base := wayBase g word Bi i acc q
  (offerBNative stored g word (i + q * g.U)
    (offerANative stored g word (i + q * g.U) base.1),base.2)

def wayEvents (g : SepGeom) (word : LogicalKey → Nat) (Bi : Bucket) (i : Nat)
    (acc : FinishGhost × List Rec) (q : Nat) : List Event :=
  let base := wayBase g word Bi i acc q
  offerAEvents g word (i + q * g.U) base.1 ++
    offerBEvents g word (i + q * g.U) (offerAExact g word (i + q * g.U) base.1)

def bucketExact (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : FinishGhost) (i : Nat) : FinishGhost :=
  let Bi := bMain.getD i []
  ((List.range g.d).foldl (wayExact g word Bi i) (clearExact g Bi i ghost,[])).1

def bucketNative (stored : LogicalKey → Stored) (g : SepGeom) (word : LogicalKey → Nat)
    (bMain : List Bucket) (ghost : FinishGhost) (i : Nat) : FinishGhost :=
  let Bi := bMain.getD i []
  ((List.range g.d).foldl (wayNative stored g word Bi i)
    (clearNative stored g Bi i ghost,[])).1

def bucketEvents (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : FinishGhost) (i : Nat) : List Event :=
  let Bi := bMain.getD i []
  clearEvents g Bi i ghost ++ eventsOf (wayExact g word Bi i) (wayEvents g word Bi i)
    (clearExact g Bi i ghost,[]) (List.range g.d)

def finishExact (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : FinishGhost) : FinishGhost :=
  (List.range g.U).foldl (bucketExact g word bMain) ghost

def finishNative (stored : LogicalKey → Stored) (g : SepGeom) (word : LogicalKey → Nat)
    (bMain : List Bucket) (ghost : FinishGhost) : FinishGhost :=
  (List.range g.U).foldl (bucketNative stored g word bMain) ghost

def finishEvents (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : FinishGhost) : List Event :=
  eventsOf (bucketExact g word bMain) (bucketEvents g word bMain) ghost (List.range g.U)

end RebuildBound.Spec.NativeMatchJobTrace

namespace RebuildBound.Spec.NativeMatchJobTrace
open Model NativeMatch NativeMatch.Lanes NativeMatchTrace

/-- DFS leaves are physically one page and compact after partitioning. The
capacity guard is what justifies this construction's per-leaf bound. -/
def onePageLeaves (leaves : List (List Rec)) : List (List Page) :=
  leaves.map (fun leaf => [Page.ofRecords leaf])

end RebuildBound.Spec.NativeMatchJobTrace

namespace RebuildBound.Spec.NativeMatchJobTrace
open Model NativeMatch NativeMatch.Lanes NativeMatchTrace

/-- Erase only the source-class metadata. Every physical empty lane remains. -/
def eraseTags (tier : List (Option (Rec × Bool))) : Bucket :=
  tier.map (fun slot => slot.map Prod.fst)

/-- The B-class occupancy of the initial drain. Dummy metadata never matters,
so the fixed class mask is zero in initially empty lanes. -/
def bClassTags (tier : List (Option (Rec × Bool))) : Bucket :=
  tier.map (fun slot => slot.bind (fun p => if p.2 then none else some p.1))

def drainClasses (tier : List (Option (Rec × Bool))) (page : Nat) : Mask :=
  (Page.ofBucket (bClassTags (tier.drop (64 * page)))).2

def firstDrain (st : SFin) : List (Option (Rec × Bool)) :=
  ((st.leaves.map (fun leaf => leaf.map (fun r => (r,true))) ++
    st.bcopy.map (fun page => page.map (fun r => (r,false)))).foldl sDrainStep ([],[])).1

def drainInitial (shedPages tierPages : Nat) (st : SFin) : Leftovers :=
  (bucketPages shedPages (st.ins.map some), bucketPages tierPages (eraseTags (firstDrain st)))

def drainEvents (shedPages tierPages : Nat) (st : SFin) : List Event :=
  leftoverTrace (drainClasses (firstDrain st)) (drainInitial shedPages tierPages st)
    (leftoverPairs shedPages tierPages)

def drainNative (stored : LogicalKey → Stored) (shedPages tierPages : Nat) (st : SFin) : Bucket :=
  let initial := drainInitial shedPages tierPages st
  let result := (leftoverPairs shedPages tierPages).foldl
    (leftoverNativeStep stored (drainClasses (firstDrain st))) initial
  (fill (result.2.flatMap Page.bucket) (pageRecords result.1)).1

end RebuildBound.Spec.NativeMatchJobTrace

namespace RebuildBound.Spec.NativeMatchJobTrace
open Model NativeMatch NativeMatch.Lanes NativeMatchTrace

def aClassTags (tier : List (Option (Rec × Bool))) : Bucket :=
  tier.map (fun slot => slot.bind (fun p => if p.2 then some p.1 else none))

def drainCarryPages (shedPages tierPages : Nat) (st : SFin) : List Page :=
  (List.range tierPages).map (fun i =>
    let page := (drainInitial shedPages tierPages st).2.getD i default
    (page.1,page.2 &&& ~~~drainClasses (firstDrain st) i))

end RebuildBound.Spec.NativeMatchJobTrace

namespace RebuildBound.Spec.NativeMatchDirectJobTrace
open Model Model.DirectJob NativeMatchTrace NativeMatchJobTrace

/-- Stage drains and the radix append-only drain are grouped once. The old
published A tier is supplied with its original optional lanes and pages. -/
def rawPages (stagePages radixPages : Nat) (aTierPages : List Page) (route : SRoute) : List Page :=
  route.stash.flatMap (fun rs => bucketPages stagePages (rs.map some)) ++
    bucketPages radixPages (route.radix.map some) ++ aTierPages

/-- The direct range retains the surviving physical pool groups. In
particular a four-group direct leaf is never rechunked after deletions. -/
def initialGhost (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) : FinishGhost :=
  let route := (analyticalA g word inp.aMain).state
  let groups := poolExact sources raw
  ⟨finishInitial b route.main [pageRecords groups], [groups]⟩

def events (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) : List Event :=
  poolTrace sources raw ++ NativeMatchJobTrace.finishEvents g.finishTopology word b.bLanes
    (initialGhost g word inp b sources raw)

end RebuildBound.Spec.NativeMatchDirectJobTrace

namespace RebuildBound.Spec.NativeMatchDirectJobTrace
open Model Model.DirectJob NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchJobTrace

def allocatedRaw (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (stagePages radixPages : Nat) (aTierPages : List Page) : List Page :=
  rawPages stagePages (if 1 < g.aTopology.r then radixPages else 0) aTierPages
    (analyticalA g word inp.aMain).state

def initialNative (stored : LogicalKey → Stored) (g : Geometry) (word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page) : FinishGhost :=
  let route := (analyticalA g word inp.aMain).state
  let groups := poolNative stored sources raw
  ⟨finishInitial b route.main [pageRecords groups], [groups]⟩

end RebuildBound.Spec.NativeMatchDirectJobTrace

namespace RebuildBound.Spec.NativeMatchTopJobTrace
open Model NativeMatch NativeMatch.Lanes NativeMatchTrace

/-- The B-tier pages retain their published physical boundaries; erasure is
`pageRecords bpages = state.bcopy`. Leaves remain one-page DFS outputs. -/
structure Ghost where
  state : FinState
  bpages : List Page

def resolveExact (g : TopGeom) (word : LogicalKey → Nat) (ci : Nat)
    (direction : Page) (ghost : Ghost) : Ghost :=
  ⟨topResolve g word ci direction.bucket.keys ghost.state,
    ghost.bpages.map (Page.filter (fun r => !(topHome g word r == ci && r.tomb)))⟩

def resolveNative (stored : LogicalKey → Stored) (g : TopGeom)
    (word : LogicalKey → Nat) (ci : Nat) (direction : Page) (ghost : Ghost) : Ghost :=
  ⟨topResolveNative stored g word ci direction ghost.state ghost.bpages,
    ghost.bpages.map (Page.filter (fun r => !(topHome g word r == ci && r.tomb)))⟩

def resolveEvents (g : TopGeom) (word : LogicalKey → Nat) (ci : Nat)
    (direction : Page) (ghost : Ghost) : List Event :=
  topResolveEvents g word ci direction ghost.state ghost.bpages

/-- The keys consumed by the second, nonmatching top offer, computed before
mutation with the actual ordered fill after the A offer. -/
def placedB (g : TopGeom) (word : LogicalKey → Nat) (ci : Nat) (st : FinState) : List LogicalKey :=
  let ca := (st.leaves.getD (ci / 2 ^ g.I) []).filter fun r => topHome g word r == ci
  let fa := fill (st.main.getD ci []) ca
  let cb := st.bcopy.filter fun r => topHome g word r == ci
  let fb := fill fa.1 cb
  (cb.take (cb.length - fb.2.length)).map Rec.key

def offer (g : TopGeom) (word : LogicalKey → Nat) (ci : Nat) (ghost : Ghost) : Ghost :=
  ⟨topOffer g word ci ghost.state,
    ghost.bpages.map (Page.filter (fun r => !(placedB g word ci ghost.state).contains r.key))⟩

def direction (g : TopGeom) (word : LogicalKey → Nat) (Bi : Bucket) (q : Nat) : Page :=
  Page.filter (fun r => topWay g word r == q) (Page.ofBucket Bi)

def destExact (g : TopGeom) (word : LogicalKey → Nat) (Bi : Bucket) (i q : Nat)
    (ghost : Ghost) : Ghost × List Rec :=
  let ci := i + q * g.U
  let resolved := resolveExact g word ci (direction g word Bi q) ghost
  let f := fill (resolved.state.main.getD ci [])
    ((Bi.recs.filter (fun r => topWay g word r == q)).filter (fun r => !r.tomb))
  (offer g word ci ⟨{resolved.state with main := resolved.state.main.set ci f.1},resolved.bpages⟩,f.2)

def destNative (stored : LogicalKey → Stored) (g : TopGeom) (word : LogicalKey → Nat)
    (Bi : Bucket) (i q : Nat) (ghost : Ghost) : Ghost × List Rec :=
  let ci := i + q * g.U
  let resolved := resolveNative stored g word ci (direction g word Bi q) ghost
  let f := fill (resolved.state.main.getD ci [])
    ((Bi.recs.filter (fun r => topWay g word r == q)).filter (fun r => !r.tomb))
  (offer g word ci ⟨{resolved.state with main := resolved.state.main.set ci f.1},resolved.bpages⟩,f.2)

def destEvents (g : TopGeom) (word : LogicalKey → Nat) (Bi : Bucket) (i q : Nat)
    (ghost : Ghost) : List Event :=
  resolveEvents g word (i + q * g.U) (direction g word Bi q) ghost

def clearExact (g : TopGeom) (Bi : Bucket) (i : Nat) (ghost : Ghost) : Ghost :=
  let main := (List.range g.D).foldl (fun main q => main.set (i + q * g.U)
    ((main.getD (i + q * g.U) []).clear (fun key => Bi.keys.contains key))) ghost.state.main
  ⟨{ghost.state with main := main},ghost.bpages⟩

def clearNative (stored : LogicalKey → Stored) (g : TopGeom) (Bi : Bucket)
    (i : Nat) (ghost : Ghost) : Ghost :=
  let main := (fixedNative stored (Page.ofBucket Bi)
    (ghost.state.main.map Page.ofBucket) ((List.range g.D).map (fun q => i + q * g.U))).map Page.bucket
  ⟨{ghost.state with main := main},ghost.bpages⟩

def clearEvents (g : TopGeom) (Bi : Bucket) (i : Nat) (ghost : Ghost) : List Event :=
  fixedTrace (Page.ofBucket Bi) (ghost.state.main.map Page.ofBucket)
    ((List.range g.D).map (fun q => i + q * g.U))

def wayExact (g : TopGeom) (word : LogicalKey → Nat) (Bi : Bucket) (i : Nat)
    (acc : Ghost × List Rec) (q : Nat) : Ghost × List Rec :=
  let p := destExact g word Bi i q acc.1
  (p.1,acc.2 ++ p.2)

def wayNative (stored : LogicalKey → Stored) (g : TopGeom) (word : LogicalKey → Nat)
    (Bi : Bucket) (i : Nat) (acc : Ghost × List Rec) (q : Nat) : Ghost × List Rec :=
  let p := destNative stored g word Bi i q acc.1
  (p.1,acc.2 ++ p.2)

def wayEvents (g : TopGeom) (word : LogicalKey → Nat) (Bi : Bucket) (i : Nat)
    (acc : Ghost × List Rec) (q : Nat) : List Event := destEvents g word Bi i q acc.1

def appendSheds (acc : Ghost × List Rec) : Ghost :=
  let ins := acc.1.state.ins ++ acc.2
  ⟨{acc.1.state with ins := ins, trace := acc.1.state.trace ++ [(.insertion,ins.length)]},acc.1.bpages⟩

def bucketExact (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (i : Nat) : Ghost :=
  let Bi := bMain.getD i []
  appendSheds ((List.range g.D).foldl (wayExact g word Bi i) (clearExact g Bi i ghost,[]))

def bucketNative (stored : LogicalKey → Stored) (g : TopGeom) (word : LogicalKey → Nat)
    (bMain : List Bucket) (ghost : Ghost) (i : Nat) : Ghost :=
  let Bi := bMain.getD i []
  appendSheds ((List.range g.D).foldl (wayNative stored g word Bi i) (clearNative stored g Bi i ghost,[]))

def bucketEvents (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) (i : Nat) : List Event :=
  let Bi := bMain.getD i []
  clearEvents g Bi i ghost ++ eventsOf (wayExact g word Bi i) (wayEvents g word Bi i)
    (clearExact g Bi i ghost,[]) (List.range g.D)

def finishExact (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) : Ghost := (List.range g.U).foldl (bucketExact g word bMain) ghost

def finishNative (stored : LogicalKey → Stored) (g : TopGeom) (word : LogicalKey → Nat)
    (bMain : List Bucket) (ghost : Ghost) : Ghost :=
  (List.range g.U).foldl (bucketNative stored g word bMain) ghost

def finishEvents (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
    (ghost : Ghost) : List Event :=
  eventsOf (bucketExact g word bMain) (bucketEvents g word bMain) ghost (List.range g.U)

end RebuildBound.Spec.NativeMatchTopJobTrace

namespace RebuildBound.Spec.NativeMatchJobTrace
open Model NativeMatchTrace

def separatedGhost (rule : CapRule) (g : SepGeom) (w : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) : FinishGhost :=
  let run := sReferenceWith rule g w inp ops
  ⟨⟨run.route.main, [], run.leaves, inp.bTier, []⟩, onePageLeaves run.leaves⟩

end RebuildBound.Spec.NativeMatchJobTrace

namespace RebuildBound.Spec.NativeMatchTopJobTrace
open Model NativeMatchTrace

/-- Initial top ghost preserves the source tier's published physical pages
and applies the actual early-drop mask before the destination sweep. -/
def initialGhost (g : TopGeom) (unsh : Rec → Bool) (word : LogicalKey → Nat)
    (inp : TopInputs) (bpages : List Page) : Ghost :=
  ⟨⟨inp.cMain,[],leavesOf g.toGeom word (topPool unsh inp),topTierCopy unsh inp,[]⟩,
    bpages.map (Page.filter (fun r => !earlyDrop unsh r))⟩

end RebuildBound.Spec.NativeMatchTopJobTrace

namespace RebuildBound.Spec.NativeMatchJobTrace
open Model NativeMatchTrace

/-- Append-only route stashes are read at their original allocation offsets;
the supplied A-tier pages retain their published holes and boundaries. -/
def rawPoolPages (g : SepGeom) (route : SRoute) (aTier : List Page) : List Page :=
  route.stash.flatMap (fun records => bucketPages g.stashPages (records.map some)) ++
    (if 1 < g.r then bucketPages g.stashPages (route.radix.map some) else []) ++ aTier

/-- Each input B page is compacted only within its original page boundary. -/
def carryTierPages (inp : SInputs) : List Page := inp.bTier.map Page.ofRecords

def poolEvents (g : SepGeom) (route : SRoute) (inp : SInputs) (aTier : List Page) : List Event :=
  poolTrace (carryTierPages inp) (rawPoolPages g route aTier)

end RebuildBound.Spec.NativeMatchJobTrace

namespace RebuildBound.Spec.NativeMatchJobTrace
open Model NativeMatch NativeMatch.Lanes NativeMatchTrace

/-- All ordinary matching sites are recorded from reference prestates. Routing
and DFS remain the existing exact transitions. The final drain is recorded
before any coordinated class mask is mutated. -/
def separatedEvents (rule : CapRule) (g : SepGeom) (word : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (aTier : List Page) : List Event :=
  let run := sReferenceWith rule g word inp ops
  poolEvents g run.route inp aTier ++
    finishEvents g word inp.bMain (separatedGhost rule g word inp ops) ++
    drainEvents g.stashPages g.tierPages run.fin

def separatedInitialNative (stored : LogicalKey → Stored) (rule : CapRule) (g : SepGeom)
    (word : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat))
    (aTier : List Page) : FinishGhost :=
  let route := sRouteWith rule g word inp.aMain ops
  let pool := pageRecords (poolNative stored (carryTierPages inp) (rawPoolPages g route aTier))
  let leaves := sLeaves g word pool
  ⟨⟨route.main,[],leaves,inp.bTier,[]⟩,onePageLeaves leaves⟩

def separatedNative (stored : LogicalKey → Stored) (rule : CapRule) (g : SepGeom)
    (word : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat)) (aTier : List Page) : Output :=
  let finish := finishNative stored g word inp.bMain
    (separatedInitialNative stored rule g word inp ops aTier)
  ⟨finish.state.main,drainNative stored g.stashPages g.tierPages finish.state⟩

end RebuildBound.Spec.NativeMatchJobTrace

namespace RebuildBound.Spec.NativeMatchTopJobTrace
open Model

/-- The top's flat direct B copy is the one B list in the same coordinated
class-drain transition; its physical output pages are built after first drain. -/
def toSFin (state : FinState) : SFin :=
  ⟨state.main,state.ins,state.leaves,[state.bcopy],[]⟩

end RebuildBound.Spec.NativeMatchTopJobTrace

namespace RebuildBound.Spec.NativeMatchTopJobTrace
open Model NativeMatch NativeMatch.Lanes NativeMatchTrace

/-- Top's sweep is preceded by actual raw B-tier-vs-carry matching and followed
by the same coordinated class drain. All events use the exact reference
state, before mutation; raw tombstones participate before early dropping. -/
def events (g : TopGeom) (unsh : Rec → Bool) (word : LogicalKey → Nat)
    (inp : TopInputs) (carryPages bpages : List Page) : List Event :=
  poolTrace bpages carryPages ++ finishEvents g word inp.bMain (initialGhost g unsh word inp bpages) ++
    NativeMatchJobTrace.drainEvents g.mergePages g.tierPages (toSFin (topReference g unsh word inp).fin)

def initialNative (stored : LogicalKey → Stored) (g : TopGeom) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs) (carryPages bpages : List Page) : Ghost :=
  let pool := (pageRecords (poolNative stored bpages carryPages)).filter (fun r => !earlyDrop unsh r)
  ⟨⟨inp.cMain,[],leavesOf g.toGeom word pool,topTierCopy unsh inp,[]⟩,
    bpages.map (Page.filter (fun r => !earlyDrop unsh r))⟩

def native (stored : LogicalKey → Stored) (g : TopGeom) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs) (carryPages bpages : List Page) : Output :=
  let finish := finishNative stored g word inp.bMain
    (initialNative stored g unsh word inp carryPages bpages)
  ⟨finish.state.main.map dropTombs,
    dropTombs (NativeMatchJobTrace.drainNative stored g.mergePages g.tierPages (toSFin finish.state))⟩

end RebuildBound.Spec.NativeMatchTopJobTrace

namespace RebuildBound.Spec.NativeMatchDirectJobTrace
open Model Model.DirectJob NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchJobTrace

def finishState (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs) (b : Table) : SFin :=
  (analyticalFinish g word b (analyticalA g word inp.aMain).state.main
    (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves).state

def fullEvents (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (b : Table) (sources raw : List Page) (shedPages tierPages : Nat) : List Event :=
  events g word inp b sources raw ++ NativeMatchJobTrace.drainEvents shedPages tierPages (finishState g word inp b)

def native (stored : LogicalKey → Stored) (g : Geometry) (word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : Table) (sources raw : List Page) (shedPages tierPages : Nat) : Output :=
  let finish := finishNative stored g.finishTopology word b.bLanes
    (initialNative stored g word inp b sources raw)
  ⟨finish.state.main,NativeMatchJobTrace.drainNative stored shedPages tierPages finish.state⟩

end RebuildBound.Spec.NativeMatchDirectJobTrace

namespace RebuildBound.Spec
open Model NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchJobTrace

/-- Erasing only the page ghosts recovers the existing reference transitions,
for arbitrary operation prefixes. No matching-success premise is needed. -/
def NativeMatchJobProjection_statement : Prop :=
  (∀ (g : SepGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
      (ghost : FinishGhost) (ops : List Nat),
    (ops.foldl (bucketExact g word bMain) ghost).state =
      ops.foldl (fun state i => sInsertBucket g word bMain i state) ghost.state) ∧
  (∀ (g : TopGeom) (word : LogicalKey → Nat) (bMain : List Bucket)
      (ghost : NativeMatchTopJobTrace.Ghost) (ops : List Nat),
    (∀ i ∈ ops, (bMain.getD i []).length = 64) →
    (ops.foldl (NativeMatchTopJobTrace.bucketExact g word bMain) ghost).state =
      ops.foldl (fun state i => topBucket g word bMain i state) ghost.state)

/-- Successful exact reference states construct the leaf layout and all
preserved shape/uniqueness invariants used by the native matching replay. -/
def NativeMatchSeparatedJobTrace_statement : Prop :=
  ∀ (_bridge : NativeMatchLanesBridge_statement) (_retained : NativeMatchRetained_statement)
    (stored : LogicalKey → Stored) (rule : CapRule) (g : SepGeom)
    (oldWord word : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat)),
    rule.Valid → g.Valid → g.C = 64 → SInputShape g oldWord word inp →
    List.Perm ops g.canonicalOps →
    sFirstFailure g (sReferenceWith rule g word inp ops).trace = none →
    (∀ page ∈ inp.bTier, page.length ≤ g.C) →
    let ghost := separatedGhost rule g word inp ops
    ((∀ e ∈ finishEvents g word inp.bMain ghost, ¬e.bad stored) →
      ∀ n, ((List.range g.U).take n).foldl (bucketNative stored g word inp.bMain) ghost =
        ((List.range g.U).take n).foldl (bucketExact g word inp.bMain) ghost) ∧
    ((∃ n, ((List.range g.U).take n).foldl (bucketNative stored g word inp.bMain) ghost ≠
        ((List.range g.U).take n).foldl (bucketExact g word inp.bMain) ghost) →
      ∃ e ∈ finishEvents g word inp.bMain ghost, e.bad stored)

/-- The direct range uses original surviving physical pool pages, including
multi-group leaves. Allocated route storage is justified by actual successful
bounded preparation, and ghost erasure is the existing analytical insert. -/
def NativeMatchDirectJobLayout_statement : Prop :=
  (∀ (g : DirectJob.Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
      (route : SRoute) (stagePages radixPages : Nat) (aTierPages : List Page),
    g.digit ≠ 1 → DirectJob.prepareA g word inp.aMain = .ok route →
    g.routeCapacity ≤ 64*stagePages →
    (1 < g.aTopology.r → g.radixCapacity ≤ 64*radixPages) →
    pageRecords aTierPages = inp.aTier →
    pageRecords (NativeMatchDirectJobTrace.allocatedRaw g word inp stagePages radixPages aTierPages) =
      DirectJob.aResidual (DirectJob.analyticalA g word inp.aMain).state inp.aTier) ∧
  (∀ (g : DirectJob.Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
      (b : DirectJob.Table) (sources raw : List Page),
    g.ranges = .direct → pageRecords sources = b.tier →
    pageRecords raw = DirectJob.aResidual (DirectJob.analyticalA g word inp.aMain).state inp.aTier →
    (finishExact g.finishTopology word b.bLanes
      (NativeMatchDirectJobTrace.initialGhost g word inp b sources raw)).state =
      (DirectJob.analyticalInsert g word b (DirectJob.analyticalA g word inp.aMain).state.main
        (DirectJob.distributeA g word (DirectJob.aOperational
          (DirectJob.analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves).state)

/-- Pool and finish share one exact pre-state inventory. The initial physical
pool sources/targets are inputs, never reconstructed from surviving compact
records. Arbitrary page count includes the production four-group direct case. -/
def NativeMatchDirectJobTrace_statement : Prop :=
  ∀ (_bridge : NativeMatchLanesBridge_statement) (_retained : NativeMatchRetained_statement)
    (stored : LogicalKey → Stored) (g : DirectJob.Geometry) (oldWord word : LogicalKey → Nat)
    (inp : DirectJob.Inputs) (b : DirectJob.Table) (sources raw : List Page),
    g.Valid → 2 ≤ g.digit → inp.Valid g oldWord → DirectJob.buildB g word inp = .ok b →
    g.bCapacity ≤ 64 → pageRecords sources = b.tier →
    pageRecords raw = DirectJob.aResidual (DirectJob.analyticalA g word inp.aMain).state inp.aTier →
    ((∀ e ∈ NativeMatchDirectJobTrace.events g word inp b sources raw, ¬e.bad stored) →
      ∀ n, ((List.range g.finishTopology.U).take n).foldl
        (bucketNative stored g.finishTopology word b.bLanes)
        (NativeMatchDirectJobTrace.initialNative stored g word inp b sources raw) =
      ((List.range g.finishTopology.U).take n).foldl (bucketExact g.finishTopology word b.bLanes)
        (NativeMatchDirectJobTrace.initialGhost g word inp b sources raw)) ∧
    ((∃ n, ((List.range g.finishTopology.U).take n).foldl
        (bucketNative stored g.finishTopology word b.bLanes)
        (NativeMatchDirectJobTrace.initialNative stored g word inp b sources raw) ≠
      ((List.range g.finishTopology.U).take n).foldl (bucketExact g.finishTopology word b.bLanes)
        (NativeMatchDirectJobTrace.initialGhost g word inp b sources raw)) →
      ∃ e ∈ NativeMatchDirectJobTrace.events g word inp b sources raw, e.bad stored)

/-- Both class directions execute from the same physical pre-state. The
exact reference's fit and B-source disjointness suffice for complete drain
agreement, including holes and final unused padding. -/
def NativeMatchDrainJobTrace_statement : Prop :=
  ∀ (_bridge : NativeMatchClassBridge_statement) (stored : LogicalKey → Stored)
    (shedPages tierPages : Nat) (state : SFin),
    state.ins.length ≤ 64*shedPages → (firstDrain state).length ≤ 64*tierPages →
    occupied (sDrain state).1 ≤ 64*tierPages →
    (∀ r ∈ state.ins, r.key ∉ state.bcopy.flatten.map Rec.key) →
    ((∀ e ∈ drainEvents shedPages tierPages state, ¬e.bad stored) →
      drainNative stored shedPages tierPages state =
        (sDrain state).1 ++ List.replicate (64*tierPages - (sDrain state).1.length) none) ∧
    (drainNative stored shedPages tierPages state ≠
        (sDrain state).1 ++ List.replicate (64*tierPages - (sDrain state).1.length) none →
      ∃ e ∈ drainEvents shedPages tierPages state, e.bad stored)

/-- Top replay includes tombstone resolution before insertion and subsequent
nonmatching offers. Its original B page layout is retained throughout. -/
def NativeMatchTopJobTrace_statement : Prop :=
  ∀ (_bridge : NativeMatchLanesBridge_statement) (_retained : NativeMatchRetained_statement)
    (stored : LogicalKey → Stored) (g : TopGeom) (unsh : Rec → Bool)
    (word : LogicalKey → Nat) (inp : TopInputs) (bpages : List Page),
    g.C = 64 → TopShape g unsh word inp → g.dfs = true →
    firstFailure g.toGeom g.caps (topReference g unsh word inp).trace = none →
    pageRecords bpages = inp.bTier →
    let ghost := NativeMatchTopJobTrace.initialGhost g unsh word inp bpages
    ((∀ e ∈ NativeMatchTopJobTrace.finishEvents g word inp.bMain ghost, ¬e.bad stored) →
      ∀ n, ((List.range g.U).take n).foldl
        (NativeMatchTopJobTrace.bucketNative stored g word inp.bMain) ghost =
        ((List.range g.U).take n).foldl (NativeMatchTopJobTrace.bucketExact g word inp.bMain) ghost) ∧
    ((∃ n, ((List.range g.U).take n).foldl
        (NativeMatchTopJobTrace.bucketNative stored g word inp.bMain) ghost ≠
        ((List.range g.U).take n).foldl (NativeMatchTopJobTrace.bucketExact g word inp.bMain) ghost) →
      ∃ e ∈ NativeMatchTopJobTrace.finishEvents g word inp.bMain ghost, e.bad stored)

end RebuildBound.Spec

namespace RebuildBound.Spec
open Model NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchJobTrace

/-- Complete pool/finish/class-drain matching refinement of the actual
successful separated reference job. All finite storage fits and source
uniqueness facts are derived from that job's checks and input invariants. -/
def NativeMatchSeparatedFullJob_statement : Prop :=
  ∀ (_bridge : NativeMatchLanesBridge_statement) (_retained : NativeMatchRetained_statement)
    (_classes : NativeMatchClassBridge_statement) (stored : LogicalKey → Stored)
    (rule : CapRule) (g : SepGeom) (oldWord word : LogicalKey → Nat)
    (inp : SInputs) (ops : List (Nat × Nat)) (aTier : List Page),
    rule.Valid → g.Valid → g.C = 64 → SInputShape g oldWord word inp → SValidSched g ops →
    sFirstFailure g (sReferenceWith rule g word inp ops).trace = none →
    pageRecords aTier = inp.aTier → (∀ page ∈ inp.bTier, page.length ≤ 64) →
    let expected : Output := ⟨(sReferenceWith rule g word inp ops).output.main,
      (sReferenceWith rule g word inp ops).output.tier ++
        List.replicate (64*g.tierPages - (sReferenceWith rule g word inp ops).output.tier.length) none⟩
    ((∀ e ∈ separatedEvents rule g word inp ops aTier, ¬e.bad stored) →
      separatedNative stored rule g word inp ops aTier = expected) ∧
    (separatedNative stored rule g word inp ops aTier ≠ expected →
      ∃ e ∈ separatedEvents rule g word inp ops aTier, e.bad stored)

/-- Actual writer construction has finite dependence on the logical routing
tape. Neither a stored-key map nor an inventory-independence assumption is an
argument of these exact transitions or comparison inventories. -/
def NativeMatchJobFiniteRead_statement : Prop :=
  (∀ (cfg : Model.Config) (level ordinal : Nat) (g : SepGeom)
      (bMain : List Bucket) (ghost : FinishGhost),
    IdealKey.FiniteRead (fun tape => finishEvents g
      (Model.Hierarchy.jobWord cfg (IdealHierarchy.words tape) level ordinal) bMain ghost) ∧
    IdealKey.FiniteRead (fun tape => finishExact g
      (Model.Hierarchy.jobWord cfg (IdealHierarchy.words tape) level ordinal) bMain ghost)) ∧
  (∀ (cfg : Model.Config) (level ordinal : Nat) (g : TopGeom)
      (bMain : List Bucket) (ghost : NativeMatchTopJobTrace.Ghost),
    IdealKey.FiniteRead (fun tape => NativeMatchTopJobTrace.finishEvents g
      (Model.Hierarchy.jobWord cfg (IdealHierarchy.words tape) level ordinal) bMain ghost) ∧
    IdealKey.FiniteRead (fun tape => NativeMatchTopJobTrace.finishExact g
      (Model.Hierarchy.jobWord cfg (IdealHierarchy.words tape) level ordinal) bMain ghost))

end RebuildBound.Spec

namespace RebuildBound.Spec
open Model NativeMatch NativeMatch.Lanes NativeMatchTrace

def NativeMatchTopFullJob_statement : Prop :=
  ∀ (_bridge : NativeMatchLanesBridge_statement) (_retained : NativeMatchRetained_statement)
    (_classes : NativeMatchClassBridge_statement) (stored : LogicalKey → Stored)
    (g : TopGeom) (unsh : Rec → Bool) (word : LogicalKey → Nat) (inp : TopInputs)
    (carryPages bpages : List Page),
    g.Valid → g.C = 64 → TopShape g unsh word inp → g.dfs = true →
    firstFailure g.toGeom g.caps (topReference g unsh word inp).trace = none →
    pageRecords carryPages = inp.carry → pageRecords bpages = inp.bTier →
    let expected : Output := ⟨(topReference g unsh word inp).output.main,
      (topReference g unsh word inp).output.tier ++
        List.replicate (64*g.tierPages - (topReference g unsh word inp).output.tier.length) none⟩
    ((∀ e ∈ NativeMatchTopJobTrace.events g unsh word inp carryPages bpages, ¬e.bad stored) →
      NativeMatchTopJobTrace.native stored g unsh word inp carryPages bpages = expected) ∧
    (NativeMatchTopJobTrace.native stored g unsh word inp carryPages bpages ≠ expected →
      ∃ e ∈ NativeMatchTopJobTrace.events g unsh word inp carryPages bpages, e.bad stored)

end RebuildBound.Spec

namespace RebuildBound.Spec
open Model Model.DirectJob NativeMatch NativeMatch.Lanes NativeMatchTrace NativeMatchDirectJobTrace

/-- Direct plans retain their original pool groups through matching and
insertion. The final class drain is checked against the direct interpreter's
actual allocation checks, then erases to its ordered analytical output. -/
def NativeMatchDirectFullJob_statement : Prop :=
  ∀ (_bridge : NativeMatchLanesBridge_statement) (_retained : NativeMatchRetained_statement)
    (_classes : NativeMatchClassBridge_statement) (stored : LogicalKey → Stored)
    (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (b : Table)
    (sources raw : List Page) (shedPages tierPages : Nat),
    g.Valid → 2 ≤ g.digit → inp.Valid g oldWord → buildB g word inp = .ok b →
    g.ranges = .direct → g.bCapacity ≤ 64 → pageRecords sources = b.tier →
    pageRecords raw = aResidual (analyticalA g word inp.aMain).state inp.aTier →
    DirectJob.firstFailure (analyticalFinish g word b (analyticalA g word inp.aMain).state.main
      (distributeA g word (aOperational (analyticalA g word inp.aMain).state inp.aTier b.tier)).leaves).trace = none →
    g.insertionCapacity ≤ 64*shedPages → g.outputCapacity ≤ 64*tierPages →
    let expected : Output := ⟨(finishState g word inp b).main,(sDrain (finishState g word inp b)).1 ++
      List.replicate (64*tierPages - (sDrain (finishState g word inp b)).1.length) none⟩
    ((∀ e ∈ fullEvents g word inp b sources raw shedPages tierPages, ¬e.bad stored) →
      native stored g word inp b sources raw shedPages tierPages = expected) ∧
    (native stored g word inp b sources raw shedPages tierPages ≠ expected →
      ∃ e ∈ fullEvents g word inp b sources raw shedPages tierPages, e.bad stored)

end RebuildBound.Spec

namespace RebuildBound.Spec
open Model NativeMatchTrace NativeMatchJobTrace

def NativeMatchFullJobFiniteRead_statement : Prop :=
  (∀ (cfg : Model.Config) (level ordinal : Nat) (g : SepGeom) (inp : SInputs)
      (ops : List (Nat × Nat)) (aTier : List Page),
    IdealKey.FiniteRead (fun tape => separatedEvents engineRule g
      (Model.Hierarchy.jobWord cfg (IdealHierarchy.words tape) level ordinal) inp ops aTier)) ∧
  (∀ (cfg : Model.Config) (level ordinal : Nat) (g : TopGeom) (unsh : Rec → Bool)
      (inp : TopInputs) (carryPages bpages : List Page),
    IdealKey.FiniteRead (fun tape => NativeMatchTopJobTrace.events g unsh
      (Model.Hierarchy.jobWord cfg (IdealHierarchy.words tape) level ordinal) inp carryPages bpages))

end RebuildBound.Spec

namespace RebuildBound.Spec
open Model NativeMatchTrace
/-- The complete direct observer also has finite routing dependence. Its raw
physical page arguments are fixed here; composing the actual allocated route
observer uses the same finite-read bind operation. -/
def NativeMatchDirectJobFiniteRead_statement : Prop :=
  ∀ (cfg : Model.Config) (level ordinal : Nat) (g : DirectJob.Geometry)
    (inp : DirectJob.Inputs) (b : DirectJob.Table) (sources raw : List Page)
    (shedPages tierPages : Nat),
    IdealKey.FiniteRead (fun tape => NativeMatchDirectJobTrace.fullEvents g
      (Model.Hierarchy.jobWord cfg (IdealHierarchy.words tape) level ordinal)
      inp b sources raw shedPages tierPages)
end RebuildBound.Spec
