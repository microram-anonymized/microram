import RebuildBound.Spec.Model.DirectJobA
import RebuildBound.Spec.Model.DirectJobB

/-! Core-only separated finish. Immutable B identities remain available after
shedding. Logical insertion units are complete source buckets; private offers
and the last-way check form one atomic reference transition. A leftovers drain
before ranked resolution against the insertion stash. -/
namespace RebuildBound.Model.DirectJob

/-- Topology only; checks use direct slot capacities. Direct plans use leaf zero. -/
def Geometry.finishTopology (g : Geometry) : SepGeom :=
  match g.ranges with
  | .direct => { g.aTopology with I := g.K + 3, rangeBits := 0 }
  | .dfs i r _ => { g.aTopology with I := i, rangeBits := r }

/-- Restore implicit trailing holes without moving records. -/
def Table.bLanes (b : Table) : List Bucket :=
  b.main.map fun rs => rs.map some ++ List.replicate (64 - rs.length) none

def finishInitial (b : Table) (main : List Bucket) (leaves : List (List Rec)) : SFin :=
  ⟨main, [], leaves, [b.tier], []⟩

/-- B source identities are immutable, independent of main and insertion stash.
Native last-way/fallback check normalization remains a separate obligation. -/
def finishTransition (g : Geometry) (word : LogicalKey → Nat) (b : Table)
    (ordinal : Nat) (st : SFin) (source : Nat) : SFin × CheckEvent :=
  let next := sInsertBucket g.finishTopology word b.bLanes source st
  (next, ⟨⟨.finish, .insertion, ordinal⟩, next.ins.length, g.insertionCapacity⟩)

def analyticalInsert (g : Geometry) (word : LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec)) : AnalyticalSteps SFin :=
  stepsAnalytical (finishTransition g word b) 0 (finishInitial b main leaves) (List.range g.U)

def insertBounded (g : Geometry) (word : LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec)) : Except CheckEvent SFin :=
  stepsBounded (finishTransition g word b) 0 (finishInitial b main leaves) (List.range g.U)

/-- A class first, then the standalone B tier. Empty logical chunks count. -/
def finishChunks (st : SFin) : List (List (Rec × Bool)) :=
  (st.leaves.map fun rs => rs.map fun x => (x, true)) ++
    st.bcopy.map fun rs => rs.map fun x => (x, false)

/-- Shed B wins over A; swept B wins over insertion records. Preserve holes.
Neither values nor tombstone flags affect freshness. -/
def resolveLeftovers (ins : List Rec) (tier : List (Option (Rec × Bool))) :
    List (Option (Rec × Bool)) × List Rec :=
  let cleared := tier.map fun slot =>
    slot.filter fun p => !(p.2 && (ins.map Rec.key).contains p.1.key)
  let bKeys := ((cleared.filterMap id).filter fun p => !p.2).map fun p => p.1.key
  (cleared, ins.filter fun x => !bKeys.contains x.key)

/-- Fill holes made by rank resolution before extending the tier. -/
def finishDrainTransition (g : Geometry) (ordinal : Nat) (ins : List Rec)
    (tier : List (Option (Rec × Bool))) : Bucket × CheckEvent :=
  let resolved := resolveLeftovers ins tier
  let next := appendFill resolved.1 (resolved.2.map fun x => (x, false))
  (next.map fun slot => slot.map Prod.fst,
    ⟨⟨.drain, .outputTier, ordinal⟩, occupied next, g.outputCapacity⟩)

/-- Drain events of a separated drain trace, numbered in order, against the
direct output tier's slot capacity. -/
def drainEvents (g : Geometry) (trace : List (STest × Nat)) : List CheckEvent :=
  trace.zipIdx.map fun p => ⟨⟨.drain, .outputTier, p.2⟩, p.1.2, g.outputCapacity⟩

def finishDrainBounded (g : Geometry) (st : SFin) : Except CheckEvent Bucket :=
  let chunks := finishChunks st
  match drainBounded .drain .outputTier g.outputCapacity 0 [] chunks with
  | .error e => .error e
  | .ok first =>
    let last := finishDrainTransition g chunks.length st.ins (first.map some)
    if last.2.passed then .ok last.1 else .error last.2

/-- Unlimited continuation is not a publishable table. -/
structure AnalyticalFinish where
  state : SFin
  tier : Bucket
  trace : List CheckEvent

/-- The tier and the drain events are the separated drain's (`sDrain`). -/
def analyticalFinish (g : Geometry) (word : LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec)) : AnalyticalFinish :=
  let ins := analyticalInsert g word b main leaves
  let dr := sDrain ins.state
  ⟨ins.state, dr.1, ins.trace ++ drainEvents g dr.2⟩

/-- Pad trailing output lanes after success, preserving all internal holes. -/
def finishOutput (g : Geometry) (main : List Bucket) (tier : Bucket) : Output :=
  ⟨main, tier ++ List.replicate (g.outputCapacity - tier.length) none⟩

def finishBounded (g : Geometry) (word : LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec)) : Except CheckEvent Output :=
  match insertBounded g word b main leaves with
  | .error e => .error e
  | .ok st => match finishDrainBounded g st with
    | .error e => .error e
    | .ok tier => .ok (finishOutput g st.main tier)

inductive LaneResult where
  | rejected (reason : Rejection)
  | failed (event : CheckEvent)
  | published (table : Output)

/-- Executable composition. Correctness, failure containment, and resumable
execution are proved in `Proofs/DirectJob`, `Proofs/DirectJobFailure`, and
`Proofs/DirectJobResume`. -/
def runJob (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : Inputs) : LaneResult :=
  if ¬ g.Valid then .rejected .geometry
  else if ¬ inp.Valid g oldWord then .rejected .inputs
  else if g.digit = 1 then
    match buildB g word inp with
    | .error e => .failed e
    | .ok b => .published (finishOutput g b.bLanes (b.tier.map some))
  else match prepareA g word inp.aMain with
    | .error e => .failed e
    | .ok a => match buildB g word inp with
      | .error e => .failed e
      | .ok b => match distributeABounded g word (aOperational a inp.aTier b.tier) with
        | .error e => .failed e
        | .ok leaves => match finishBounded g word b a.main leaves with
          | .error e => .failed e
          | .ok out => .published out

end RebuildBound.Model.DirectJob
