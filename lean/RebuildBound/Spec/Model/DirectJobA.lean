import RebuildBound.Spec.Model.DirectJobContract

/-! Core-only A preparation and residual distribution. These phases reuse the
separated model's ordered scalar primitives and use direct slot capacities for
operational checks. The bounded interpreter checks each transition before
proceeding. -/
namespace RebuildBound.Model.DirectJob

/-- Topology only: capacity fields are deliberately unused. The padded envelope
covers every supported radix and is not the operational range plan. B's one
standalone tier page (`bTierPages = 1`) is the separated input shape. -/
def Geometry.aTopology (g : Geometry) : SepGeom :=
  ⟨64, g.K, val2 g.digit, g.digit / 2 ^ val2 g.digit,
    3, g.K + val2 g.digit, 0, 0, 1, 0⟩

inductive AOp where
  | pair (bit index : Nat)
  | radix (index : Nat)
  deriving Repr, DecidableEq

def aOps (g : Geometry) : List AOp :=
  if g.digit = 1 then [] else
  (engineOps g.aTopology).map (fun o => .pair o.1 o.2) ++
    if 1 < g.aTopology.r then (List.range g.aTopology.blk).map AOp.radix else []

/-- No B records, keys or source units are arguments of preparation. -/
def aInitial (g : Geometry) (aMain : List Bucket) : SRoute :=
  sRouteInit g.aTopology aMain

def aTransition (g : Geometry) (word : LogicalKey → Nat) (ordinal : Nat)
    (st : SRoute) (op : AOp) : SRoute × CheckEvent :=
  match op with
  | .pair bit index =>
    let next := sPairStep engineRule g.aTopology word bit index st
    (next, ⟨⟨.prepareA, .route bit (decide (index < 2 ^ bit)), ordinal⟩,
      (next.stash.getD bit []).length, g.routeCapacity⟩)
  | .radix index =>
    let next := radixStep g.aTopology word index st
    (next, ⟨⟨.prepareA, .radix, ordinal⟩, next.radix.length, g.radixCapacity⟩)

structure AnalyticalSteps (σ : Type) where
  state : σ
  trace : List CheckEvent

/-- Shared logical-step machinery, with explicit next-operation cursor. -/
def stepsAnalytical {σ α : Type} (step : Nat → σ → α → σ × CheckEvent) :
    Nat → σ → List α → AnalyticalSteps σ
  | _, st, [] => ⟨st, []⟩
  | ordinal, st, op :: ops =>
    let next := step ordinal st op
    let tail := stepsAnalytical step (ordinal + 1) next.1 ops
    ⟨tail.state, next.2 :: tail.trace⟩

def stepsBounded {σ α : Type} (step : Nat → σ → α → σ × CheckEvent) :
    Nat → σ → List α → Except CheckEvent σ
  | _, st, [] => .ok st
  | ordinal, st, op :: ops =>
    let next := step ordinal st op
    if next.2.passed then stepsBounded step (ordinal + 1) next.1 ops else .error next.2

def analyticalA (g : Geometry) (word : LogicalKey → Nat) (aMain : List Bucket) : AnalyticalSteps SRoute :=
  stepsAnalytical (aTransition g word) 0 (aInitial g aMain) (aOps g)

def prepareA (g : Geometry) (word : LogicalKey → Nat) (aMain : List Bucket) : Except CheckEvent SRoute :=
  stepsBounded (aTransition g word) 0 (aInitial g aMain) (aOps g)

/-- Stable order: stage stashes in bit order, radix shed, then old tier.
Retained even if preparation or B production overflows. -/
def aResidual (st : SRoute) (aTier : List Rec) : List Rec :=
  st.stash.flatten ++ st.radix ++ aTier

/-- Only B-tier freshness is applied at distribution. The finish phase retains
the original B-main identities for insertion and ranked resolution. -/
def aOperational (st : SRoute) (aTier bTier : List Rec) : List Rec :=
  (aResidual st aTier).filter fun x => !(bTier.map Rec.key).contains x.key

structure ADistribution where
  leaves : List (List Rec)
  trace : List CheckEvent
  deriving Repr, DecidableEq

/-- Direct offers use one ordered pool with no distributor capacity event.
DFS uses stable range partitions and a depth-major padded logical trace. -/
def distributeA (g : Geometry) (word : LogicalKey → Nat) (pool : List Rec) : ADistribution :=
  match g.ranges with
  | .direct => ⟨[pool], []⟩
  | .dfs i r p =>
    let range := fun x : Rec => g.home (word x.key) / 2 ^ i
    let nodes := (List.range (r + 1)).flatMap fun depth =>
      (List.range (2 ^ depth)).map fun pre => (depth, pre)
    ⟨(List.range (2 ^ r)).map (fun v => pool.filter fun x => range x == v),
      nodes.zipIdx.map fun (node, ordinal) =>
        ⟨⟨.distributeA, .dfs node.1 node.2, ordinal⟩,
          (pool.filter fun x => range x / 2 ^ (r - node.1) == node.2).length,
          min p (64 * 2 ^ (r - node.1))⟩⟩

/-- Distribution is observationally read-only; failed checks expose no leaves. -/
def distributeABounded (g : Geometry) (word : LogicalKey → Nat) (pool : List Rec) :
    Except CheckEvent (List (List Rec)) :=
  let d := distributeA g word pool
  match firstFailure d.trace with
  | some e => .error e
  | none => .ok d.leaves

end RebuildBound.Model.DirectJob
