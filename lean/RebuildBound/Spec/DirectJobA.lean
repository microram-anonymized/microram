import RebuildBound.Spec.Model.DirectJobA

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- No unproved geometry adapter or route-correctness hypothesis. -/
def DirectJobATopology_statement : Prop :=
  ∀ g : Geometry, g.Valid → 2 ≤ g.digit →
    g.aTopology.Valid ∧ g.aTopology.d = g.digit ∧ g.aTopology.N = g.outputHomes ∧
    (∀ word, g.aTopology.homeOf word = g.home word)

def DirectJobARefinement_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (aMain : List Bucket), g.digit ≠ 1 →
    (analyticalA g word aMain).state =
      sRouteWith engineRule g.aTopology word aMain (engineOps g.aTopology)

/-- Exact logical first failure and successful state; no publication type here. -/
def DirectJobASimulation_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (aMain : List Bucket),
    prepareA g word aMain =
      match firstFailure (analyticalA g word aMain).trace with
      | some e => .error e
      | none => .ok (analyticalA g word aMain).state

/-- Exact direct-branch behavior, including pools larger than one page. -/
def DirectJobADirect_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (pool : List Rec), g.ranges = .direct →
    distributeA g word pool = ⟨[pool], []⟩ ∧ distributeABounded g word pool = .ok [pool]

/-- Stable DFS contents and exact padded node capacities/order. -/
def DirectJobADfs_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (pool : List Rec) (i r p : Nat),
    g.ranges = .dfs i r p →
    (distributeA g word pool).leaves =
      (List.range (2 ^ r)).map (fun v => pool.filter fun x => g.home (word x.key) / 2 ^ i == v) ∧
    (distributeA g word pool).trace =
      ((List.range (r + 1)).flatMap fun d => (List.range (2 ^ d)).map fun v => (d, v)).zipIdx.map
        (fun (node, ordinal) => ⟨⟨.distributeA, .dfs node.1 node.2, ordinal⟩,
          (pool.filter fun x => g.home (word x.key) / 2 ^ i / 2 ^ (r - node.1) == node.2).length,
          min p (64 * 2 ^ (r - node.1))⟩)

def DirectJobAFailureCheck_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (aMain : List Bucket) (e : CheckEvent),
    prepareA g word aMain = .error e →
    e ∈ (analyticalA g word aMain).trace ∧ e.capacity < e.occupancy ∧
    e.id.phase = .prepareA ∧
    ((∃ bit cont, e.id.site = .route bit cont ∧ e.capacity = g.routeCapacity) ∨
      (e.id.site = .radix ∧ e.capacity = g.radixCapacity))

end RebuildBound.Spec
