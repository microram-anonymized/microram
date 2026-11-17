import RebuildBound.Spec.Model.DirectJobFinish

/-! Execution and ranked-drain interface for the finish increment. These
statements do not assert whole-finish conservation or exact excess. -/
namespace RebuildBound.Spec
open Model Model.DirectJob

def DirectJobFinishTopology_statement : Prop :=
  ∀ g : Geometry, g.Valid → 2 ≤ g.digit →
    g.finishTopology.Valid ∧ g.finishTopology.d = g.digit ∧
    g.finishTopology.N = g.outputHomes ∧
    (∀ t, g.finishTopology.homeOf t = g.home t)

def DirectJobFinishDistribution_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (pool : List Rec), g.Valid → 2 ≤ g.digit →
    sLeaves g.finishTopology word pool = (distributeA g word pool).leaves

def DirectJobFinishInsertRefinement_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec)),
    (analyticalInsert g word b main leaves).state =
      sFinish g.finishTopology word ⟨[], [], b.bLanes, [b.tier]⟩ main leaves

def DirectJobFinishInsertSimulation_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec)),
    insertBounded g word b main leaves =
      match firstFailure (analyticalInsert g word b main leaves).trace with
      | some e => .error e
      | none => .ok (analyticalInsert g word b main leaves).state

/-- The bounded drain is the separated ranked drain stopped at its first
failing check: exact ordered lanes and events. -/
def DirectJobFinishDrainSimulation_statement : Prop :=
  ∀ (g : Geometry) (st : SFin),
    finishDrainBounded g st =
      match firstFailure (drainEvents g (sDrain st).2) with
      | some e => .error e
      | none => .ok (sDrain st).1

def DirectJobFinishSimulation_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec)),
    finishBounded g word b main leaves =
      match firstFailure (analyticalFinish g word b main leaves).trace with
      | some e => .error e
      | none => .ok (finishOutput g (analyticalFinish g word b main leaves).state.main
          (analyticalFinish g word b main leaves).tier)

def DirectJobFinishFailureCheck_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec)) (e : CheckEvent),
    finishBounded g word b main leaves = .error e →
    e ∈ (analyticalFinish g word b main leaves).trace ∧ e.capacity < e.occupancy ∧
    ((e.id.phase = .finish ∧ e.id.site = .insertion ∧ e.capacity = g.insertionCapacity) ∨
     (e.id.phase = .drain ∧ e.id.site = .outputTier ∧ e.capacity = g.outputCapacity))

/-- Padding preserves full records and gives exact valid lane widths. -/
def DirectJobFinishBLanes_statement : Prop :=
  ∀ b : Table, (∀ rs ∈ b.main, rs.length ≤ 64) →
    b.bLanes.length = b.main.length ∧ (∀ bucket ∈ b.bLanes, bucket.length = 64) ∧
    b.bLanes.map Bucket.recs = b.main

/-- Occupancy checks plus bounded preliminary drainage bound allocated lanes,
including the holes left by ranked duplicate resolution. -/
def DirectJobFinishDrainWidth_statement : Prop :=
  ∀ (g : Geometry) (st : SFin) (tier : Bucket),
    finishDrainBounded g st = .ok tier → tier.length ≤ g.outputCapacity

def DirectJobFinishOutputWidth_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (b : Table)
    (main : List Bucket) (leaves : List (List Rec)) (out : Output),
    finishBounded g word b main leaves = .ok out → out.tier.length = g.outputCapacity

end RebuildBound.Spec
