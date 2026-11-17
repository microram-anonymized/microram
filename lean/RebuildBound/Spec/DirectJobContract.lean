import RebuildBound.Spec.Model.DirectJobContract

namespace RebuildBound.Spec
open Model Model.DirectJob

def DirectJobHome_statement : Prop :=
  ∀ (g : Geometry) (word : Nat), g.home word % g.U = word % g.U

def DirectJobExamples_statement : Prop :=
  ∀ digit ∈ [1, 2, 3], (exampleGeometry digit).Valid ∧
    (exampleInputs digit).Valid (exampleGeometry digit) (fun _ => 0)

def DirectJobDrainErasure_statement : Prop :=
  ∀ (α : Type) (phase : Phase) (site : Site) (capacity ordinal : Nat)
    (state : List α) (chunks : List (List α)),
    (drainBounded phase site capacity ordinal state chunks).toOption =
      DirectDrain.run capacity state chunks

/-- Simulation includes exact first logical failure identity, and exact
successful state. Capacities are identical in both interpreters. -/
def DirectJobDrainSimulation_statement : Prop :=
  ∀ (α : Type) (phase : Phase) (site : Site) (capacity ordinal : Nat)
    (state : List α) (chunks : List (List α)),
    drainBounded phase site capacity ordinal state chunks =
      match firstFailure (drainAnalytical phase site capacity ordinal state chunks).trace with
      | some e => .error e
      | none => .ok (drainAnalytical phase site capacity ordinal state chunks).records

def DirectJobDrainRecords_statement : Prop :=
  ∀ (α : Type) (phase : Phase) (site : Site) (capacity ordinal : Nat)
    (state : List α) (chunks : List (List α)),
    (drainAnalytical phase site capacity ordinal state chunks).records = state ++ chunks.flatten

def DirectJobDrainFailureCheck_statement : Prop :=
  ∀ (α : Type) (phase : Phase) (site : Site) (capacity ordinal : Nat)
    (state : List α) (chunks : List (List α)) (e : CheckEvent),
    drainBounded phase site capacity ordinal state chunks = .error e →
    e.capacity = capacity ∧ capacity < e.occupancy ∧ e.id.phase = phase ∧ e.id.site = site

end RebuildBound.Spec
