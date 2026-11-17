import RebuildBound.Spec.Model.DirectJobFailure

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Success recovers the same full B records; failure retains the first logical
check from the unlimited continuation. -/
def DirectJobBAnalytical_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs),
    buildB g word inp =
      match firstFailure (analyticalB g word inp).trace with
      | some e => .error e
      | none => .ok (analyticalBTable g word inp)

/-- Exact whole-job simulation includes original structural rejections and all
logical check identities, occupancies and capacities, in native phase order. -/
def DirectJobSimulation_statement : Prop :=
  ∀ (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs),
    runJob g oldWord word inp =
      if ¬ g.Valid then .rejected .geometry
      else if ¬ inp.Valid g oldWord then .rejected .inputs
      else match firstFailure (analyticalJob g word inp).trace with
        | some e => .failed e
        | none => .published (finishOutput g (analyticalJob g word inp).main
            (analyticalJob g word inp).tier)

/-- Every operational DFS overflow is dominated by the corresponding check on
completed unfiltered A residuals, regardless of B tier identities or capacity. -/
def DirectJobRangeFailure_statement : Prop :=
  ∀ (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (bTier : List Rec) (e : CheckEvent),
    distributeABounded g word
      (aOperational (analyticalA g word inp.aMain).state inp.aTier bTier) = .error e →
    aRangeWitness g word inp

/-- Complete first-failure identity, failed capacity, and absence of publication.
Invalid structure is rejection, not a capacity failure. -/
def DirectJobFirstFailure_statement : Prop :=
  ∀ (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (e : CheckEvent),
    (runJob g oldWord word inp = .failed e ↔
      g.Valid ∧ inp.Valid g oldWord ∧
        firstFailure (analyticalJob g word inp).trace = some e) ∧
    (runJob g oldWord word inp = .failed e →
      e ∈ (analyticalJob g word inp).trace ∧ e.capacity < e.occupancy ∧
      ∀ out, runJob g oldWord word inp ≠ .published out)

/-- Unconditional witness containment with no internal phase-correctness premise.
The A witnesses still require their later probability/shadow adapters. -/
def DirectJobFailureContainment_statement : Prop :=
  ∀ (g : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (e : CheckEvent),
    runJob g oldWord word inp = .failed e → failureWitness g word inp

end RebuildBound.Spec
