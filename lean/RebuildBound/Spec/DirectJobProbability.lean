import RebuildBound.Spec.DirectJobFailure
import RebuildBound.Spec.P7

/-! Direct-job B count identity and the failure union bound over a finite law.
Native source laws and selected numerical rows remain explicit consumer
obligations. -/
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace RebuildBound.Spec
open Model Model.DirectJob

def directBCount (g : Geometry) (word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (v : Fin g.U) : Nat :=
  ((DirectPrefix.winners inp.bRecords).filter
    (fun r => DirectPrefix.cachedHome word g.U r == v.val)).length

def DirectJobBCount_statement : Prop :=
  ∀ g word inp, bExcess g word inp = ∑ v, (directBCount g word inp v - 64)

/-- Compose failure containment with B, A-route/range and final-union budgets.
No independence between failure events or probability normalization is needed
for this final union bound. A's event includes old-tier fit, as required by the shared SG2 adapter;
structural validity of a failed job supplies that fit. -/
def DirectJobFailureProbability_statement : Prop := by
  classical
  exact ∀ {Hist Word : Type} [Fintype Hist] [Fintype Word]
    (weight : Hist → ℝ≥0∞) (wordFn : Word → LogicalKey → Nat) (g : Geometry)
    (oldWord : Hist → LogicalKey → Nat) (inputs : Hist → (LogicalKey → Nat) → DirectJob.Inputs)
    (bB bA bUnion : ℝ≥0∞),
    (∑ hist, weight hist * ((Fintype.card Word : ℝ≥0∞)⁻¹ *
      ∑ h, if g.bCapacity < bExcess g (wordFn h) (inputs hist (wordFn h)) then 1 else 0)) ≤ bB →
    (∑ hist, weight hist * ((Fintype.card Word : ℝ≥0∞)⁻¹ *
      ∑ h, if (inputs hist (wordFn h)).aTier.length ≤ g.aTierCapacity ∧
        (aRouteWitness g (wordFn h) (inputs hist (wordFn h)) ∨
          aRangeWitness g (wordFn h) (inputs hist (wordFn h))) then 1 else 0)) ≤ bA →
    (∑ hist, weight hist * ((Fintype.card Word : ℝ≥0∞)⁻¹ *
      ∑ h, if g.outputCapacity < (inputs hist (wordFn h)).excess g (wordFn h) then 1 else 0)) ≤ bUnion →
    (∑ hist, weight hist * ((Fintype.card Word : ℝ≥0∞)⁻¹ *
      ∑ h, if ∃ e, runJob g (oldWord hist) (wordFn h) (inputs hist (wordFn h)) = .failed e
        then 1 else 0)) ≤ bB + bA + bUnion

end RebuildBound.Spec
