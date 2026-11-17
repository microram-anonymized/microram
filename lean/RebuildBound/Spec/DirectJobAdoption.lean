import RebuildBound.Spec.Model.DirectJobChain
import RebuildBound.Spec.DirectJobPublication
import RebuildBound.Spec.DirectJobSelected

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Empty/direct initialization has no old records or old-home premise. -/
def DirectJobEmptyInput_statement : Prop :=
  ∀ (g : Geometry) (oldWord : LogicalKey → Nat) (units : List Bucket),
    g.digit = 1 → (∀ u ∈ units, (u.recs.map Rec.key).Nodup) →
    (adopt emptyOutput units).Valid g oldWord

/-- Successful output is a structurally valid old table for the next digit.
There is no new capacity check: the preceding output width fits the next A tier.
This does not condition or establish a probabilistic history law. -/
def DirectJobAdoption_statement : Prop :=
  ∀ (g next : Geometry) (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs)
    (out : Output) (units : List Bucket),
    runJob g oldWord word inp = .published out →
    next.K = g.K → next.digit = g.digit + 1 →
    g.outputCapacity ≤ next.aTierCapacity →
    (∀ u ∈ units, (u.recs.map Rec.key).Nodup) →
    (adopt out units).Valid next word

/-- The selected rows discharge the consecutive-digit geometry/capacity bridge. -/
def DirectJobSelectedAdoption_statement : Prop :=
  ∀ d, 1 ≤ d → d < 8 →
    ∀ (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (out : Output)
      (units : List Bucket),
    runJob (selectedDirectGeometry d) oldWord word inp = .published out →
    (∀ u ∈ units, (u.recs.map Rec.key).Nodup) →
    (selectedDirectGeometry (d + 1)).Valid ∧
      (adopt out units).Valid (selectedDirectGeometry (d + 1)) word

/-- Consecutive selected digits, each with its own current word family and
chronological fresh units. This models one non-wrapping level-one digit cycle. -/
def selectedChainJobs (first : Nat) : List ((LogicalKey → Nat) × List Bucket) → List ChainJob
  | [] => []
  | (word, units) :: rest =>
    ⟨selectedDirectGeometry first, word, units⟩ :: selectedChainJobs (first + 1) rest

/-- Starting empty and using at most eight selected digits needs no additional
structural assumptions or capacity checks between jobs. The chain either
publishes or stops at a capacity failure; this asserts no probability bound. -/
def DirectJobSelectedChainAdmissible_statement : Prop :=
  ∀ (oldWord : LogicalKey → Nat) (steps : List ((LogicalKey → Nat) × List Bucket)),
    steps.length ≤ 8 →
    (∀ step ∈ steps, ∀ u ∈ step.2, (u.recs.map Rec.key).Nodup) →
    ∀ reason, runChain oldWord emptyOutput (selectedChainJobs 1 steps) ≠ .rejected reason

end RebuildBound.Spec
