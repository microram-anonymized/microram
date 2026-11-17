import RebuildBound.Spec.DirectJobHistoryGeometry
import RebuildBound.Spec.DirectJobUniformHierarchy

/-! Geometry-parametric direct-cycle histories. The product history and its
coupling are unconditional; only the execution correspondence may use that an
ordinal was reached. Local failure probabilities remain explicit, with no
selected numerical budgets or claim of rejection-freedom. -/

open MeasureTheory
open scoped ENNReal
namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Chronological direct jobs with their actual per-digit geometry. -/
def directChainJobs (geometry : Nat → Geometry) (first : Nat) :
    List ((LogicalKey → Nat) × List Bucket) → List ChainJob
  | [] => []
  | (word, units) :: rest =>
    ⟨geometry first, word, units⟩ :: directChainJobs geometry (first + 1) rest

/-- Match a sampled history to the actual prefix and both adjacent families.
Words outside the complete source key sets remain unconstrained. -/
def DirectCycleLaterCorrespondence {Ω : Type} (geometry : Nat → Geometry)
    (s : SepGeom) (oldWord : Ω → LogicalKey → Nat)
    (steps : Ω → List ((LogicalKey → Nat) × List Bucket)) (i : Nat)
    (data : DirectHistoryData)
    (sample : Ω → (data.lawFor (geometry (i + 1)) s).toFinite.Outcome) : Prop :=
  ∀ ω prev cur, (steps ω)[i]? = some prev → (steps ω)[i + 1]? = some cur →
    (∃ out, runChain (oldWord ω) emptyOutput
      (directChainJobs geometry 1 ((steps ω).take (i + 1))) = .published out) →
    data.before (sample ω).1.1 = referenceChain (oldWord ω) (.ofOutput emptyOutput)
      (directChainJobs geometry 1 ((steps ω).take i)) ∧
    (∀ x ∈ (data.before (sample ω).1.1).main.flatMap Bucket.recs,
      data.olderWord (sample ω).1.1 x.key =
        selectedCycleOldWord (oldWord ω) (steps ω) i x.key) ∧
    (∀ k ∈ data.KA, data.word (sample ω).1.2 k = prev.1 k) ∧
    data.priorUnits (sample ω).1.1 (data.word (sample ω).1.2) = prev.2 ∧
    data.freshUnits (sample ω).1
      ((data.lawFor (geometry (i + 1)) s).wordFn (sample ω).2) = cur.2 ∧
    ∀ k ∈ data.KA ∪ data.KB,
      (data.lawFor (geometry (i + 1)) s).wordFn (sample ω).2 k = cur.1 k

/-- A normalized, actual-load product history coupled to the ambient tape. -/
def DirectCycleLaterCoupled {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (geometry : Nat → Geometry) (s : SepGeom) (load : Nat)
    (oldWord : Ω → LogicalKey → Nat) (steps : Ω → List ((LogicalKey → Nat) × List Bucket))
    (i : Nat) : Prop :=
  ∃ data : DirectHistoryData, data.ValidFor s load ∧
    ∃ sample : Ω → (data.lawFor (geometry (i + 1)) s).toFinite.Outcome,
      FiniteCoupling μ (data.lawFor (geometry (i + 1)) s).toFinite sample ∧
      DirectCycleLaterCorrespondence geometry s oldWord steps i data sample

/-- Capacity failure at a later reached ordinal. This does not include rejection. -/
def DirectCycleLaterFailure {Ω : Type} (geometry : Nat → Geometry)
    (oldWord : Ω → LogicalKey → Nat) (steps : Ω → List ((LogicalKey → Nat) × List Bucket))
    (i : Nat) : Set Ω :=
  {ω | ∃ e step out', (steps ω)[i + 1]? = some step ∧
    runChain (oldWord ω) emptyOutput
      (directChainJobs geometry 1 ((steps ω).take (i + 1))) = .published out' ∧
    runJob (geometry (i + 2)) (selectedCycleOldWord (oldWord ω) (steps ω) (i + 1))
      step.1 (adopt out' step.2) = .failed e}

/-- A uniform cycle projection supplies the coupled history for any geometry
sequence and actual source load. Shape applicability is checked separately by
`DirectJobHistoryInputLawFor`; no upper bound on cycle length is needed here. -/
def DirectJobUniformCycleHistory_statement : Prop :=
  ∀ (n : Nat) (units : Fin n → List Bucket) (geometry : Nat → Geometry)
    (s : SepGeom) (load i : Nat), i + 1 < n → s.d = i + 2 →
    (∀ j, (unitKeys (units j)).card ≤ load * s.U) →
    ∀ [MeasurableSpace (CycleTape units)] [MeasurableSingletonClass (CycleTape units)]
      {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (π : Ω → CycleTape units),
    Measurable π → μ.map π = ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape units)) →
    ∀ (oldWord : Ω → LogicalKey → Nat) (native : Fin n → Ω → LogicalKey → Nat),
    (∀ j ω k (hk : k ∈ cycleKeys units j), native j ω k = π ω j ⟨k, hk⟩) →
    DirectCycleLaterCoupled μ geometry s load oldWord (cycleStepsOn units native) i

/-- Transport a reached capacity failure to the unconditional local history
law. A job certificate can bound the right side without conditioning on success. -/
def DirectJobCycleHistoryTransport_statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (geometry : Nat → Geometry) (s : SepGeom) (load : Nat)
    (oldWord : Ω → LogicalKey → Nat) (steps : Ω → List ((LogicalKey → Nat) × List Bucket))
    (i : Nat) (data : DirectHistoryData), data.ValidFor s load →
    ∀ sample : Ω → (data.lawFor (geometry (i + 1)) s).toFinite.Outcome,
    FiniteCoupling μ (data.lawFor (geometry (i + 1)) s).toFinite sample →
    DirectCycleLaterCorrespondence geometry s oldWord steps i data sample →
    μ (DirectCycleLaterFailure geometry oldWord steps i) ≤
      (data.lawFor (geometry (i + 1)) s).prob (fun hist word => ∃ e,
        runJob (geometry (i + 2)) ((data.lawFor (geometry (i + 1)) s).wOld hist) word
          (data.directFor (geometry (i + 1)) hist word) = .failed e)

end RebuildBound.Spec
