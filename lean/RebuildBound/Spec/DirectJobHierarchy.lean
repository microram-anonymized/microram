import RebuildBound.Spec.SelTotal
import RebuildBound.Spec.DirectJobLawTransport
import RebuildBound.Spec.DirectJobAProbability
import RebuildBound.Spec.DirectJobAdoption

/-!
# The selected horizon bound with level one closed (trusted)

`SelTotalCoupled`'s premises 1–4 verbatim (premises 2–3 in coupling form:
a law, a coupled sample of its finite outcomes, and containment of the job's
event in the law's first-failure event), with premise 5 (level one's
per-digit bound `bDense`) replaced by its source: for every potential
level-one ordinal, an unconditional reference law coupled to the probability
space whose job failure contains the ordinal's event. At digit `d ≥ 2` the
law is the selected history law `data.law d` of a valid `DirectHistoryData`;
at digit one it is any job law with fixed complete B keys (at most 512) and
uniform words.
Then the failure probability within the horizon is at most `2^-69`.

The coupling and containment are what the native hierarchy must supply
(the coordinate split of the shared tape and the hierarchy-to-reference
correspondence); nothing is conditioned on earlier success.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- One level-one ordinal of digit `d`, event `E`: a coupled reference law
whose job failure contains `E`. -/
def DirectLevelOneCoupled {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Set Ω) (d : Nat) : Prop :=
  (2 ≤ d →
    ∃ data : DirectHistoryData, data.Valid d ∧
      ∃ sample : Ω → (data.law d).toFinite.Outcome,
        FiniteCoupling μ (data.law d).toFinite sample ∧
        E ⊆ {ω | ∃ e, runJob (selectedDirectGeometry d)
          ((data.law d).wOld (sample ω).1) ((data.law d).wordFn (sample ω).2)
          (data.direct d (sample ω).1 ((data.law d).wordFn (sample ω).2)) = .failed e}) ∧
  (d = 1 →
    ∃ (g : SepGeom) (L : SJobLaw g) (direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs)
      (sample : Ω → L.toFinite.Outcome),
      (∑ hist, L.weight hist = 1) ∧ 4 ≤ L.W ∧
      (∀ hist hw, ((direct hist (L.wordFn hw)).bRecords.map Rec.key).toFinset = L.KB) ∧
      L.KB.card ≤ 512 ∧
      FiniteCoupling μ L.toFinite sample ∧
      E ⊆ {ω | ∃ e, runJob (selectedDirectGeometry 1) (L.wOld (sample ω).1)
        (L.wordFn (sample ω).2) (direct (sample ω).1 (L.wordFn (sample ω).2)) = .failed e})

/-- The horizon bound at one selected configuration, level one closed. -/
def DirectJobHierarchyFor (cfg : Config) (rows : List (SepGeom × Nat))
    (top : TopGeom) (prep init : TPGeom) (error : ℝ≥0∞) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (fails : Set Ω) (event : JobId → Set Ω),
    -- 1. covering
    (∀ ω ∈ fails, ∃ j ∈ cfg.potentialJobs, ω ∈ event j) →
    -- 2. separated jobs
    (∀ ℓ o g, JobId.ordinary ℓ o ∈ cfg.potentialJobs → 2 ≤ ℓ →
      cfg.sepRow rows ℓ (Config.digitOf (cfg.fanout ℓ) o) = some g →
      ∃ (L : SJobLaw g) (D : ℝ≥0) (sample : Ω → L.toFinite.Outcome),
        SInputLaw L 32 D ∧ L.W = 64 ∧ D ≤ g.oldDensity 64 (32 * ((g.d - 1) * g.U)) ∧
        FiniteCoupling μ L.toFinite sample ∧
        event (.ordinary ℓ o) ⊆ {ω | sepFailEvent L (sample ω).1 (L.wordFn (sample ω).2)}) →
    -- 3. the top
    (∀ o, JobId.topFinish o ∈ cfg.potentialJobs →
      ∃ (L : TopJobLaw top) (unsh : Rec → Bool) (sample : Ω → L.toFinite.Outcome),
        TopLaw L unsh 32 ∧ FiniteCoupling μ L.toFinite sample ∧
        event (.topFinish o) ⊆ {ω | topFailEvent L unsh (sample ω).1 (L.wordFn (sample ω).2)}) →
    (∀ o, JobId.topPrepare o ∈ cfg.potentialJobs →
      ∃ (L : TPJobLaw prep) (unsh : Rec → Bool) (sample : Ω → L.toFinite.Outcome),
        TPLaw L 32 1 ∧ FiniteCoupling μ L.toFinite sample ∧
        event (.topPrepare o) ⊆
          {ω | tpFailEvent L engineRule unsh (sample ω).1 (L.wordFn (sample ω).2)}) →
    (JobId.initialization ∈ cfg.potentialJobs →
      ∃ (L : TPJobLaw init) (input : List Rec) (sample : Ω → L.toFinite.Outcome),
        InitLaw L input ∧ FiniteCoupling μ L.toFinite sample ∧
        event .initialization ⊆
          {ω | tpFailEvent L engineRule (fun _ => false) (sample ω).1 (L.wordFn (sample ω).2)}) →
    -- 4. adoption
    (∀ ℓ o, JobId.ordinary ℓ o ∈ cfg.potentialJobs → 2 ≤ ℓ →
      Config.digitOf (cfg.fanout ℓ) o = 1 → μ (event (.ordinary ℓ o)) = 0) →
    -- 5. level one: coupled reference laws containing each ordinal's event
    (∀ o, JobId.ordinary 1 o ∈ cfg.potentialJobs →
      DirectLevelOneCoupled μ (event (.ordinary 1 o)) (Config.digitOf (cfg.fanout 1) o)) →
    μ fails ≤ error

/-- The original selected interface, retained as a specialization. -/
def DirectJobHierarchyAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  DirectJobHierarchyFor cfg rows selectedTop selectedTP selectedTP (ENNReal.ofReal (1 / (2 : ℝ) ^ 69))

def DirectJobHierarchy_statement : Prop :=
  DirectJobHierarchyAt uniformConfig uniformSeparated ∧
  DirectJobHierarchyAt halfFanoutConfig halfFanoutSeparated

/-- A selected level-one cycle from empty (at most eight consecutive digits,
units with unique keys) is never rejected: on any space, every outcome is a
capacity failure or a publication, so bounding the failure event bounds
everything that is not a successful cycle. -/
def DirectJobSelectedChainOutcome_statement : Prop :=
  ∀ {Ω : Type} (oldWord : Ω → LogicalKey → Nat) (steps : Ω → List ((LogicalKey → Nat) × List Bucket)),
    (∀ ω, (steps ω).length ≤ 8) →
    (∀ ω, ∀ step ∈ steps ω, ∀ u ∈ step.2, (u.recs.map Rec.key).Nodup) →
    {ω | ∃ e, runChain (oldWord ω) emptyOutput (selectedChainJobs 1 (steps ω)) = .failed e} ∪
      {ω | ∃ out, runChain (oldWord ω) emptyOutput (selectedChainJobs 1 (steps ω)) =
        .published out} = Set.univ

end RebuildBound.Spec
