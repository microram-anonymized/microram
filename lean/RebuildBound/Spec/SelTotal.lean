import RebuildBound.Spec.Compose
import RebuildBound.Spec.Model.ConfigRows
import RebuildBound.Spec.Subtotal
import RebuildBound.Spec.TopPrepG
import RebuildBound.Spec.FiniteTransport

/-!
# The selected configurations' horizon bound (trusted)

`REPORT.tex`, Theorem `thm:abstract-composition` at the two selected
configurations, with every per-role bound proved so far. For each selected
configuration (`uniformConfig` with `uniformSeparated`, `halfFanoutConfig`
with `halfFanoutSeparated`), on any probability space, if

1. **(covering)** every capacity failure within the horizon lies in the event
   of some potential job (`Config.potentialJobs`);
2. **(separated jobs)** the event of each potential separated job (levels
   `2 … L - 1`, digits `≥ 2`) has probability at most that of its row's
   job's failure under a law with `SInputLaw`
   at load 32 with 64-bit words and old-home density at most `oldDensity`;
3. **(top)** each potential top finish's event has probability at most that
   of a selected finish's failure under `TopLaw` at load 32; each top
   preparation's, at most that of a selected preparation under `TPLaw` at load
   32 and density 1; the initialization's, at most that of a selected
   initialization under `InitLaw`;
4. **(adoption)** an adoption (digit one above level one) performs no
   capacity test: its event is null;
5. **(dense level one)** each level-one job of digit `d` has probability at
   most `bDense d`, an explicit parameter here; `Spec/DirectJobHierarchy.lean`
   replaces it by the direct job's unconditional reference law,

then the probability of a capacity failure within `2^32` accesses is at most

  `1.29 · 2^-70 + 258 · 2^-115 + Σ_d n_(1,d) bDense d`,

the selected subtotal (separated rows and top finishes, `Spec/Subtotal.lean`),
the 257 top preparations and the initialization, and level one's open term.
Current native numerical subtotals are separate evidence; this theorem retains
the per-digit level-one bounds as explicit premises.

Premises 1–4 and the laws in 2–3 are what the hierarchy model (`Spec/Model/Hierarchy.lean`)
establishes (`prop:native-sources`, `prop:native-frontiers`,
`prop:ordinal-exposures`); the deterministic inventory of native metadata is
outside the model.

**SelTotalCoupled** is the same bound with premises 2–3 in the form the hierarchy model (`Spec/Model/Hierarchy.lean`)
supplies (`Spec/FiniteTransport.lean`): per potential job, a law meeting its
contract, a sample of its finite outcomes coupled to `μ`, and containment of
the job's event in the law's first-failure event at the sample.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec

open RebuildBound.Model

/-- The per-class bounds of a selected configuration. -/
noncomputable def selClassBound (cfg : Config) (rows : List (SepGeom × Nat))
    (bDense : Nat → ℝ≥0∞) : JobClass → ℝ≥0∞
  | .ordinary ℓ d =>
    if ℓ = 1 then bDense d
    else if d = 1 then 0
    else ((cfg.sepRow rows ℓ d).map selSepBound).getD 1
  | .topPrepare => ENNReal.ofReal (1 / 2 ^ 115)
  | .topFinish => ENNReal.ofReal (5845 / (10000 * 2 ^ 78))
  | .initialization => ENNReal.ofReal (1 / 2 ^ 115)

/-- The horizon bound at one selected configuration with its separated rows. -/
def SelTotalAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (fails : Set Ω) (event : JobId → Set Ω) (bDense : Nat → ℝ≥0∞),
    -- 1. covering
    (∀ ω ∈ fails, ∃ j ∈ cfg.potentialJobs, ω ∈ event j) →
    -- 2. separated jobs
    (∀ ℓ o g, JobId.ordinary ℓ o ∈ cfg.potentialJobs → 2 ≤ ℓ →
      cfg.sepRow rows ℓ (Config.digitOf (cfg.fanout ℓ) o) = some g →
      ∃ (L : SJobLaw g) (D : ℝ≥0), SInputLaw L 32 D ∧ L.W = 64 ∧
        D ≤ g.oldDensity 64 (32 * ((g.d - 1) * g.U)) ∧
        μ (event (.ordinary ℓ o)) ≤ L.prob (fun hist w =>
          STiersFit g (L.inputs hist w) ∧ (sJob engineRule g w (L.inputs hist w)).toBool = false)) →
    -- 3. the top
    (∀ o, JobId.topFinish o ∈ cfg.potentialJobs →
      ∃ (L : TopJobLaw selectedTop) (unsh : Rec → Bool), TopLaw L unsh 32 ∧
        μ (event (.topFinish o)) ≤ L.prob (topFailEvent L unsh)) →
    (∀ o, JobId.topPrepare o ∈ cfg.potentialJobs →
      ∃ (L : TPJobLaw selectedTP) (unsh : Rec → Bool), TPLaw L 32 1 ∧
        μ (event (.topPrepare o)) ≤ L.prob (tpFailEvent L engineRule unsh)) →
    (JobId.initialization ∈ cfg.potentialJobs →
      ∃ (L : TPJobLaw selectedTP) (input : List Rec), InitLaw L input ∧
        μ (event .initialization) ≤ L.prob (tpFailEvent L engineRule fun _ => false)) →
    -- 4. adoption
    (∀ ℓ o, JobId.ordinary ℓ o ∈ cfg.potentialJobs → 2 ≤ ℓ →
      Config.digitOf (cfg.fanout ℓ) o = 1 → μ (event (.ordinary ℓ o)) = 0) →
    -- 5. dense level one
    (∀ o, JobId.ordinary 1 o ∈ cfg.potentialJobs →
      μ (event (.ordinary 1 o)) ≤ bDense (Config.digitOf (cfg.fanout 1) o)) →
    μ fails ≤ ENNReal.ofReal (129 / (100 * 2 ^ 70)) + 258 * ENNReal.ofReal (1 / 2 ^ 115) +
      ((List.range (cfg.fanout 1)).map fun i =>
        (cfg.ordinaryCount 1 (i + 1) : ℝ≥0∞) * bDense (i + 1)).sum

/-- **SelTotal**: the horizon bound at both selected configurations. -/
def SelTotal_statement : Prop :=
  SelTotalAt uniformConfig uniformSeparated ∧ SelTotalAt halfFanoutConfig halfFanoutSeparated

/-- The first-failure event of one separated job (premise 2's event): A's tier
fits and the job fails. -/
def sepFailEvent {g : SepGeom} (L : SJobLaw g) (hist : L.Hist) (w : LogicalKey → Nat) : Prop :=
  STiersFit g (L.inputs hist w) ∧ (sJob engineRule g w (L.inputs hist w)).toBool = false

/-- `SelTotalAt` with premises 2–3 in coupling form, the form the hierarchy
model supplies: for each potential job, a law meeting its contract, a sample of the
law's finite outcomes coupled to `μ` (`FiniteCoupling`), and deterministic
containment of the job's event in the law's first-failure event at the
sample. Premises 1, 4, 5 and the conclusion are `SelTotalAt`'s. -/
def SelTotalCoupledFor (cfg : Config) (rows : List (SepGeom × Nat))
    (top : TopGeom) (prep init : TPGeom)
    (budget : (Nat → ℝ≥0∞) → ℝ≥0∞) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (fails : Set Ω) (event : JobId → Set Ω) (bDense : Nat → ℝ≥0∞),
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
    -- 5. dense level one
    (∀ o, JobId.ordinary 1 o ∈ cfg.potentialJobs →
      μ (event (.ordinary 1 o)) ≤ bDense (Config.digitOf (cfg.fanout 1) o)) →
    μ fails ≤ budget bDense

/-- The original selected subtotal and preparation allocation. -/
noncomputable def selectedHierarchyBudget (cfg : Config) (bDense : Nat → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (129 / (100 * 2 ^ 70)) + 258 * ENNReal.ofReal (1 / 2 ^ 115) +
    ((List.range (cfg.fanout 1)).map fun i =>
      (cfg.ordinaryCount 1 (i + 1) : ℝ≥0∞) * bDense (i + 1)).sum

/-- The selected coupling interface, retained as a specialization. -/
def SelTotalAtCoupled (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  SelTotalCoupledFor cfg rows selectedTop selectedTP selectedTP (selectedHierarchyBudget cfg)

/-- **SelTotalCoupled**: the horizon bound at both selected configurations,
premises 2–3 in coupling form. -/
def SelTotalCoupled_statement : Prop :=
  SelTotalAtCoupled uniformConfig uniformSeparated ∧
    SelTotalAtCoupled halfFanoutConfig halfFanoutSeparated

end RebuildBound.Spec
