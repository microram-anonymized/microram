import RebuildBound.Spec.HierarchyFirstFailure
import RebuildBound.Spec.AdaptiveSteps
import RebuildBound.Spec.Selected
import RebuildBound.Spec.DirectJobABounds
import RebuildBound.Spec.DirectJobAProbability
import RebuildBound.Spec.TopBound
import RebuildBound.Spec.TopPrepG
import RebuildBound.Spec.FiniteTransport

/-!
# Adaptive clients: capacity statements over a causal trace

Package statements for the capacity bound. The family causal headline reaches
`CausalBound` here and `CausalSetting` in `Spec/AdaptiveSteps.lean`; these shared
definitions belong to its human review surface. Every statement concerns a trace `T` drawn from
the joint numeric tape that is causal for exposure (`CausalSetting`), so it
never mentions the client.

* `JobFailsFirst`: the event G4a sees for a potential job: within the horizon,
  its input tiers fit, it fails on its reference inputs, and at level one the
  earlier ordinals of its cycle do not fail. `AdaptiveCovering31`: a failure
  is such an event of some potential job.
* `CausalCell`: the conditioning lemma. Within each cell of the tape off a
  set of fresh coordinates, the fresh blocks are uniform; an event is bounded
  by bounding it on every cell with a finite law of the fresh blocks.
* Per job, one cutoff per population: the separated A terms
  (`sepAEvent`, cutoff `time ℓ (o-1)`, fresh families of `(ℓ, o-1)` and
  `(ℓ, o)`) and the insertion/output term (`sepUEvent`, cutoff `time ℓ o`,
  fresh family of `(ℓ, o)`); level one's A term and its B and union terms
  likewise; the top preparation, top finish and initialization at single
  cutoffs; level one's digit-one job with its B and union terms. The budgets
  are the existing class budgets: `selSepBound` is
  `selSepABound + selSepUBound`, and `selectedDirectBound` is the B, A and
  union terms.
* `CausalWindows31`: the bound `h · 2^-64` over `h` chunks, by G4a per chunk.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.DirectJob

/-! ### The first-failure event and the covering -/

/-- **AdaptiveCovering31**: a capacity failure within the horizon is the
first-failure event of some potential job, for every trace and words. -/
def AdaptiveCovering31_statement : Prop :=
  ∀ h, 1 ≤ h → ∀ (tr : Trace) (words : Words),
    Fails (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words →
    ∃ j ∈ (geometry31.chunk h).cfg.potentialJobs,
      JobFailsFirst (geometry31.chunk h).cfg (geometry31.chunk h).shapes tr words j

/-! ### The conditioning lemma -/

/-- **CausalCell**. Under the joint tape premises, an event has probability at
most `b` when, for every cell `y` (the tape off the fresh coordinates, and the
dummy tape), there is a finite law with uniform history weights and
probability at most `b` of an event `E`, and a bijection from the fresh blocks
to the law's outcomes, such that every outcome of the event in the cell has
`E` at its fresh blocks. -/
def CausalCell_statement : Prop :=
  ∀ (cfg : Config) (N n m : Nat) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (tape : Ω → FamilyTape cfg N) (dtape : Ω → DummyTape n m)
    (words : Ω → Words), OnlineTapePremises cfg N n m μ tape dtape words →
    ∀ (fresh : Coord cfg → Prop) [DecidablePred fresh] (A : Set Ω) (b : ℝ≥0∞),
      (∀ y : ({c : Coord cfg // ¬ fresh c} → KeyIndex N → Fin (2 ^ 64)) × DummyTape n m,
        ∃ (L : FiniteJobLaw)
          (split : ({c : Coord cfg // fresh c} → KeyIndex N → Fin (2 ^ 64)) ≃ L.Outcome)
          (E : L.Hist → (LogicalKey → Nat) → Prop),
          (∀ hist, L.weight hist = (Fintype.card L.Hist : ℝ≥0∞)⁻¹) ∧ L.prob E ≤ b ∧
          ∀ ω ∈ A, (fun c => tape ω c.1) = y.1 → dtape ω = y.2 →
            E (split fun c => tape ω c.1).1 (L.wordFn (split fun c => tape ω c.1).2)) →
      μ A ≤ b

/-! ### Per-job events and budgets -/

/-- The separated merge `(ℓ, o)`'s A witnesses: a stage or radix stash, or a
completed-A range, overflows. They read A's records under the old family
`(ℓ, o-1)` and the new family, never B. -/
def sepAEvent (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (ℓ o : Nat) : Prop :=
  WithinHorizon cfg (.ordinary ℓ o) ∧ jobTiersFit cfg sh tr words (.ordinary ℓ o) ∧
    (sharedARouteWitness (sh.sep ℓ (cfg.digitAt ℓ o)) (jobWord cfg words ℓ (o - 1))
        (jobWord cfg words ℓ o) (sepInputsAt cfg sh tr words ℓ o) ∨
      sharedARangeWitness (sh.sep ℓ (cfg.digitAt ℓ o)) (jobWord cfg words ℓ o)
        (sepInputsAt cfg sh tr words ℓ o))

/-- The separated merge `(ℓ, o)`'s insertion and output witness: the union's
current-home excess exceeds the insertion stash and output tier. It reads the
union's key set under the new family only. -/
def sepUEvent (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (ℓ o : Nat) : Prop :=
  WithinHorizon cfg (.ordinary ℓ o) ∧ jobTiersFit cfg sh tr words (.ordinary ℓ o) ∧
    min ((sh.sep ℓ (cfg.digitAt ℓ o)).stashPages * (sh.sep ℓ (cfg.digitAt ℓ o)).C)
        ((sh.sep ℓ (cfg.digitAt ℓ o)).tierPages * (sh.sep ℓ (cfg.digitAt ℓ o)).C) <
      sHomeExcess (sh.sep ℓ (cfg.digitAt ℓ o)) (jobWord cfg words ℓ o) (sepInputsAt cfg sh tr words ℓ o)

/-- The A terms of `sepBound`: the stage stashes, the radix stash and the
completed-A ranges. -/
noncomputable def sepABound (g : SepGeom) (W : ℕ) (lam D : ℝ≥0) (nA K1 : ℕ) : ℝ≥0∞ :=
  g.k * ENNReal.ofReal (witness g.N g.C lam (g.stashPages * g.C) K1 D) +
    (if 1 < g.r then
      ENNReal.ofReal (witness g.N g.C lam (g.stashPages * g.C) K1 (g.curDensity W nA))
    else 0) +
    (D : ℝ≥0∞) * 2 ^ (g.k - g.I) *
      ∑ a ∈ Finset.range g.r,
        stopLoss (rangeLawR g.C lam g.earlyCap (2 ^ g.I) (g.k - g.I) g.r (qMass W g.k g.r a)) g.C

/-- The insertion and output term of `sepBound`. -/
noncomputable def sepUBound (g : SepGeom) (W : ℕ) (lam : ℝ≥0) (nU K2 : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (witness g.N g.C lam (min (g.stashPages * g.C) (g.tierPages * g.C)) K2
    (g.curDensity W nU))

/-- The A terms of `selSepBound`. -/
noncomputable def selSepABound (g : SepGeom) : ℝ≥0∞ :=
  sepABound g 64 32 (g.oldDensity 64 (32 * ((g.d - 1) * g.U))) (32 * ((g.d - 1) * g.U)) 256

/-- The insertion and output term of `selSepBound`. -/
noncomputable def selSepUBound (g : SepGeom) : ℝ≥0∞ := sepUBound g 64 32 (32 * g.N) 256

/-- Level-one ordinal `o`'s job in a cycle whose earlier ordinals did not
fail, with the property `P` of its geometry, current word and inputs. -/
def levelOneTerm (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (o : Nat)
    (P : Geometry → (LogicalKey → Nat) → DirectJob.Inputs → Prop) : Prop :=
  WithinHorizon cfg (.ordinary 1 o) ∧
    (∀ i, 0 < i → i < cfg.digitAt 1 o → jobFails cfg sh tr words (.ordinary 1 (o - i)) = false) ∧
    P (sh.direct (cfg.digitAt 1 o)) (jobWord cfg words 1 o) (levelOneInputs cfg sh tr words o)

/-- Level one's A term: A's tier fits and its route or a range overflows. -/
def levelOneA (g : Geometry) (w : LogicalKey → Nat) (inp : DirectJob.Inputs) : Prop :=
  inp.aTier.length ≤ g.aTierCapacity ∧ (aRouteWitness g w inp ∨ aRangeWitness g w inp)

/-- Level one's B term: B's excess exceeds its capacity. -/
def levelOneB (g : Geometry) (w : LogicalKey → Nat) (inp : DirectJob.Inputs) : Prop :=
  g.bCapacity < bExcess g w inp

/-- Level one's union term: the output excess exceeds its capacity. -/
def levelOneU (g : Geometry) (w : LogicalKey → Nat) (inp : DirectJob.Inputs) : Prop :=
  g.outputCapacity < inp.excess g w

/-! ### Per-role bounds over a causal trace -/

/-- A claim about the causal trace drawn from the joint tape, in every causal
setting and on every ambient space with the joint tape premises. -/
def CausalBound (geo : HierarchyGeometry)
    (claim : ∀ {Ω : Type} [MeasurableSpace Ω], Measure Ω → (Ω → Trace) → (Ω → Words) → Prop) :
    Prop :=
  ∀ N n m (T : FamilyTape geo.cfg N × DummyTape n m → Trace), CausalSetting geo N n m T →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape geo.cfg N) (dtape : Ω → DummyTape n m) (words : Ω → Words),
      OnlineTapePremises geo.cfg N n m μ tape dtape words →
      claim μ (fun ω => T (tape ω, dtape ω)) words

/-- **CausalSepA31**: a separated merge's A terms, at the cutoff `time ℓ (o-1)`. -/
def CausalSepA31_statement : Prop :=
  ∀ h, 1 ≤ h → CausalBound (geometry31.chunk h) fun μ tr words =>
    ∀ ℓ o g, JobId.ordinary ℓ o ∈ (geometry31.chunk h).cfg.potentialJobs → 2 ≤ ℓ →
      2 ≤ (geometry31.chunk h).cfg.digitAt ℓ o →
      (geometry31.chunk h).cfg.sepRow (geometry31.chunk h).rows ℓ
          ((geometry31.chunk h).cfg.digitAt ℓ o) = some g →
      μ {ω | sepAEvent (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω) (words ω) ℓ o} ≤
        selSepABound g

/-- **CausalSepU31**: a separated merge's insertion and output term, at the
cutoff `time ℓ o`. -/
def CausalSepU31_statement : Prop :=
  ∀ h, 1 ≤ h → CausalBound (geometry31.chunk h) fun μ tr words =>
    ∀ ℓ o g, JobId.ordinary ℓ o ∈ (geometry31.chunk h).cfg.potentialJobs → 2 ≤ ℓ →
      2 ≤ (geometry31.chunk h).cfg.digitAt ℓ o →
      (geometry31.chunk h).cfg.sepRow (geometry31.chunk h).rows ℓ
          ((geometry31.chunk h).cfg.digitAt ℓ o) = some g →
      μ {ω | sepUEvent (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω) (words ω) ℓ o} ≤
        selSepUBound g

/-- **CausalSep31**: a separated merge's first-failure event, at most its
class budget. -/
def CausalSep31_statement : Prop :=
  ∀ h, 1 ≤ h → CausalBound (geometry31.chunk h) fun μ tr words =>
    ∀ ℓ o g, JobId.ordinary ℓ o ∈ (geometry31.chunk h).cfg.potentialJobs → 2 ≤ ℓ →
      (geometry31.chunk h).cfg.sepRow (geometry31.chunk h).rows ℓ
          ((geometry31.chunk h).cfg.digitAt ℓ o) = some g →
      μ {ω | JobFailsFirst (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω) (words ω)
          (.ordinary ℓ o)} ≤ selSepBound g

/-- **CausalLevelOneA31**: level one's A term, at the cutoff `o - 1`. -/
def CausalLevelOneA31_statement : Prop :=
  ∀ h, 1 ≤ h → CausalBound (geometry31.chunk h) fun μ tr words =>
    ∀ o, JobId.ordinary 1 o ∈ (geometry31.chunk h).cfg.potentialJobs →
      2 ≤ (geometry31.chunk h).cfg.digitAt 1 o →
      μ {ω | levelOneTerm (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω) (words ω) o
          levelOneA} ≤ selectedDirectABudget ((geometry31.chunk h).cfg.digitAt 1 o)

/-- **CausalLevelOneBU31**: level one's B and union terms at digit `≥ 2`, and
the whole job at digit one (A is empty), all at the cutoff `o`. -/
def CausalLevelOneBU31_statement : Prop :=
  ∀ h, 1 ≤ h → CausalBound (geometry31.chunk h) fun μ tr words =>
    ∀ o, JobId.ordinary 1 o ∈ (geometry31.chunk h).cfg.potentialJobs →
      (2 ≤ (geometry31.chunk h).cfg.digitAt 1 o →
        μ {ω | levelOneTerm (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω) (words ω) o
            levelOneB} ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 117) ∧
        μ {ω | levelOneTerm (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω) (words ω) o
            levelOneU} ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 111)) ∧
      ((geometry31.chunk h).cfg.digitAt 1 o = 1 →
        μ {ω | JobFailsFirst (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω) (words ω)
            (.ordinary 1 o)} ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 117))

/-- **CausalLevelOne31**: a level-one ordinal's first-failure event, at most
its class budget. -/
def CausalLevelOne31_statement : Prop :=
  ∀ h, 1 ≤ h → CausalBound (geometry31.chunk h) fun μ tr words =>
    ∀ o, JobId.ordinary 1 o ∈ (geometry31.chunk h).cfg.potentialJobs →
      μ {ω | JobFailsFirst (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω) (words ω)
          (.ordinary 1 o)} ≤
        selectedDirectBound selectedDirectABudget ((geometry31.chunk h).cfg.digitAt 1 o)

/-- **CausalTop31**: the top finish (cutoff `time L o`), the top preparation
(cutoff `time L (o-1)`) and the initialization, at most their class budgets. -/
def CausalTop31_statement : Prop :=
  ∀ h, 1 ≤ h → CausalBound (geometry31.chunk h) fun μ tr words =>
    (∀ o, JobId.topFinish o ∈ (geometry31.chunk h).cfg.potentialJobs →
      μ {ω | JobFailsFirst (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω) (words ω)
          (.topFinish o)} ≤
        ENNReal.ofReal (topFinishBound top31.C top31.SR top31.rho top31.I top31.T
          (min top31.SMerge top31.STier) 576 576 32)) ∧
    (∀ o, JobId.topPrepare o ∈ (geometry31.chunk h).cfg.potentialJobs →
      μ {ω | JobFailsFirst (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω) (words ω)
          (.topPrepare o)} ≤ tpBound prep31 32 1 576 576) ∧
    (JobId.initialization ∈ (geometry31.chunk h).cfg.potentialJobs →
      μ {ω | JobFailsFirst (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω) (words ω)
          .initialization} ≤ tpBound init31 32 1 576 576)

/-- **CausalWindows31**: a causal trace's failure within `h` chunks of `2^32`
accesses has probability at most `h · 2^-64`. -/
def CausalWindows31_statement : Prop :=
  ∀ h, 1 ≤ h → CausalBound (geometry31.chunk h) fun μ tr words =>
    μ {ω | Fails (geometry31.chunk h).cfg (geometry31.chunk h).shapes (tr ω) (words ω)} ≤
      (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 64)

/-! ### Package steps -/

def CausalSepAStep_statement : Prop :=
  TracePrefix_statement → CausalCell_statement → CausalSepA31_statement

def CausalSepUStep_statement : Prop :=
  TracePrefix_statement → CausalCell_statement → CausalSepU31_statement

def CausalSepStep_statement : Prop :=
  CausalSepA31_statement → CausalSepU31_statement → CausalSep31_statement

def CausalLevelOneAStep_statement : Prop :=
  TracePrefix_statement → CausalCell_statement → CausalLevelOneA31_statement

def CausalLevelOneBUStep_statement : Prop :=
  TracePrefix_statement → CausalCell_statement → CausalLevelOneBU31_statement

def CausalLevelOneStep_statement : Prop :=
  CausalLevelOneA31_statement → CausalLevelOneBU31_statement → CausalLevelOne31_statement

def CausalTopStep_statement : Prop :=
  TracePrefix_statement → CausalCell_statement → CausalTop31_statement

def CausalWindowsStep_statement : Prop :=
  AdaptiveCovering31_statement → CausalSep31_statement → CausalLevelOne31_statement →
    CausalTop31_statement → CausalWindows31_statement

end RebuildBound.Spec
