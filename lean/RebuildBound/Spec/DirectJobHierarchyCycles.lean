import RebuildBound.Spec.DirectJobHierarchy
import RebuildBound.Spec.DirectJobSelectedCycle

/-!
# The selected horizon bound with level one given by its cycles (trusted)

`DirectJobHierarchy` takes, per level-one ordinal, a coupled reference law whose
job failure contains that ordinal's event, and its covering premise names an
abstract event per ordinal. `DirectJobSelectedCycle` bounds one selected cycle
from its per-ordinal coupled laws and the pointwise correspondence at reached
ordinals, deriving the containment. This file joins the two: level one of the
horizon is a sequence of selected cycles, each run by `runChain` from
`emptyOutput` over the ordinals of one period of the fanout `b_1` (the last
cycle of the horizon may be shorter), and

* the covering premise says that every capacity failure in the horizon is the
  event of a potential job above level one or a level-one cycle that does not
  publish;
* level one's premises are those of `DirectJobSelectedCycle`, per cycle:
  bounded length, units with unique keys, a coupled digit-one law and, per
  later position, a coupled selected history law with the correspondence at
  reached ordinals.

The conclusion is `2^-69` at both selected configurations. The per-ordinal
events of `DirectJobHierarchy` are the derived `selectedCycleFailAt` sets:
the cycle reaches position `j` (its earlier ordinals published) and its job at
`j` is a capacity failure. Which ordinal a failing cycle fails at is derived,
so the native side need only identify failures with cycles.

Level-one ordinal `s_1 + 1 + i` (`i < m_1(H)`) is position `i mod b_1` of cycle
`i / b_1`; since `b_1 ∣ s_1` at both selected configurations (the seed is
`D b_1 ⋯ b_(L-1)`), that position is the ordinal's digit minus one.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.Model.Config

variable (cfg : Config)

/-- The number of level-one cycles in the horizon: the potential level-one
ordinals in groups of `b_1`, the last group possibly shorter. -/
def levelOneCycles : Nat := (cfg.ordinals 1 + cfg.fanout 1 - 1) / cfg.fanout 1

/-- The number of potential ordinals of level-one cycle `c`: `b_1`, except
that the last cycle stops at the horizon. -/
def cycleLength (c : Nat) : Nat := min (cfg.fanout 1) (cfg.ordinals 1 - c * cfg.fanout 1)

/-- The level-one ordinal of position `j` of cycle `c`. -/
def cycleOrdinal (c j : Nat) : Nat := cfg.seed 1 + 1 + (c * cfg.fanout 1 + j)

end RebuildBound.Model.Config

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- A selected cycle (initial old word `oldWord`, chronological `steps`) fails
at position `j`: it has a step there, its first `j` ordinals published, and
the job at position `j` (digit `1 + j`, the preceding step's word as its old
word) is a capacity failure. -/
def selectedCycleFailAt {Ω : Type} (oldWord : Ω → LogicalKey → Nat)
    (steps : Ω → List ((LogicalKey → Nat) × List Bucket)) (j : Nat) : Set Ω :=
  {ω | ∃ e step out', (steps ω)[j]? = some step ∧
    runChain (oldWord ω) emptyOutput (selectedChainJobs 1 ((steps ω).take j)) =
      .published out' ∧
    runJob (selectedDirectGeometry (1 + j)) (selectedCycleOldWord (oldWord ω) (steps ω) j)
      step.1 (adopt out' step.2) = .failed e}

/-- The horizon bound at one selected configuration, level one given by its
cycles. `oldWord c` and `steps c` are cycle `c`'s initial old word and its
chronological steps (current word family and fresh units per ordinal). -/
def DirectJobHierarchyCyclesFor (cfg : Config) (rows : List (SepGeom × Nat))
    (top : TopGeom) (prep init : TPGeom) (error : ℝ≥0∞) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (fails : Set Ω) (event : JobId → Set Ω)
    (oldWord : Nat → Ω → LogicalKey → Nat) (steps : Nat → Ω → List ((LogicalKey → Nat) × List Bucket)),
    -- 1. covering: a failure is the event of a potential job above level one,
    --    or a level-one cycle of the horizon that does not publish
    (∀ ω ∈ fails,
      (∃ j ∈ cfg.potentialJobs, (∀ o, j ≠ .ordinary 1 o) ∧ ω ∈ event j) ∨
      ∃ c < cfg.levelOneCycles, ¬ ∃ out,
        runChain (oldWord c ω) emptyOutput (selectedChainJobs 1 (steps c ω)) = .published out) →
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
    -- 5. level one: each cycle of the horizon as in `DirectJobSelectedCycle`
    (∀ c < cfg.levelOneCycles, ∀ ω, (steps c ω).length ≤ cfg.cycleLength c) →
    (∀ c < cfg.levelOneCycles, ∀ ω, ∀ step ∈ steps c ω, ∀ u ∈ step.2,
      (u.recs.map Rec.key).Nodup) →
    (∀ c < cfg.levelOneCycles, SelectedCycleDigitOneCoupled μ (steps c)) →
    (∀ c < cfg.levelOneCycles, ∀ i, i + 1 < cfg.cycleLength c →
      SelectedCycleLaterCoupled μ (oldWord c) (steps c) i) →
    μ fails ≤ error

/-- The original selected interface, retained as a specialization. -/
def DirectJobHierarchyCyclesAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  DirectJobHierarchyCyclesFor cfg rows selectedTop selectedTP selectedTP (ENNReal.ofReal (1 / (2 : ℝ) ^ 69))

def DirectJobHierarchyCycles_statement : Prop :=
  DirectJobHierarchyCyclesAt uniformConfig uniformSeparated ∧
  DirectJobHierarchyCyclesAt halfFanoutConfig halfFanoutSeparated

end RebuildBound.Spec
