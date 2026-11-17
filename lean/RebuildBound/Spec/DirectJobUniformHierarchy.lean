import RebuildBound.Spec.DirectJobHierarchyCycles
import RebuildBound.Spec.DirectJobUniformCycle

/-!
# The selected horizon bound with level one on uniform word blocks (trusted)

`DirectJobHierarchyCycles` takes, per level-one cycle, the coupled laws and the
pointwise correspondence of `DirectJobSelectedCycle`; `DirectJobUniformCycle`
supplies them on one cycle's own uniform tape. This file lifts that supply to
the ambient probability space of the horizon: level-one cycle `c` has fixed
units `(cyc c).units` and a measurable projection `tape c` of the ambient
space onto its word tape `CycleTape (cyc c).units` whose image law is uniform
(the cycle's word blocks are uniform and independent across keys and ordinals;
nothing is assumed about their joint law with anything else), and ordinal
`j`'s native word agrees with block `j` on the ordinal's complete union
`cycleKeys`. Together with the covering premise in cycle form and
`SelTotalCoupled`'s premises 2–4 for the other levels, the failure probability
within the horizon is at most `2^-69` at both selected configurations.

For level one this leaves native scope only: that the native hash words of a
cycle, restricted to the ordinals' complete unions, have the uniform law and
that native execution of a cycle is `runChain` on these steps.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- One level-one cycle's fixed data: its number of ordinals and their units. -/
structure CycleUnits where
  n : Nat
  units : Fin n → List Bucket

/-- A cycle's chronological steps on an ambient space: ordinal `j`'s native
word at `ω` and its fixed units. -/
def cycleStepsOn {Ω : Type} {n : Nat} (units : Fin n → List Bucket)
    (native : Fin n → Ω → LogicalKey → Nat) (ω : Ω) : List ((LogicalKey → Nat) × List Bucket) :=
  List.ofFn fun j => (native j ω, units j)

/-- The horizon bound at one selected configuration, level one on uniform word
blocks. -/
def DirectJobUniformHierarchyFor (cfg : Config) (rows : List (SepGeom × Nat))
    (top : TopGeom) (prep init : TPGeom) (error : ℝ≥0∞) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (fails : Set Ω) (event : JobId → Set Ω)
    (cyc : Nat → CycleUnits) (tape : ∀ c, Ω → CycleTape (cyc c).units)
    (oldWord : Nat → Ω → LogicalKey → Nat) (native : ∀ c, Fin (cyc c).n → Ω → LogicalKey → Nat),
    -- 1. covering: a failure is the event of a potential job above level one,
    --    or a level-one cycle of the horizon that does not publish
    (∀ ω ∈ fails,
      (∃ j ∈ cfg.potentialJobs, (∀ o, j ≠ .ordinary 1 o) ∧ ω ∈ event j) ∨
      ∃ c < cfg.levelOneCycles, ¬ ∃ out, runChain (oldWord c ω) emptyOutput
        (selectedChainJobs 1 (cycleStepsOn (cyc c).units (native c) ω)) = .published out) →
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
    -- 5. level one: each cycle's shape, uniform word blocks, native words on the unions
    (∀ c < cfg.levelOneCycles, (cyc c).n ≤ cfg.cycleLength c) →
    (∀ c < cfg.levelOneCycles, ∀ j, ∀ u ∈ (cyc c).units j, (u.recs.map Rec.key).Nodup) →
    (∀ c < cfg.levelOneCycles, ∀ j, (unitKeys ((cyc c).units j)).card ≤ 512) →
    (∀ c < cfg.levelOneCycles, Measurable (tape c) ∧
      μ.map (tape c) = ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape (cyc c).units))) →
    (∀ c < cfg.levelOneCycles, ∀ j ω k (hk : k ∈ cycleKeys (cyc c).units j),
      native c j ω k = tape c ω j ⟨k, hk⟩) →
    μ fails ≤ error

/-- The original selected interface, retained as a specialization. -/
def DirectJobUniformHierarchyAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  DirectJobUniformHierarchyFor cfg rows selectedTop selectedTP selectedTP (ENNReal.ofReal (1 / (2 : ℝ) ^ 69))

def DirectJobUniformHierarchy_statement : Prop :=
  DirectJobUniformHierarchyAt uniformConfig uniformSeparated ∧
  DirectJobUniformHierarchyAt halfFanoutConfig halfFanoutSeparated

end RebuildBound.Spec
