import RebuildBound.Spec.HierarchyBase
import RebuildBound.Spec.DirectJobUniformHierarchy

/-!
# Shared hierarchy contracts and laws

The public capacity and adaptive endpoints use `geometry31`. The selected
configuration specializations below remain internal proof infrastructure for
its generic hierarchy, local-law, and numerical constructions; they are not
an independently supported security endpoint.

`TracePremises` fixes distinct unit and initialization keys, per-unit loads,
and a key bound. `UnshPromise` supplies the top-finish flag promise, and
`TapePremises` supplies the uniform family tape. The geometry-parametric
capacity statement is `HierarchyUniformFor` in `Spec/HierarchyUniform31.lean`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec
open Model Model.DirectJob Model.Hierarchy

/-- A property of a configuration with its rows, at both selected
configurations. -/
def SelectedAt (P : Config → List (SepGeom × Nat) → Prop) : Prop :=
  P uniformConfig uniformSeparated ∧ P halfFanoutConfig halfFanoutSeparated

/-! ### The jobs' contracts (HierarchyInvariant) -/


/-- The starting buckets of a top preparation: the old homes under the
previous top ordinal's family. -/
def prepPos (cfg : Config) (sh : Shapes) (words : Words) (o : Nat) : LogicalKey → Nat :=
  fun k => jobWord cfg words cfg.levels (o - 1) k % sh.prep.T

/-- The structural contracts of the potential jobs under one tape, with fixed
key sets (against every other tape), keys below `N` and the loads. -/
structure JobContracts (cfg : Config) (sh : Shapes) (tr : Trace) (N : Nat) (words : Words) :
    Prop where
  /-- A separated job's inputs meet `SInputShape`, with the previous ordinal's
  family as A's old family. -/
  sepShape : ∀ ℓ o, JobId.ordinary ℓ o ∈ cfg.potentialJobs → 2 ≤ ℓ → 2 ≤ cfg.digitAt ℓ o →
    SInputShape (sh.sep ℓ (cfg.digitAt ℓ o)) (jobWord cfg words ℓ (o - 1)) (jobWord cfg words ℓ o)
      (sepInputsAt cfg sh tr words ℓ o)
  sepKeysA : ∀ ℓ o, JobId.ordinary ℓ o ∈ cfg.potentialJobs → 2 ≤ ℓ → 2 ≤ cfg.digitAt ℓ o →
    ∀ words' : Words,
      ((sepInputsAt cfg sh tr words ℓ o).aAll.map Rec.key).toFinset =
        ((sepInputsAt cfg sh tr words' ℓ o).aAll.map Rec.key).toFinset
  sepKeysB : ∀ ℓ o, JobId.ordinary ℓ o ∈ cfg.potentialJobs → 2 ≤ ℓ → 2 ≤ cfg.digitAt ℓ o →
    ∀ words' : Words,
      ((sepInputsAt cfg sh tr words ℓ o).bAll.map Rec.key).toFinset =
        ((sepInputsAt cfg sh tr words' ℓ o).bAll.map Rec.key).toFinset
  sepLoadA : ∀ ℓ o, JobId.ordinary ℓ o ∈ cfg.potentialJobs → 2 ≤ ℓ → 2 ≤ cfg.digitAt ℓ o →
    ((sepInputsAt cfg sh tr words ℓ o).aAll.map Rec.key).toFinset.card ≤
      cfg.load * ((cfg.digitAt ℓ o - 1) * cfg.carry ℓ)
  sepLoadB : ∀ ℓ o, JobId.ordinary ℓ o ∈ cfg.potentialJobs → 2 ≤ ℓ → 2 ≤ cfg.digitAt ℓ o →
    ((sepInputsAt cfg sh tr words ℓ o).bAll.map Rec.key).toFinset.card ≤ cfg.load * cfg.carry ℓ
  sepBelow : ∀ ℓ o, JobId.ordinary ℓ o ∈ cfg.potentialJobs → 2 ≤ ℓ → 2 ≤ cfg.digitAt ℓ o →
    ∀ x ∈ (sepInputsAt cfg sh tr words ℓ o).aAll ++ (sepInputsAt cfg sh tr words ℓ o).bAll, x.key.toNat < N
  /-- A top preparation's inputs meet `TPShape` at the previous family's old
  homes. -/
  prepShape : ∀ o, JobId.topPrepare o ∈ cfg.potentialJobs →
    TPShape sh.prep (prepPos cfg sh words o) (prepInputsAt cfg sh tr words o)
  prepKeys : ∀ o, JobId.topPrepare o ∈ cfg.potentialJobs → ∀ words' : Words,
    ((prepInputsAt cfg sh tr words o).aAll.map Rec.key).toFinset =
      ((prepInputsAt cfg sh tr words' o).aAll.map Rec.key).toFinset
  prepLoad : ∀ o, JobId.topPrepare o ∈ cfg.potentialJobs →
    ((prepInputsAt cfg sh tr words o).aAll.map Rec.key).toFinset.card ≤ cfg.load * sh.prep.T
  prepBelow : ∀ o, JobId.topPrepare o ∈ cfg.potentialJobs →
    ∀ x ∈ (prepInputsAt cfg sh tr words o).aAll, x.key.toNat < N
  /-- A top finish's inputs meet `TopShape` under its family. -/
  finishShape : ∀ o, JobId.topFinish o ∈ cfg.potentialJobs →
    TopShape sh.top tr.unsh (jobWord cfg words cfg.levels o) (finishInputsAt cfg sh tr words o)
  finishRecsA : ∀ o, JobId.topFinish o ∈ cfg.potentialJobs → ∀ words' : Words,
    (finishInputsAt cfg sh tr words o).aAll.toFinset = (finishInputsAt cfg sh tr words' o).aAll.toFinset
  finishRecsB : ∀ o, JobId.topFinish o ∈ cfg.potentialJobs → ∀ words' : Words,
    (finishInputsAt cfg sh tr words o).bAll.toFinset = (finishInputsAt cfg sh tr words' o).bAll.toFinset
  finishLoadA : ∀ o, JobId.topFinish o ∈ cfg.potentialJobs →
    (finishInputsAt cfg sh tr words o).aAll.toFinset.card ≤ cfg.load * sh.top.T
  finishLoadW : ∀ o, JobId.topFinish o ∈ cfg.potentialJobs →
    (liveSet (finishInputsAt cfg sh tr words o).aAll.toFinset
      (finishInputsAt cfg sh tr words o).bAll.toFinset).card ≤ cfg.load * sh.top.T
  finishBelow : ∀ o, JobId.topFinish o ∈ cfg.potentialJobs →
    ∀ x ∈ (finishInputsAt cfg sh tr words o).aAll ++ (finishInputsAt cfg sh tr words o).bAll, x.key.toNat < N
  /-- The initialization's input fits the scatter. -/
  initCount : tr.init.length ≤ sh.init.C / 2 * sh.init.T
  /-- Every table's keys lie below `N`. -/
  tableBelow : ∀ ℓ v, ∀ x ∈ (table cfg sh tr words ℓ v).records, x.key.toNat < N
  /-- Below the top no key is lost: a job's input keys (the level's previous
  table, except at digit one where it has been forwarded, and the units or
  the carry) are keys of its table. -/
  keysFlow : ∀ ℓ v, 1 ≤ ℓ → ℓ < cfg.levels → cfg.seed ℓ < v →
    ∀ x ∈ (if cfg.digitAt ℓ v = 1 then [] else (table cfg sh tr words ℓ (v - 1)).records) ++
      (if ℓ = 1 then DirectMasks.records (tr.units (v - cfg.seed 1 - 1))
        else (carryOf cfg sh tr words ℓ v).records),
      x.key ∈ (table cfg sh tr words ℓ v).records.map Rec.key

/-- The contracts hold at one selected configuration. -/
def HierarchyInvariantAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  ∀ (N : Nat) (tr : Trace), N ≤ 2 ^ 27 → TracePremises cfg N tr →
    UnshPromise cfg (hierarchyShapes cfg rows) tr →
    ∀ words : Words, JobContracts cfg (hierarchyShapes cfg rows) tr N words

/-- **HierarchyInvariant**: the potential jobs' structural contracts, fixed
key sets, key bound and loads, under every tape. -/
def HierarchyInvariant_statement : Prop := SelectedAt HierarchyInvariantAt

/-! ### Word locality of the tables (HierarchyLocality) -/

/-- Two tapes agree on the cone of `(ℓ, v)`: at every coordinate of the cone,
the job's words (the family's, `jobWord`) agree on the keys that job reads
(`jobKeys`, under the first tape). -/
def AgreeOnCone (cfg : Config) (sh : Shapes) (tr : Trace) (words words' : Words) (ℓ v : Nat) :
    Prop :=
  ∀ p ∈ cone cfg ℓ v, ∀ k ∈ jobKeys cfg sh tr words p.1 p.2,
    jobWord cfg words p.1 p.2 k = jobWord cfg words' p.1 p.2 k

/-- Word locality at one selected configuration: tables agree on tapes
agreeing on their cones, and a job's family is the family of no coordinate in
the cone of the level's previous table. -/
def HierarchyLocalityAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  (∀ (tr : Trace) (words words' : Words) (ℓ v : Nat),
    AgreeOnCone cfg (hierarchyShapes cfg rows) tr words words' ℓ v →
    table cfg (hierarchyShapes cfg rows) tr words ℓ v =
      table cfg (hierarchyShapes cfg rows) tr words' ℓ v) ∧
  (∀ ℓ v, 1 ≤ ℓ → ℓ ≤ cfg.levels → cfg.seed ℓ < v →
    ∀ q ∈ cone cfg ℓ (v - 1), familyOf cfg q.1 q.2 ≠ familyOf cfg ℓ v)

/-- **HierarchyLocality**: word locality of the tables along the cones. -/
def HierarchyLocality_statement : Prop := SelectedAt HierarchyLocalityAt

/-! ### Tier fit of a publication (TierFit) -/

/-- **SepTierFit**: a separated job's publication has a tier within the
output tier's capacity. -/
def SepTierFit_statement : Prop :=
  ∀ (g : SepGeom) (w : LogicalKey → Nat) (inp : SInputs) (out : Output),
    sJob engineRule g w inp = .ok out → (Bucket.recs out.tier).length ≤ g.tierPages * g.C

/-- **TopTierFit**: a top finish's publication has a tier within `S_tier`. -/
def TopTierFit_statement : Prop :=
  ∀ (g : TopGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat) (inp : TopInputs) (out : Output),
    topJob g unsh w inp = .ok out → (Bucket.recs out.tier).length ≤ g.STier

/-- **TPTierFit**: a top preparation's (or initialization's) publication has
a drain target within its capacity. -/
def TPTierFit_statement : Prop :=
  ∀ (g : TPGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat) (inp : TPInputs) (out : Output),
    tpJob engineRule g unsh w inp = .ok out → (Bucket.recs out.tier).length ≤ g.drainPages * g.C

/-! ### Covering (HierarchyCovering) -/

/-- A potential job's input tiers fit their public capacities (trivially for
level one, adoptions and the initialization). -/
def jobTiersFit (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) : JobId → Prop
  | .ordinary ℓ o =>
    if ℓ = 1 ∨ cfg.digitAt ℓ o = 1 then True
    else STiersFit (sh.sep ℓ (cfg.digitAt ℓ o)) (sepInputsAt cfg sh tr words ℓ o)
  | .topPrepare o => TPTiersFit sh.prep (prepInputsAt cfg sh tr words o)
  | .topFinish o => TopTiersFit sh.top (finishInputsAt cfg sh tr words o)
  | .initialization => True

/-- Level-one cycle `c`'s fixed units. -/
def cycleUnits (cfg : Config) (tr : Trace) (c : Nat) : CycleUnits :=
  ⟨cfg.cycleLength c, fun j => tr.units (c * cfg.fanout 1 + j)⟩

/-- The model's word of position `j` of level-one cycle `c`, as a function
of the tape. -/
def cycleNative (cfg : Config) (c : Nat) (j : Fin (cfg.cycleLength c)) (words : Words) : LogicalKey → Nat :=
  jobWord cfg words 1 (cfg.cycleOrdinal c j)

/-- The old word the model passes to the first ordinal of cycle `c`. -/
def cycleOldWord (cfg : Config) (words : Words) (c : Nat) : LogicalKey → Nat :=
  jobWord cfg words 1 (cfg.cycleOrdinal c 0 - 1)

/-- Level-one cycle `c` does not publish under the tape: `runChain` on the
model's steps (the form of `DirectJobUniformHierarchy`'s covering premise). -/
def CycleStuck (cfg : Config) (tr : Trace) (words : Words) (c : Nat) : Prop :=
  ¬ ∃ out, runChain (cycleOldWord cfg words c) emptyOutput
    (selectedChainJobs 1 (cycleStepsOn (cycleUnits cfg tr c).units (cycleNative cfg c) words)) =
      .published out

/-- Covering at one selected configuration: a failure is a potential job
above level one within the horizon whose input tiers fit and which fails, or
a level-one cycle that does not publish. -/
def HierarchyCoveringAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  ∀ (tr : Trace) (words : Words), Fails cfg (hierarchyShapes cfg rows) tr words →
    (∃ j ∈ cfg.potentialJobs, (∀ o, j ≠ .ordinary 1 o) ∧ WithinHorizon cfg j ∧
      jobTiersFit cfg (hierarchyShapes cfg rows) tr words j ∧
      jobFails cfg (hierarchyShapes cfg rows) tr words j = true) ∨
    ∃ c < cfg.levelOneCycles, CycleStuck cfg tr words c

/-- **HierarchyCovering**: the first failing job's input tiers fit; a
level-one failure stops its cycle. Conditional on the tier-fit lemmas, which
it takes as hypotheses (proved separately). -/
def HierarchyCovering_statement : Prop :=
  SepTierFit_statement → TopTierFit_statement → TPTierFit_statement →
    SelectedAt HierarchyCoveringAt

/-! ### Old-home density of a uniform block (OldWordDensity) -/

/-- **OldWordDensity**: for a separated row whose previous digit's map reads
at most 64 bits, the old-home vector of a uniform 64-bit block has density at
most `oldDensity 64 n` against the uniform law on the old positions. -/
def OldWordDensity_statement : Prop := by
  classical
  exact ∀ (g : SepGeom) (keys : Finset LogicalKey) (target : keys → Fin ((g.d - 1) * g.U)),
    1 ≤ g.d - 1 → g.K + val2 (g.d - 1) ≤ 64 →
    (Fintype.card (keys → Fin (2 ^ 64)) : ℝ≥0∞)⁻¹ *
      ∑ h : keys → Fin (2 ^ 64),
        (if ∀ x, g.oldHome (h x) = (target x : Nat) then 1 else 0) ≤
      (g.oldDensity 64 keys.card : ℝ≥0∞) / (((g.d - 1) * g.U : Nat) : ℝ≥0∞) ^ keys.card

/-! ### The laws (HierarchySepLaw, HierarchyTopLaw, HierarchyLevelOne) -/

/-- The event of a potential job above level one: it is within the horizon,
its input tiers fit and it fails (empty for the inventory's speculative jobs
beyond the horizon, whose laws are then trivial). -/
def jobEvent (cfg : Config) (sh : Shapes) (tr : Trace) {Ω : Type} (words : Ω → Words) (j : JobId) :
    Set Ω :=
  {ω | WithinHorizon cfg j ∧ jobTiersFit cfg sh tr (words ω) j ∧ jobFails cfg sh tr (words ω) j = true}

/-- The separated laws at one selected configuration: premise 2 of
`DirectJobUniformHierarchyAt` for the jobs' events. -/
def HierarchySepLawAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  ∀ (N : Nat) (tr : Trace), N ≤ 2 ^ 27 → TracePremises cfg N tr →
    UnshPromise cfg (hierarchyShapes cfg rows) tr →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape cfg N) (words : Ω → Words),
      TapePremises cfg N μ tape words →
      ∀ ℓ o g, JobId.ordinary ℓ o ∈ cfg.potentialJobs → 2 ≤ ℓ →
        cfg.sepRow rows ℓ (Config.digitOf (cfg.fanout ℓ) o) = some g →
        ∃ (L : SJobLaw g) (D : ℝ≥0) (sample : Ω → L.toFinite.Outcome),
          SInputLaw L 32 D ∧ L.W = 64 ∧ D ≤ g.oldDensity 64 (32 * ((g.d - 1) * g.U)) ∧
          FiniteCoupling μ L.toFinite sample ∧
          jobEvent cfg (hierarchyShapes cfg rows) tr words (.ordinary ℓ o) ⊆
            {ω | sepFailEvent L (sample ω).1 (L.wordFn (sample ω).2)}

/-- **HierarchySepLaw**: conditional on the invariant, locality and density
statements, which it takes as hypotheses (proved separately). -/
def HierarchySepLaw_statement : Prop :=
  HierarchyInvariant_statement → HierarchyLocality_statement → OldWordDensity_statement →
    SelectedAt HierarchySepLawAt

/-- The top laws at one selected configuration: premise 3 of
`DirectJobUniformHierarchyAt` (finish, preparation, initialization). -/
def HierarchyTopLawAt (cfg : Config) (rows : List (SepGeom × Nat)) : Prop :=
  ∀ (N : Nat) (tr : Trace), N ≤ 2 ^ 27 → TracePremises cfg N tr →
    UnshPromise cfg (hierarchyShapes cfg rows) tr →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape cfg N) (words : Ω → Words),
      TapePremises cfg N μ tape words →
      (∀ o, JobId.topFinish o ∈ cfg.potentialJobs →
        ∃ (L : TopJobLaw selectedTop) (unsh : Rec → Bool) (sample : Ω → L.toFinite.Outcome),
          TopLaw L unsh 32 ∧ FiniteCoupling μ L.toFinite sample ∧
          jobEvent cfg (hierarchyShapes cfg rows) tr words (.topFinish o) ⊆
            {ω | topFailEvent L unsh (sample ω).1 (L.wordFn (sample ω).2)}) ∧
      (∀ o, JobId.topPrepare o ∈ cfg.potentialJobs →
        ∃ (L : TPJobLaw selectedTP) (unsh : Rec → Bool) (sample : Ω → L.toFinite.Outcome),
          TPLaw L 32 1 ∧ FiniteCoupling μ L.toFinite sample ∧
          jobEvent cfg (hierarchyShapes cfg rows) tr words (.topPrepare o) ⊆
            {ω | tpFailEvent L engineRule unsh (sample ω).1 (L.wordFn (sample ω).2)}) ∧
      (JobId.initialization ∈ cfg.potentialJobs →
        ∃ (L : TPJobLaw selectedTP) (input : List Rec) (sample : Ω → L.toFinite.Outcome),
          InitLaw L input ∧ FiniteCoupling μ L.toFinite sample ∧
          jobEvent cfg (hierarchyShapes cfg rows) tr words .initialization ⊆
            {ω | tpFailEvent L engineRule (fun _ => false) (sample ω).1 (L.wordFn (sample ω).2)})

/-- **HierarchyTopLaw**: conditional on the invariant and locality
statements, which it takes as hypotheses (proved separately). -/
def HierarchyTopLaw_statement : Prop :=
  HierarchyInvariant_statement → HierarchyLocality_statement → SelectedAt HierarchyTopLawAt

/-- Level one at one selected configuration: premise 5 of
`DirectJobUniformHierarchyAt` on the model's cycles (fixed units, a
measurable projection of the family tape with the uniform image law, the
model's words agreeing with the blocks on the unions). -/
def HierarchyLevelOneAt (cfg : Config) (_rows : List (SepGeom × Nat)) : Prop :=
  ∀ (N : Nat) (tr : Trace), N ≤ 2 ^ 27 → TracePremises cfg N tr →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (tape : Ω → FamilyTape cfg N) (words : Ω → Words),
      TapePremises cfg N μ tape words →
      ∃ cycTape : ∀ c, Ω → CycleTape (cycleUnits cfg tr c).units,
        (∀ c < cfg.levelOneCycles, (cycleUnits cfg tr c).n ≤ cfg.cycleLength c) ∧
        (∀ c < cfg.levelOneCycles, ∀ j, ∀ u ∈ (cycleUnits cfg tr c).units j,
          (u.recs.map Rec.key).Nodup) ∧
        (∀ c < cfg.levelOneCycles, ∀ j, (unitKeys ((cycleUnits cfg tr c).units j)).card ≤ 512) ∧
        (∀ c < cfg.levelOneCycles, Measurable (cycTape c) ∧
          μ.map (cycTape c) =
            ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape (cycleUnits cfg tr c).units))) ∧
        (∀ c < cfg.levelOneCycles, ∀ j ω k (hk : k ∈ cycleKeys (cycleUnits cfg tr c).units j),
          cycleNative cfg c j (words ω) k = cycTape c ω j ⟨k, hk⟩)

/-- **HierarchyLevelOne**. -/
def HierarchyLevelOne_statement : Prop := SelectedAt HierarchyLevelOneAt

end RebuildBound.Spec
