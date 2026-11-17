import RebuildBound.Spec.DirectJobPopulation
import RebuildBound.Spec.DirectJobReferenceGeometry

/-! Geometry-parametric, unconditional direct-job histories. The complete
source key sets are fixed before the previous and current family words are
sampled. No successful-production or tier-fit premise restricts the law. -/

open scoped ENNReal NNReal
namespace RebuildBound.Spec
open Model Model.DirectJob

namespace DirectHistoryData

/-- Replay the actual preceding direct shape, including reference fallback. -/
def stateFor (data : DirectHistoryData) (prior : Geometry) (hist : data.Hist) : ReferenceTable :=
  referenceStep (data.olderWord hist.1) (data.before hist.1)
    ⟨prior, data.word hist.2, data.priorUnits hist.1 (data.word hist.2)⟩

def directFor (data : DirectHistoryData) (prior : Geometry) (hist : data.Hist)
    (currentWord : LogicalKey → Nat) : DirectJob.Inputs :=
  (data.stateFor prior hist).inputs (data.freshUnits hist currentWord)

/-- One product history, followed by independent current words on the complete
A/B union. The law's geometry controls the shared probability input. -/
noncomputable def lawFor (data : DirectHistoryData) (prior : Geometry) (s : SepGeom) : SJobLaw s where
  KA := data.KA
  KB := data.KB
  W := 64
  Hist := data.Hist
  weight hist := data.weight hist.1 * (Fintype.card data.Words : ℝ≥0∞)⁻¹
  aIn hist := ((data.stateFor prior hist).main, (data.stateFor prior hist).tier)
  wOld hist := data.word hist.2
  bIn hist word :=
    let inp := referenceSepInputs s (data.stateFor prior hist) (data.freshUnits hist word)
    (inp.bMain, inp.bTier)

/-- Source premises and actual load; geometry linkage is a separate contract. -/
structure ValidFor (data : DirectHistoryData) (s : SepGeom) (load : Nat) : Prop where
  weight_sum : ∑ base, data.weight base = 1
  before_history : ∀ base,
    (data.before base).records.Perm (DirectPrefix.winners (data.chronology base))
  prior_keys : ∀ base h,
    ((data.chronology base ++ DirectMasks.records (data.priorUnits base (data.word h))).map
      Rec.key).toFinset = data.KA
  fresh_keys : ∀ hist word,
    ((DirectMasks.records (data.freshUnits hist word)).map Rec.key).toFinset = data.KB
  aLoad : data.KA.card ≤ load * ((s.d - 1) * s.U)
  bLoad : data.KB.card ≤ load * s.U

end DirectHistoryData

/-- The shared source law for any compatible preceding geometry, with exact
finite-word old-home density and both current/previous bit-width premises. -/
def DirectJobHistoryInputLawFor_statement : Prop :=
  ∀ (prior : Geometry) (s : SepGeom), ReferenceInputCompatible prior s →
    2 ≤ s.d → s.k < 64 → s.K + val2 (s.d - 1) ≤ 64 →
    ∀ (load : Nat) (data : DirectHistoryData), data.ValidFor s load →
      SInputLaw (data.lawFor prior s) load (s.oldDensity 64 data.KA.card)

/-- The general shared input preserves the actual direct A lanes and complete
B population; it does not replace B by a successful bounded producer. -/
def DirectJobHistoryInputMatchFor_statement : Prop :=
  ∀ (prior : Geometry) (s : SepGeom) (load : Nat) (data : DirectHistoryData),
    data.ValidFor s load →
      DirectJobInputMatch (data.lawFor prior s) (data.directFor prior)

/-- Reference chronology and populations at an arbitrary incoming capacity. -/
def DirectJobReferencePopulationFor_statement : Prop :=
  ∀ (oldWord : LogicalKey → Nat) (jobs : List ChainJob) (populations : List (Finset LogicalKey))
    (capacity : Nat),
    List.Forall₂ (fun job keys =>
      ((DirectMasks.records job.units).map Rec.key).toFinset = keys) jobs populations →
    (∀ keys ∈ populations, keys.card ≤ capacity) →
    let st := referenceChain oldWord (.ofOutput emptyOutput) jobs
    st.records.Perm (DirectPrefix.winners (chainRecords jobs)) ∧
    (st.records.map Rec.key).toFinset = directPopulationUnion populations ∧
    (directPopulationUnion populations).card ≤ capacity * jobs.length

/-- Derive the cumulative A load and chronology from a reference prefix;
only each incoming population's load needs to be checked. -/
def DirectJobHistoryPrefixValidFor_statement : Prop :=
  ∀ (data : DirectHistoryData) (s : SepGeom) (load : Nat)
    (pre : data.Base → List ChainJob) (initialWord : data.Base → LogicalKey → Nat)
    (populations : List (Finset LogicalKey)) (priorKeys : Finset LogicalKey),
    (∑ base, data.weight base = 1) →
    (∀ base, data.before base =
      referenceChain (initialWord base) (.ofOutput emptyOutput) (pre base) ∧
      data.chronology base = chainRecords (pre base)) →
    (∀ base, List.Forall₂ (fun job keys =>
      ((DirectMasks.records job.units).map Rec.key).toFinset = keys)
      (pre base) populations) →
    (∀ keys ∈ priorKeys :: populations, keys.card ≤ load * s.U) →
    (∀ base h, ((DirectMasks.records (data.priorUnits base (data.word h))).map
      Rec.key).toFinset = priorKeys) →
    data.KA = directPopulationUnion populations ∪ priorKeys →
    populations.length + 2 = s.d →
    (∀ hist word, ((DirectMasks.records (data.freshUnits hist word)).map
      Rec.key).toFinset = data.KB) →
    data.KB.card ≤ load * s.U → data.ValidFor s load

end RebuildBound.Spec
