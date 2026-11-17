import RebuildBound.Spec.DirectJobReferenceInputs
import RebuildBound.Spec.DirectJobFiniteWords
import RebuildBound.Spec.DirectJobOldWordDensity

open scoped ENNReal NNReal
namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Data preceding one selected direct job. A fresh independent word assignment
for the previous digit is added to Base; the current job's independent words
are then supplied by SJobLaw. Nothing is conditioned on either job succeeding. -/
structure DirectHistoryData where
  KA : Finset LogicalKey
  KB : Finset LogicalKey
  Base : Type
  [baseFintype : Fintype Base]
  weight : Base → ℝ≥0∞
  before : Base → ReferenceTable
  olderWord : Base → LogicalKey → Nat
  chronology : Base → List Rec
  priorUnits : Base → (LogicalKey → Nat) → List Bucket
  freshUnits : (Base × (KA → Fin (2 ^ 64))) → (LogicalKey → Nat) → List Bucket

namespace DirectHistoryData
attribute [instance] baseFintype

abbrev Words (data : DirectHistoryData) := data.KA → Fin (2 ^ 64)
abbrev Hist (data : DirectHistoryData) := data.Base × data.Words

def word (data : DirectHistoryData) (h : data.Words) (key : LogicalKey) : Nat :=
  if hk : key ∈ data.KA then h ⟨key, hk⟩ else 0

/-- Run the preceding digit on its full reference space, including overflow. -/
def state (data : DirectHistoryData) (d : Nat) (hist : data.Hist) : ReferenceTable :=
  referenceStep (data.olderWord hist.1) (data.before hist.1)
    ⟨selectedDirectGeometry (d - 1), data.word hist.2,
      data.priorUnits hist.1 (data.word hist.2)⟩

def direct (data : DirectHistoryData) (d : Nat) (hist : data.Hist)
    (currentWord : LogicalKey → Nat) : DirectJob.Inputs :=
  (data.state d hist).inputs (data.freshUnits hist currentWord)

noncomputable def law (data : DirectHistoryData) (d : Nat) : SJobLaw (selectedDirectSep d) where
  KA := data.KA
  KB := data.KB
  W := 64
  Hist := data.Hist
  weight hist := data.weight hist.1 * (Fintype.card data.Words : ℝ≥0∞)⁻¹
  aIn hist := ((data.state d hist).main, (data.state d hist).tier)
  wOld hist := data.word hist.2
  bIn hist word :=
    let inp := referenceSepInputs (selectedDirectSep d) (data.state d hist)
      (data.freshUnits hist word)
    (inp.bMain, inp.bTier)

/-- Source chronology and populations remain explicit. Before the newly drawn
previous-family words, Base already determines the old table and its chronology.
Fresh ordering/payloads may depend on words; complete key sets must stay fixed. -/
structure Valid (data : DirectHistoryData) (d : Nat) : Prop where
  weight_sum : ∑ base, data.weight base = 1
  before_history : ∀ base,
    (data.before base).records.Perm (DirectPrefix.winners (data.chronology base))
  prior_keys : ∀ base h,
    ((data.chronology base ++ DirectMasks.records (data.priorUnits base (data.word h))).map
      Rec.key).toFinset = data.KA
  fresh_keys : ∀ hist word,
    ((DirectMasks.records (data.freshUnits hist word)).map Rec.key).toFinset = data.KB
  aLoad : data.KA.card ≤ 32 * ((d - 1) * 16)
  bLoad : data.KB.card ≤ 512

end DirectHistoryData

/-- Discharge the shared input law from an explicit product history and source
premises. Includes joint old-home density, shape and key matching on all outcomes. -/
def DirectJobHistoryInputLaw_statement : Prop :=
  ∀ d, 2 ≤ d → d ≤ 8 → ∀ data : DirectHistoryData, data.Valid d →
    SInputLaw (data.law d) 32 ((selectedDirectSep d).oldDensity 64 data.KA.card)

/-- The original direct input on the product history matches the shared law. -/
def DirectJobHistoryInputMatch_statement : Prop :=
  ∀ d (data : DirectHistoryData), data.Valid d →
    DirectJobInputMatch (data.law d) (data.direct d)

/-- Selected per-job probability with the shared input-law premise discharged.
This remains an ideal independent-word reference theorem, not native seeding or
whole-hierarchy applicability. -/
def DirectJobHistoryProbability_statement : Prop :=
  ∀ d, 2 ≤ d → d ≤ 8 → ∀ data : DirectHistoryData, data.Valid d →
    (data.law d).prob (fun hist word => ∃ e,
      runJob (selectedDirectGeometry d) ((data.law d).wOld hist) word
        (data.direct d hist word) = .failed e) ≤
      selectedDirectBound selectedDirectABudget d

end RebuildBound.Spec
