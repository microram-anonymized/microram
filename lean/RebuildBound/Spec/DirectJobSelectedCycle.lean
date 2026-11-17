import RebuildBound.Spec.DirectJobLawTransport
import RebuildBound.Spec.DirectJobAdoption

/-!
# One selected level-one cycle from empty (trusted)

The level-one cycle correspondence. A cycle is the chronological list `steps`
of at most eight selected digits, each with its current word family and fresh
units, run by `runChain` from `emptyOutput` with the selected geometries
(`selectedChainJobs 1 steps`). The probability that the cycle does not
publish is at most the sum over its ordinals of the per-digit bounds.

**What the native side supplies** (the premises), per ordinal, on the one
ambient measure `μ`:
* a finite job law and a sample of its outcomes with `FiniteCoupling`
  (digit one: an `SJobLaw` with fixed complete B keys, at most 512, and
  `W ≥ 4`; digit `d ≥ 2`: `data.law d` of a `DirectHistoryData` valid at `d`);
* the pointwise correspondence, required only at outcomes where the cycle
  reaches that ordinal (its earlier ordinals all published). At ordinal
  `i + 1` the law's history reproduces the cycle: the old table `before` is
  the total reference prefix of the first `i` ordinals, `olderWord` agrees
  with ordinal `i`'s previous family word on that table's main records, the
  law's previous-family word agrees with ordinal `i`'s word on all of `KA`,
  `priorUnits` are ordinal `i`'s units, `freshUnits` are ordinal `i + 1`'s,
  and the law's current word agrees with ordinal `i + 1`'s word on
  `KA ∪ KB`. At ordinal zero the law's input is the adopted empty table
  with the ordinal's units and its word agrees on `KA ∪ KB`.
  Words need to agree only on these key sets; off them the native words
  are arbitrary (hash words on all keys).

**What is derived** (the proof): that a capacity failure at a reached ordinal
is the law's job failure at the sample. The actual state before ordinal
`i + 1` is the reference prefix (`DirectJobReferenceAgreement`); the record
keys of ordinals `i` and `i + 1` lie in `KA` and `KA ∪ KB` (`data.Valid`
and `DirectJobReferenceStep`: the keys of one ordinal's input and output are
the next ordinal's `KA`, i.e. `KA_{i+1} = KA_i ∪ KB_i` on the cycle); so the
word agreements give equal job results (`DirectJobWordLocal`), first for the
law's replay of ordinal `i` and then for ordinal `i + 1` itself. The union
over ordinals, the transports (`FiniteTransport`,
`DirectJobHistoryTransport`, `DirectJobDigitOneFiniteWords`) and
`DirectJobSelectedChainOutcome` (a selected cycle from empty is never
rejected, so not publishing is a capacity failure) give the bound.
No independence between ordinals is assumed and nothing is conditioned on
success; unreached ordinals need no correspondence.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- The previous family's word at ordinal `i` of a selected cycle, i.e. the
old word `runChain` passes to ordinal `i`: the cycle's initial old word at
ordinal zero, else the word of ordinal `i - 1`. -/
def selectedCycleOldWord : (LogicalKey → Nat) → List ((LogicalKey → Nat) × List Bucket) → Nat → LogicalKey → Nat
  | oldWord, _, 0 => oldWord
  | _, step :: rest, i + 1 => selectedCycleOldWord step.1 rest i
  | oldWord, [], _ + 1 => oldWord

/-- Per-digit failure budget: digit one has only the B check; a later digit
has the selected direct bound. -/
noncomputable def selectedCycleBudget (d : Nat) : ℝ≥0∞ :=
  if d = 1 then ENNReal.ofReal (1 / (2 : ℝ) ^ 117)
  else selectedDirectBound selectedDirectABudget d

/-- Ordinal zero (digit one): a coupled job law with fixed complete B keys
whose input at the sample is the adopted empty table with the ordinal's
units, and whose current word agrees with the ordinal's word on its keys. -/
def SelectedCycleDigitOneCoupled {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (steps : Ω → List ((LogicalKey → Nat) × List Bucket)) : Prop :=
  ∃ (g : SepGeom) (L : SJobLaw g) (direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs)
    (sample : Ω → L.toFinite.Outcome),
    (∑ hist, L.weight hist = 1) ∧ 4 ≤ L.W ∧
    (∀ hist hw, ((direct hist (L.wordFn hw)).bRecords.map Rec.key).toFinset = L.KB) ∧
    L.KB.card ≤ 512 ∧
    FiniteCoupling μ L.toFinite sample ∧
    ∀ ω step, (steps ω)[0]? = some step →
      direct (sample ω).1 (L.wordFn (sample ω).2) = adopt emptyOutput step.2 ∧
      ∀ k ∈ L.KA ∪ L.KB, L.wordFn (sample ω).2 k = step.1 k

/-- Ordinal `i + 1` (digit `i + 2`): a coupled selected history law whose
history reproduces the cycle wherever the cycle reaches ordinal `i + 1`:
the reference prefix of the first `i` ordinals, ordinal `i`'s previous word
on its main records, ordinal `i`'s word on `KA` and its units, ordinal
`i + 1`'s fresh units and its word on `KA ∪ KB`. -/
def SelectedCycleLaterCoupled {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (oldWord : Ω → LogicalKey → Nat) (steps : Ω → List ((LogicalKey → Nat) × List Bucket))
    (i : Nat) : Prop :=
  ∃ data : DirectHistoryData, data.Valid (i + 2) ∧
    ∃ sample : Ω → (data.law (i + 2)).toFinite.Outcome,
      FiniteCoupling μ (data.law (i + 2)).toFinite sample ∧
      ∀ ω prev cur, (steps ω)[i]? = some prev → (steps ω)[i + 1]? = some cur →
        (∃ out, runChain (oldWord ω) emptyOutput
          (selectedChainJobs 1 ((steps ω).take (i + 1))) = .published out) →
        data.before (sample ω).1.1 = referenceChain (oldWord ω) (.ofOutput emptyOutput)
          (selectedChainJobs 1 ((steps ω).take i)) ∧
        (∀ x ∈ (data.before (sample ω).1.1).main.flatMap Bucket.recs,
          data.olderWord (sample ω).1.1 x.key =
            selectedCycleOldWord (oldWord ω) (steps ω) i x.key) ∧
        (∀ k ∈ data.KA, data.word (sample ω).1.2 k = prev.1 k) ∧
        data.priorUnits (sample ω).1.1 (data.word (sample ω).1.2) = prev.2 ∧
        data.freshUnits (sample ω).1 ((data.law (i + 2)).wordFn (sample ω).2) = cur.2 ∧
        ∀ k ∈ data.KA ∪ data.KB, (data.law (i + 2)).wordFn (sample ω).2 k = cur.1 k

/-- A selected level-one cycle from empty with at most `n ≤ 8` ordinals fails
to publish with probability at most the sum of its ordinals' budgets, given a
coupled law and the pointwise correspondence at each ordinal. The per-ordinal
containment of the failure in the law's job failure is derived, not assumed. -/
def DirectJobSelectedCycle_statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (n : Nat)
    (oldWord : Ω → LogicalKey → Nat) (steps : Ω → List ((LogicalKey → Nat) × List Bucket)),
    n ≤ 8 → (∀ ω, (steps ω).length ≤ n) →
    (∀ ω, ∀ step ∈ steps ω, ∀ u ∈ step.2, (u.recs.map Rec.key).Nodup) →
    (0 < n → SelectedCycleDigitOneCoupled μ steps) →
    (∀ i, i + 1 < n → SelectedCycleLaterCoupled μ oldWord steps i) →
    μ {ω | ¬ ∃ out, runChain (oldWord ω) emptyOutput (selectedChainJobs 1 (steps ω)) =
      .published out} ≤ ∑ i ∈ Finset.range n, selectedCycleBudget (i + 1)

end RebuildBound.Spec
