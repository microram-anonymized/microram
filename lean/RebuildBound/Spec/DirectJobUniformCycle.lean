import RebuildBound.Spec.DirectJobSelectedCycle
import RebuildBound.Spec.DirectJobUniform

/-!
# One selected cycle on the uniform word tape (trusted)

`DirectJobSelectedCycle` bounds a selected level-one cycle from premises that
a native model has to supply per ordinal: a coupled job law and the pointwise
correspondence between the law's history and the cycle. This file instantiates
all of them on the ideal word model, leaving one premise.

The cycle has `n ≤ 8` ordinals with fixed fresh units `units j` (the records
written into level one during ordinal `j`; their keys are the only randomness
the words see). Ordinal `j`'s current family draws one uniform 64-bit word per
key of its complete union `KA_j ∪ KB_j = cycleKeys units j`, the keys of
units `0 … j`, independently across keys and ordinals: the tape `CycleTape`
is the product of these blocks with the uniform measure. The native word of
ordinal `j` may be any function (a hash on all of ℕ) that agrees with the
tape's block on `cycleKeys units j`; off those keys it is unconstrained.

Then the cycle, run by `runChain` from `emptyOutput`, fails to publish with
probability at most the sum of the per-digit budgets. The proof constructs,
per ordinal, the digit-one law or the `DirectHistoryData` whose base is the
earlier blocks of the tape, discharges `Valid` from `DirectJobHistoryPrefixValid`,
the coupling from the coordinate split (`FiniteCoupling` of a projection of the
uniform tape) and the correspondence by definition, then applies
`DirectJobSelectedCycle`. This is the ideal independent-word reference
theorem for one cycle; identifying native hash words with the tape's blocks on
`cycleKeys` and native execution with `runChain` remains native scope.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- The complete key set of a unit list. -/
def unitKeys (units : List Bucket) : Finset LogicalKey :=
  ((DirectMasks.records units).map Rec.key).toFinset

/-- The keys of ordinals `0 … j` of a cycle with fixed units: ordinal `j`'s
complete union `KA_j ∪ KB_j`. -/
def cycleKeys {n : Nat} (units : Fin n → List Bucket) (j : Fin n) : Finset LogicalKey :=
  (Finset.univ.filter (· ≤ j)).biUnion fun p => unitKeys (units p)

/-- The uniform word tape of a cycle: per ordinal, one 64-bit word per key
of its complete union. -/
abbrev CycleTape {n : Nat} (units : Fin n → List Bucket) : Type :=
  ∀ j : Fin n, (cycleKeys units j → Fin (2 ^ 64))

/-- The cycle's chronological steps: ordinal `j`'s native word and fresh units. -/
def cycleSteps {n : Nat} (units : Fin n → List Bucket)
    (native : Fin n → CycleTape units → LogicalKey → Nat) (ω : CycleTape units) :
    List ((LogicalKey → Nat) × List Bucket) :=
  List.ofFn fun j => (native j ω, units j)

/-- A selected cycle from empty on the uniform word tape fails to publish with
probability at most the sum of its ordinals' budgets, whenever each ordinal's
native word agrees with its tape block on the ordinal's complete union. -/
def DirectJobUniformCycle_statement : Prop :=
  ∀ (n : Nat), n ≤ 8 → ∀ (units : Fin n → List Bucket),
    (∀ j, ∀ u ∈ units j, (u.recs.map Rec.key).Nodup) →
    (∀ j, (unitKeys (units j)).card ≤ 512) →
    ∀ [MeasurableSpace (CycleTape units)] [MeasurableSingletonClass (CycleTape units)]
      (oldWord : CycleTape units → LogicalKey → Nat)
      (native : Fin n → CycleTape units → LogicalKey → Nat),
    (∀ j ω k (hk : k ∈ cycleKeys units j), native j ω k = ω j ⟨k, hk⟩) →
    ProbabilityTheory.uniformOn (Set.univ : Set (CycleTape units))
      {ω | ¬ ∃ out, runChain (oldWord ω) emptyOutput
        (selectedChainJobs 1 (cycleSteps units native ω)) = .published out} ≤
      ∑ i ∈ Finset.range n, selectedCycleBudget (i + 1)

end RebuildBound.Spec
