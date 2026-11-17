import RebuildBound.Proofs.HierarchyInvariant.Contracts

/-!
# HierarchyInvariant

Under the trace
premises and the unshadowed promise, at both selected configurations and
under every tape, the potential jobs' inputs meet their structural contracts
(`SInputShape`, `TPShape`, `TopShape`), their key sets (record sets at the
finish) do not depend on the tape, their keys lie below `N`, they meet the
loads, and no key is lost below the top.

Proof outline (files of `HierarchyInvariant/`):

1. `Basic.lean`: homes at a power-of-two digit, digits, the carry's family
   (`jobWord_carry`), the winners `win A B` as a list, a key set and a record
   set, cardinality from distinct keys below `N`.
2. `Facts.lean`: the lower configuration facts (`LowFacts`) and compatible
   top dimensions/capacity (`TopFacts`); the selected `Facts` interface remains
   a specialization.
3. `Provenance.lean`: the reference preparation and finish only move records
   (no shape hypothesis), for keys below `N` beyond the horizon.
4. `Steps.lean`, `Low.lean`: below the top, by induction on `(ℓ, v)`, every
   partial after a potential ordinal has `d U_ℓ` buckets of 64 lanes at
   `digitHome K_ℓ d` under its family, distinct keys below `N`, at most
   `32 d U_ℓ` keys, and its records are the winners of the inputs (level one:
   `DirectJobPublication` or the reference fallback; digit one: the carry;
   later digits: ST1/ST2 on `SInputShape`). Record sets are tape-invariant.
5. `Top.lean`, `TopIndFor.lean`: the top's tables within the horizon have
   `top.T` buckets at `w mod top.T`, with initialization's own geometry
   (initialization and preparation: TP12; finish: T3top on `TopShape`, with
   the unshadowed promise). `TopInd.lean` retains the selected wrappers.
6. `ContractsFor.lean`: the fields of `JobContracts`, using the actual
   key-capacity link; `Contracts.lean` retains the selected wrappers.
-/

open RebuildBound.HierarchyInvariantProof in
/-- **HierarchyInvariant.** -/
theorem RebuildBound.HierarchyInvariant : RebuildBound.Spec.HierarchyInvariant_statement := by
  unfold RebuildBound.Spec.HierarchyInvariant_statement RebuildBound.Spec.SelectedAt
    RebuildBound.Spec.HierarchyInvariantAt
  exact ⟨fun N tr hN hT hU words => contracts uniformFacts hN hT hU words,
    fun N tr hN hT hU words => contracts halfFanoutFacts hN hT hU words⟩
