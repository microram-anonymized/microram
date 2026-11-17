import RebuildBound.Spec.Model.DirectProducer
import RebuildBound.Spec.Model.DirectScan
namespace RebuildBound.Spec
open Model Model.DirectProducer

def DirectProducerExact_statement : Prop :=
  ∀ (digit output U : Nat) (home : Nat → Nat) (chunks : List (List Nat)),
    chunks.flatten.Nodup → (∀ i ∈ chunks.flatten, home i < U) →
    let homes := DirectGroups.groups U home chunks.flatten
    build digit output U home chunks =
      if DirectB.excess 64 homes ≤ DirectDrain.tierCapacity digit output
      then some (DirectB.main 64 homes, DirectRemaining.run 64 chunks.flatten homes)
      else none

def DirectProducerFailure_statement : Prop :=
  ∀ (digit output U : Nat) (home : Nat → Nat) (chunks : List (List Nat)),
    chunks.flatten.Nodup → (∀ i ∈ chunks.flatten, home i < U) →
    (build digit output U home chunks = none ↔
      DirectDrain.tierCapacity digit output <
        DirectB.excess 64 (DirectGroups.groups U home chunks.flatten))

def DirectProducerSuccess_statement : Prop :=
  ∀ (digit output U : Nat) (home : Nat → Nat) (chunks main : List (List Nat))
    (tier : List Nat),
    chunks.flatten.Nodup → (∀ i ∈ chunks.flatten, home i < U) →
    build digit output U home chunks = some (main, tier) →
    (main.flatten ++ tier).Perm chunks.flatten ∧
    (main.flatten ++ tier).Nodup ∧
    tier.length = DirectB.excess 64 (DirectGroups.groups U home chunks.flatten) ∧
    tier.length ≤ DirectDrain.tierCapacity digit output

def DirectProducerRechunk_statement : Prop :=
  ∀ (digit output U : Nat) (home : Nat → Nat) (first second : List (List Nat)),
    first.flatten = second.flatten →
    build digit output U home first = build digit output U home second

/-- The producer main is exactly the result of per-home source chunk scans. -/
def DirectProducerScanned_statement : Prop :=
  ∀ (U : Nat) (home : Nat → Nat) (chunks : List (List Nat)),
    DirectB.main 64 (DirectGroups.groups U home chunks.flatten) =
      (List.range U).map (fun h =>
        (DirectScan.run 64 (DirectScan.candidates home h chunks)).selected)

end RebuildBound.Spec
