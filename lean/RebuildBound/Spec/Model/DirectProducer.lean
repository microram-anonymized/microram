import RebuildBound.Spec.Model.DirectGroups
import RebuildBound.Spec.Model.DirectRemaining
import RebuildBound.Spec.Model.DirectDrain
/-! Composed finite logical B producer on already deduplicated occurrence
indices. Actual home filters construct stable groups; selected prefixes clear
source buckets; the source-order remainder drains through checked appends.
Digit one uses the configured output tier, later digits a 64-slot producer
tier. `none` prevents a publishable result but does not model native scratch
rollback. SIMD, cached bytes and publication control flow are not extracted. -/
namespace RebuildBound.Model.DirectProducer

def build (digit output U : Nat) (home : Nat → Nat) (chunks : List (List Nat)) :
    Option (List (List Nat) × List Nat) :=
  let homes := DirectGroups.groups U home chunks.flatten
  let remaining := chunks.map (fun source => DirectRemaining.run 64 source homes)
  (DirectDrain.run (DirectDrain.tierCapacity digit output) [] remaining).map
    (fun tier => (DirectB.main 64 homes, tier))

end RebuildBound.Model.DirectProducer
