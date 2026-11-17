import RebuildBound.Spec.DirectProducer
import RebuildBound.Proofs.DirectGroups
import RebuildBound.Proofs.DirectRemaining
import RebuildBound.Proofs.DirectScan
import Mathlib.Tactic
namespace RebuildBound
open Model Model.DirectProducer

theorem DirectProducerExact : Spec.DirectProducerExact_statement := by
  intro digit output U home chunks hn hb
  dsimp only
  have hg := DirectGroupsGrouped U home chunks.flatten hn hb
  dsimp only [build]
  rw [DirectDrainExact _ _ _ (by simp)]
  simp only [List.nil_append]
  rw [DirectRemainingChunks]
  rw [DirectRemainingOccupancy 64 chunks.flatten _ hg]
  split_ifs <;> rfl

theorem DirectProducerFailure : Spec.DirectProducerFailure_statement := by
  intro digit output U home chunks hn hb
  rw [DirectProducerExact digit output U home chunks hn hb]
  split_ifs <;> simp_all

theorem DirectProducerSuccess : Spec.DirectProducerSuccess_statement := by
  intro digit output U home chunks main tier hn hb hs
  have hg := DirectGroupsGrouped U home chunks.flatten hn hb
  rw [DirectProducerExact digit output U home chunks hn hb] at hs
  split_ifs at hs with hc
  · have he := Option.some.inj hs
    cases he
    rw [DirectRemainingDrain 64 chunks.flatten _ hg]
    exact ⟨DirectSelectConservation 64 _ _ hg,
      DirectSelectUnique 64 _ _ hg, DirectSelectOccupancy 64 _ _ hg,
      (DirectSelectOccupancy 64 _ _ hg).le.trans hc⟩

theorem DirectProducerRechunk : Spec.DirectProducerRechunk_statement := by
  intro digit output U home first second he
  dsimp only [build]
  rw [he]
  congr 1
  apply DirectDrainRechunk _ _ _ _ (by simp)
  rw [DirectRemainingChunks, DirectRemainingChunks, he]

theorem DirectProducerScanned : Spec.DirectProducerScanned_statement := by
  intro U home chunks
  simp only [DirectB.main, DirectGroups.groups, List.map_map]
  apply List.map_congr_left
  intro h hh
  exact (DirectScanHomeSelected 64 home h chunks).symm

-- Empty input is a successful producer. Out-of-range homes violate the
-- contract: their records remain in the tier despite zero grouped excess.
example : build 1 0 1 (fun _ => 0) [] = some ([[]], []) := by decide
example : build 1 0 0 (fun _ => 0) [[0]] = none := by decide
example : build 1 1 0 (fun _ => 0) [[0]] = some ([], [0]) := by decide
-- Digit one can use its full output tier; later digits cannot borrow it.
example : (build 1 128 1 (fun _ => 0) [List.range 130]).isSome = true := by decide
example : build 2 128 1 (fun _ => 0) [List.range 130] = none := by decide
end RebuildBound
