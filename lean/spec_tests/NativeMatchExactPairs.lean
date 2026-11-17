import RebuildBound.Proofs.NativeMatchExactPairs
import RebuildBound.Proofs.NativeMatchApi

/-! Local exact comparisons can fail with no VP2 event. These regressions also
separate current-unit removal from collisions in untouched frozen units. -/
namespace RebuildBound.NativeMatchExactPairsTests
open Model Spec NativeNormalize NativeNormalizePairs NativeMatch NativeMatch.Lanes
open NativeMatchTrace NativeMatchExactPairs NativeMatchDispatch

private def keyA : LogicalKey := [0]
private def keyB : LogicalKey := [1]
private def recordA : Rec := ⟨keyA, 7, false⟩
private def recordB : Rec := ⟨keyB, 11, false⟩
private def tombA : Rec := ⟨keyA, 0, true⟩
private def collapsed : LogicalKey → Stored := fun _ => 0

private def frozenCollision : Requester.State := ⟨[[some recordA]], [some recordB]⟩

theorem current_only_pairs :
    requesterPairs frozenCollision (.access recordB true) = [(keyB, keyB)] := by
  decide +kernel

/-- Frozen A and current B collide globally, but removal never compares A. -/
example : collision [(keyA, collapsed keyA), (keyB, collapsed keyB)] ∧
    ¬ PairBad collapsed (requesterPairs frozenCollision (.access recordB true)) := by
  rw [current_only_pairs]
  simp [collision, PairBad, collapsed, keyA, keyB]

/-- Both blind clear-then-insert operations leave the same current unit and preserve
the frozen unit, even with the unrelated collision. -/
example :
    (requesterStep (fun _ => .scalar) collapsed 64 frozenCollision (.access recordB true)).current =
      (Requester.step 64 frozenCollision (.access recordB true)).current ∧
    (requesterStep (fun _ => .scalar) collapsed 64 frozenCollision (.access recordB true)).frozen =
      frozenCollision.frozen := by
  decide +kernel

private def blindState : Requester.State := ⟨[], [some recordA]⟩

theorem blind_pairs : requesterPairs blindState (.access recordB true) = [(keyA, keyB)] := by
  decide +kernel

/-- A blind write has a clear even though it has no probe; an absent colliding
key also contributes no dense VP2 events. The pair inventory still catches it. -/
example : PairBad collapsed (requesterPairs blindState (.access recordB true)) := by
  rw [blind_pairs]
  simp [PairBad, collapsed, keyA, keyB]

example : requesterEvents blindState (.access recordB true) = [] := by decide +kernel

example : storedClear collapsed blindState.current [keyB] = [none] ∧
    Requester.clearKey keyB blindState.current = [some recordA] := by
  decide +kernel

/-- Forwarding and scalar fallback can select an absent colliding key even
when no dense page is involved. -/
example : storedLatest collapsed keyB [recordA] = some recordA ∧
    storedFirst collapsed keyB [recordA] = some recordA ∧
    DirectPrefix.latest keyB [recordA] = none := by
  decide +kernel

example : PairBad collapsed (listPairs [recordA] keyB) := by
  simp [PairBad, listPairs, collapsed, recordA, keyA, keyB]

private def empty : Requester.State := ⟨[], []⟩

/-- Supersession compares later lane keys even with an empty current unit. -/
example : storedSuperseded collapsed [recordA, recordB] 0 recordA = true ∧
    Requester.superseded [recordA, recordB] 0 recordA = false ∧
    requesterEvents empty (.batch [recordA, recordB]) = [] := by
  decide +kernel

example : PairBad collapsed (requesterPairs empty (.batch [recordA, recordB])) := by
  simp [PairBad, requesterPairs, unitPairs, listPairs, empty, requesterKeys,
    Bucket.recs, collapsed, recordA, recordB, keyA, keyB]

/-- Repeating a logical key is genuine supersession, not normalization failure. -/
example : storedSuperseded collapsed [recordA, recordA] 0 recordA = true ∧
    Requester.superseded [recordA, recordA] 0 recordA = true := by
  decide +kernel

example : ¬ PairBad collapsed (requesterPairs empty (.batch [recordA, recordA])) := by
  simp [PairBad, requesterPairs, unitPairs, listPairs, empty, requesterKeys,
    Bucket.recs, recordA]

private def tombPage : Page := Page.ofBucket [none, some tombA, none]

theorem tomb_page_pairs : pagePairs tombPage keyB = [(keyA, keyB)] := by
  decide +kernel

/-- A retained tombstone remains a partner; the surrounding holes and the
61 padded lanes do not contribute pairs. -/
example : (pagePairs tombPage keyB).length = 1 ∧
    PairBad collapsed (pagePairs tombPage keyB) := by
  rw [tomb_page_pairs]
  simp [PairBad, collapsed, keyA, keyB]

/-- An absent key has no VP2 event, yet normalization can return the tombstone. -/
example : denseEvents tombPage keyB true = [] ∧
    denseRecord collapsed tombPage keyB true = some tombA := by
  decide +kernel

/-- Deferred batch removal compares every query with the same original unit. -/
example : unitPairs [none, some tombA, none] [keyA, keyB] =
    [(keyA, keyA), (keyA, keyB)] := by
  decide +kernel

/-- The conservative table inventory retains obsolete repeated records and a
tombstone; the tier is included once, regardless of physical capacity. -/
private def retainedTable : Output :=
  ⟨[[some recordA, none, some recordA]], [some tombA, none]⟩

example : scanPairs retainedTable keyB = [(keyA, keyB), (keyA, keyB), (keyA, keyB)] := by
  decide +kernel

/-- The registered local coverage theorem discharges requester agreement even
when the untouched frozen key collides with the current key. -/
example : requesterStep (fun _ => .scalar) collapsed 64 frozenCollision (.access recordB true) =
    Requester.step 64 frozenCollision (.access recordB true) := by
  have hlocal := (NativeMatchExactPairsLocal collapsed).2.2.2.2.2.2
    frozenCollision (.access recordB true)
  have hpairs : ¬ PairBad collapsed (requesterPairs frozenCollision (.access recordB true)) := by
    rw [current_only_pairs]
    simp [PairBad]
  apply NativeMatchDispatchProof.requesterStep_agreement
  · simp [Requester.Unique, frozenCollision, Bucket.recs]
  · exact hlocal.not.mp hpairs
  · rintro ⟨lanes, heq⟩
    cases heq

end RebuildBound.NativeMatchExactPairsTests
