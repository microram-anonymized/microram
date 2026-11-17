import RebuildBound.Spec.NativeRouting.Actual
set_option linter.unusedSimpArgs false
namespace RebuildBound.NativeRoutingActualTests
open Model Model.Adaptive Spec NativeRoutingActual NativeMatchPhysical NativeNormalize NativeRoutingCoupling

private def repeated : ReadTree Unit Bool :=
  .read () fun first => .read () fun second => .done (first == second)

-- The second answer slot differs, but repeated routing coordinates retain
-- the first tape word in the actual shared memoized conversion machinery.
example : (conversions (chooseCoordinates (ReadTree.replyChooser (fun _ => [7]) repeated))
    (fun i : Fin 2 => if i.val = 0 then 9 else 17)).map Prod.snd = [9, 9] := by decide

private def causal : ReadTree Bool Word64 :=
  .read false fun first => .read (first == 9) fun second => .done second

example : (conversions (chooseCoordinates (ReadTree.replyChooser (fun q => if q then [2] else [1]) causal))
    (fun i : Fin 2 => if i.val = 0 then 9 else 17)).map Prod.snd = [17, 9] := by decide

private def old : LiveTable 2 := ⟨0, (1, 2), 0, false⟩
private def recent : LiveTable 2 := ⟨1, (2, 3), 1, true⟩
private def snapshot : Nat → List (LiveTable 2) := fun _ => [old, recent]
private def shape : List Kind := [.blind, .chunk 2, .probe]

private theorem composed : composeEntries [old, recent] =
    [⟨recent, false⟩, ⟨recent, true⟩, ⟨old, false⟩] := by
  simp [composeEntries, sourceEntries, old, recent, List.mergeSort, entryBefore]

-- Four reserved prefix entries and the intervening dense tier both remain
-- in the full physical stride; hashed positions are absolute indices.
private theorem fixture_stride : physicalStride 2 [old, recent] = 7 := by simp [physicalStride, physicalPlan, composed]
private theorem fixture_hashed : hashedSlots 2 [old, recent] = [(4, (2, 3)), (6, (1, 2))] := by
  rw [hashedSlots, composed]
  decide
example : reservedBefore (reservationCost 2 snapshot shape) 1 = 0 := by decide
example : reservedBefore (reservationCost 2 snapshot shape) 4 = 21 := by
  simp [dummyToken, reservedBefore, reservationCost, shape, shapePattern, shapeWidths,
    Kind.width, Kind.probes, Model.OnlineBatch.chunkStart, snapshot, fixture_stride, fixture_hashed]
example : dummyToken 2 snapshot shape 1 0 = 5 := by
  simp [dummyToken, reservedBefore, reservationCost, shape, shapePattern, shapeWidths,
    Kind.width, Kind.probes, Model.OnlineBatch.chunkStart, snapshot, fixture_stride, fixture_hashed]
example : dummyToken 2 snapshot shape 2 0 = 12 := by
  simp [dummyToken, reservedBefore, reservationCost, shape, shapePattern, shapeWidths,
    Kind.width, Kind.probes, Model.OnlineBatch.chunkStart, snapshot, fixture_stride, fixture_hashed]
example : dummyToken 2 snapshot shape 3 1 = 21 := by
  simp [dummyToken, reservedBefore, reservationCost, shape, shapePattern, shapeWidths,
    Kind.width, Kind.probes, Model.OnlineBatch.chunkStart, snapshot, fixture_stride, fixture_hashed]

-- Repeated and superseded input keys are retained in the finite key budget.
example (r : Rec) : usedKeys (⟨[.blind r, .batch [r,r]], [r], fun _ => false⟩ : Model.OnlineBatch.BatchRun) =
    [r.key,r.key,r.key,r.key] := by simp [usedKeys, Model.OnlineBatch.slots, Model.OnlineBatch.Op.lanes]

private def boundedClient : AdaptiveRun 0 :=
  ⟨[.probe], [], fun _ => false, fun _ lane =>
    if lane = 0 then ⟨List.replicate 16 1, 0, false⟩ else default⟩

-- Production clients return the empty default for unused lanes. The public
-- width condition concerns the sole issued lane, and remains satisfiable.
example : InputWidth boundedClient 16 := by
  constructor
  · simp [boundedClient]
  · intro before kind after hshape rows _ lane hl
    have hlen := congrArg List.length hshape
    have hb : before = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [boundedClient, List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    subst before
    have he : kind = .probe ∧ after = [] := by simpa [boundedClient] using hshape.symm
    rcases he with ⟨rfl, rfl⟩
    have hzero : lane = 0 := by simpa only [Kind.width, Nat.lt_one_iff] using hl
    simp [boundedClient, hzero]

example : (boundedClient.client [] 1).key = [] := rfl

end RebuildBound.NativeRoutingActualTests
