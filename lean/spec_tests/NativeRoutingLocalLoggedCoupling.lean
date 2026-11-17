import RebuildBound.Proofs.NativeRoutingLocalLoggedCoupling

/-! Logged replay retains chronological logical query names while cached
complete messages may reuse replies. Family separation is part of coupling. -/
namespace RebuildBound.NativeRoutingLocalLoggedCouplingTests
open Model Spec NativeRoutingActual NativeRoutingCoupling NativeNormalize
open NativeRoutingLocalBudget NativeRoutingLocalLog NativeRoutingLocalLoggedCoupling
open NativeRoutingLocalLoggedCouplingProof

private def first : IdealKey.Coord := .inl ((1, 0), [0])
private def second : IdealKey.Coord := .inl ((1, 0), [1])

/-- Repeated queries and dummy tokens do not themselves create an alias. -/
example (stored : Tape 128) :
    ¬memoAlias stored [(first, 0), (first, 7), (.inr (0, 0), 7)] := by
  simp [memoAlias, first]

/-- Distinct logical keys in one family are charged even when replies differ. -/
example : memoAlias (fun _ => (0 : Fingerprint 128)) [(first, 0), (second, 7)] := by
  refine ⟨(1, 0), [0], [1], ?_, ?_, ?_, rfl⟩ <;> simp [first, second]

private def two : ReadTree Bool (Word64 × Word64) :=
  .read false fun x => .read true fun y => .done (x, y)

/-- Sampled replay's returned log is chronological, even when both logical
query names use the same complete-message cache coordinate. -/
example (tape : Tape 64) :
    NativeRoutingLocalBudget.replayResult (fun _ : Bool => []) (record two)
      (sample (paddedChooser 0 (chooseCoordinates (ReadTree.replyChooser (fun _ : Bool => [])
        (record two)))) tape (depth (record two))) =
      some ((tape [], tape []), [(false, tape []), (true, tape [])]) := by
  exact NativeRoutingLocalBudgetProof.replay_sampled (record two) (fun _ => []) 0 tape

private def families : Bool → Coordinates.Query
  | false => .real 0 1 [0]
  | true => .real 0 2 [1]

/-- A collision of stored keys across distinct message families cannot change
the finite logged result, for any iid answers or normalization function. -/
example (stored : Tape 128) (answers : Answers 64 (depth (record two))) result
    (hr : NativeRoutingLocalBudget.replayResult (Coordinates.referenceCode ∘ families)
      (record two) answers = some result) :
    NativeRoutingLocalBudget.replayResult (Coordinates.nativeCode stored ∘ families)
      (record two) answers = some result := by
  apply logged_reindex two families stored answers result hr
  intro a _ b _ he
  cases a <;> cases b
  · rfl
  · have hf := (NativeRoutingRealCodeFamily stored 0 0 1 2 [0] [1]).mp he
    have hlevel := congrArg Fin.val hf.2.1
    norm_num at hlevel
  · have hf := (NativeRoutingRealCodeFamily stored 0 0 2 1 [1] [0]).mp he
    have hlevel := congrArg Fin.val hf.2.1
    norm_num at hlevel
  · rfl

/-- The encoded conversion log reverses chronological output order; every
reference reply is retained, including replies for repeated logical reads. -/
example (encode : Bool → LogicalKey) (answers : Answers 64 (depth (record two))) result
    (hr : NativeRoutingLocalBudget.replayResult encode (record two) answers = some result) :
    conversions (chooseCoordinates (ReadTree.replyChooser encode (record two))) answers =
      (result.2.map fun entry => (encode entry.1, entry.2)).reverse :=
  NativeRoutingLocalLoggedHistory two encode answers result hr

end RebuildBound.NativeRoutingLocalLoggedCouplingTests
