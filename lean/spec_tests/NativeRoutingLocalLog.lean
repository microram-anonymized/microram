import RebuildBound.Proofs.NativeRoutingLocalLog

namespace RebuildBound.SpecTests.NativeRoutingLocalLog
open Model Spec NativeRoutingActual NativeRoutingLocalLog ReadTree

example : evaluate (fun _ : Nat => (0 : Word64))
    (record (.done 37 : ReadTree Nat Nat)) = (37, []) := rfl

def repeated : ReadTree Nat (Word64 × Word64) :=
  .read 2 fun first => .read 2 fun second => .done (first, second)

/-- Logging preserves chronological replies even on a syntactically possible
branch whose repeated-coordinate answers disagree. -/
example : (resume (record repeated) [0, 1]).returned =
    some ((0, 1), [(2, 0), (2, 1)]) := rfl

example : allQueries (fun q : Nat => q = 2) (record repeated) := by
  apply (NativeRoutingLocalLogQueries repeated _).mpr
  exact ⟨rfl, fun _ => ⟨rfl, fun _ => trivial⟩⟩

example (tape : Nat → Word64) :
    evaluate tape (record repeated) = ((tape 2, tape 2), [(2, tape 2), (2, tape 2)]) := rfl

/-- The log retains both original query names even when native encoding aliases them. -/
def distinct : ReadTree Nat Unit := .read 2 fun _ => .read 3 fun _ => .done ()

example : evaluate (fun _ : Nat => (9 : Word64)) (record distinct) =
    ((), [(2, 9), (3, 9)]) := rfl

example : NativeRoutingLocalBudget.depth (record distinct) = NativeRoutingLocalBudget.depth distinct :=
  NativeRoutingLocalLogDepth distinct

example {α : Type} (tree : ReadTree IdealKey.Coord α) (tape : IdealKey.Tape) :
    let result := evaluate tape (record tree)
    evaluate (memoTape result.2) tree = result.1 ∧
      reads (memoTape result.2) tree = result.2 ∧
      ∀ entry ∈ result.2, memoTape result.2 entry.1 = entry.2 :=
  NativeRoutingLocalLogMemo tree tape

open NativeRoutingCoupling NativeNormalize MeasureTheory

/-- The native law accepts aliased encodings without an injection premise. -/
example {Value : Type} [MeasurableSpace (Option Value)]
    (observe : Unit × List (Nat × Word64) → Value) :
    (((Measure.dirac ()).prod (answerLaw 64 (NativeRoutingLocalBudget.depth (record distinct)))).prod
      (tapeLaw 128)).map
      (fun p => (p.2, (NativeRoutingLocalBudget.replayResult
        (Coordinates.nativeCode p.2 ∘ fun _ : Nat => Coordinates.Query.dummy 0 0 0)
        (record distinct) p.1.2).map observe)) =
    (((Measure.dirac ()).prod (tapeLaw 128)).prod (tapeLaw 64)).map
      (fun p => (p.1.2, some (observe (evaluate
        (p.2 ∘ Coordinates.nativeCode p.1.2 ∘ fun _ : Nat => Coordinates.Query.dummy 0 0 0)
        (record distinct))))) :=
  NativeRoutingLocalLogNative distinct (fun _ => Coordinates.Query.dummy 0 0 0) observe

end RebuildBound.SpecTests.NativeRoutingLocalLog
