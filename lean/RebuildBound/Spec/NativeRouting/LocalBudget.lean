import RebuildBound.Spec.NativeRouting.LocalReplay

/-! A finite replay budget for every Word64-branching reader. The budget is
structural and may be very loose; it is not the deduplicated normalization
pair coefficient. Decoding and native marginals use every reply branch without
conditioning on collision, capacity, or ring success. Production public-domain
and key-width coverage for the reference marginal remain separate obligations. -/
namespace RebuildBound.Spec.NativeRoutingLocalBudget
open Model Model.Hierarchy Model.Online Model.Adaptive
open NativeRoutingActual NativeRoutingCoupling NativeNormalize

/-- Finite branching gives a uniform bound, even when later client requests
and the lengths of their dependency reconstructions depend on earlier words. -/
noncomputable def depth {Q α : Type} : ReadTree Q α → Nat
  | .done _ => 0
  | .read _ next => 1 + Finset.univ.sup (fun word : Word64 => depth (next word))

/-- Decode a memoized complete-message replay using precisely its returned
words. The same decoder serves reference and native encodings. -/
def replayResult {Q α : Type} (encode : Q → LogicalKey) (tree : ReadTree Q α)
    {queries : Nat} (answers : Answers 64 queries) : Option α :=
  let history := conversions (chooseCoordinates (ReadTree.replyChooser encode tree)) answers
  (ReadTree.resume tree (history.map Prod.snd).reverse).returned

noncomputable def readBudget (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} (a : AdaptiveRun m) : Nat :=
  depth (NativeRoutingLocalReplay.readProgram cfg sh g S a)
end RebuildBound.Spec.NativeRoutingLocalBudget

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive MeasureTheory
open NativeRoutingActual NativeRoutingCoupling NativeNormalize NativeRoutingLocalBudget

/-- The maximum depth is a uniform bound on every reply branch and is the
least such bound. No execution-success premise is required. -/
def NativeRoutingFiniteBudget_statement : Prop :=
  ∀ {Q α : Type} (tree : ReadTree Q α), ReadTree.bounded (depth tree) tree ∧
    ∀ n, ReadTree.bounded n tree → depth tree ≤ n

/-- A finite iid-answer experiment always decodes a result, including cached
repeated coordinates and native aliases. -/
def NativeRoutingFiniteComplete_statement : Prop :=
  ∀ {Q α : Type} (tree : ReadTree Q α) (encode : Q → LogicalKey)
    (answers : Answers 64 (depth tree)), ∃ result, replayResult encode tree answers = some result

/-- The direct native-coordinate replay is exactly the generic reindexing of
the reference chooser used by the normalization coupling. -/
def NativeRoutingFiniteReindexed_statement : Prop :=
  ∀ {Q α : Type} (tree : ReadTree Q α) (wire : Q → Coordinates.Query) (stored : Tape 128),
    chooseReindexed (Coordinates.reindex stored)
      (ReadTree.replyChooser (Coordinates.referenceCode ∘ wire) tree) =
    chooseCoordinates (ReadTree.replyChooser (Coordinates.nativeCode stored ∘ wire) tree)

/-- Specialization to the actual sparse adaptive reader. This read budget is
independent of the normalization tape and requires no public schedule bound. -/
def NativeRoutingLocalBudget_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m),
    ReadTree.bounded (NativeRoutingLocalBudget.readBudget cfg sh g S a)
      (NativeRoutingLocalReplay.readProgram cfg sh g S a)

/-- The sparse decoded native replay has the unconditional complete-message
random-function law, jointly with the independent normalization tape. This is
a law for replayed logical operations/rows, not native API agreement. -/
def NativeRoutingLocalNativeLaw_statement : Prop :=
  ∀ {Value : Type} [MeasurableSpace (Option Value)]
    (wire : IdealKey.Coord → Coordinates.Query)
    (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat} (a : AdaptiveRun m)
    (observe : Acc m → Value),
    (((Measure.dirac ()).prod (answerLaw 64 (NativeRoutingLocalBudget.readBudget cfg sh g S a))).prod
      (tapeLaw 128)).map
      (fun p => (p.2, (replayResult (Coordinates.nativeCode p.2 ∘ wire)
        (NativeRoutingLocalReplay.readProgram cfg sh g S a) p.1.2).map observe)) =
    (((Measure.dirac ()).prod (tapeLaw 128)).prod (tapeLaw 64)).map
      (fun p => (p.1.2, some (observe (ReadTree.evaluate
        (p.2 ∘ Coordinates.nativeCode p.1.2 ∘ wire)
        (NativeRoutingLocalReplay.readProgram cfg sh g S a)))))

/-- Reusable reference-law bridge with honest all-branch support and encoded
width premises. The sparse production reader must still discharge these
premises; they are not supplied by deterministic evaluation on a single tape. -/
def NativeRoutingFiniteReferenceLaw_statement : Prop :=
  ∀ {α Value : Type} [MeasurableSpace (Option Value)]
    (tree : ReadTree IdealKey.Coord α) (D : Set IdealKey.Coord)
    (encode : IdealKey.Coord → LogicalKey) (width : Nat),
    ReadTree.allQueries D tree → Set.InjOn encode D →
    ReadTree.allQueries (fun q => (encode q).length ≤ width) tree →
    ∀ (observe : α → Value),
    ((answerLaw 64 (depth tree)).prod (tapeLaw 128)).map
      (fun p => ((replayResult encode tree p.1).map observe, p.2)) =
    (IdealKey.tapeLaw.map (fun tape => some (observe (ReadTree.evaluate tape tree)))).prod
      (tapeLaw 128)
end RebuildBound.Spec
