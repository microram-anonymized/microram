import RebuildBound.Proofs.NativeRoutingLocalReference

namespace RebuildBound.SpecTests.LocalReference
open Model Spec NativeRoutingActual NativeRoutingLocalReference

/-- The maximum sees a wider query on an unselected branch. -/
def variableWidth : ReadTree Nat Unit :=
  .read 1 fun word => if word = 0 then .done () else .read 7 fun _ => .done ()

def encode (n : Nat) : LogicalKey := List.replicate n 0

example : ReadTree.allQueries (fun q => (encode q).length ≤ encodedWidth encode variableWidth)
    variableWidth := NativeRoutingFiniteEncodedWidth variableWidth encode

/-- The second reply to a repeated coordinate may disagree with the first;
the structural bound still includes the query selected by that branch. -/
def inconsistent : ReadTree Nat Unit :=
  .read 0 fun first => .read 0 fun second =>
    if first = second then .done () else .read 19 fun _ => .done ()

example : ReadTree.allQueries (fun q => (encode q).length ≤ encodedWidth encode inconsistent)
    inconsistent := NativeRoutingFiniteEncodedWidth inconsistent encode

example : encodedWidth encode (.done () : ReadTree Nat Unit) = 0 := rfl

example : 7 ≤ encodedWidth encode variableWidth := by
  have h := NativeRoutingFiniteEncodedWidth variableWidth encode
  have hbranch := h.2 (1 : Word64)
  simp only [variableWidth, ReadTree.allQueries, show (1 : Word64) ≠ 0 by decide,
    ↓reduceIte] at hbranch
  exact hbranch.1

example : 19 ≤ encodedWidth encode inconsistent := by
  have h := NativeRoutingFiniteEncodedWidth inconsistent encode
  have hbranch := (h.2 (0 : Word64)).2 (1 : Word64)
  simp only [inconsistent, ReadTree.allQueries, show (0 : Word64) ≠ 1 by decide,
    ↓reduceIte] at hbranch
  exact hbranch.1

open NativeMatchProduction NativeMatchRoutingBudget NativeRoutingCoupling NativeNormalize
open MeasureTheory Model.Hierarchy Model.Adaptive

/-- Existing public field/counter obligations suffice; no fixed input width or
capacity/ring-success premise is needed for this unconditional marginal. -/
example {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hf : FieldsFit ctx) (hc : CounterFit ctx)
    {Value : Type} [MeasurableSpace (Option Value)] (observe : Acc ctx.transcriptWidth → Value) :
    ((answerLaw 64 (NativeRoutingLocalBudget.readBudget ctx.geo.cfg ctx.geo.shapes ctx.unit
      ctx.schedule ctx.client)).prod (tapeLaw 128)).map
      (fun p => ((NativeRoutingLocalBudget.replayResult (Coordinates.referenceCode ∘ wire ctx)
        (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)
        p.1).map observe, p.2)) =
    (IdealKey.tapeLaw.map (fun tape => some (observe
      (interact ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape))))).prod (tapeLaw 128) :=
  NativeRoutingLocalReference ctx hf hc observe

end RebuildBound.SpecTests.LocalReference
