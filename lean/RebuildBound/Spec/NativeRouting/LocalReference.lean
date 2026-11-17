import RebuildBound.Spec.NativeRouting.LocalBudget
import RebuildBound.Spec.NativeMatch.RoutingBudget

/-! The finite sparse reader also has a finite maximum encoded query width.
The reference marginal therefore requires only public-coordinate coverage and
injective encoding, without a separate key-provenance or fixed-width premise.
All statements cover every reply branch and use unconditional product laws. -/
namespace RebuildBound.Spec.NativeRoutingLocalReference
open Model NativeRoutingActual

/-- Maximum encoded width over every branch, including mutually inconsistent
answers to repeated queries. This auxiliary replay bound is not a pair count. -/
noncomputable def encodedWidth {Q α : Type} (encode : Q → LogicalKey) : ReadTree Q α → Nat
  | .done _ => 0
  | .read query next => max (encode query).length
      (Finset.univ.sup (fun word : Word64 => encodedWidth encode (next word)))
end RebuildBound.Spec.NativeRoutingLocalReference

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive MeasureTheory
open NativeRoutingActual NativeRoutingCoupling NativeNormalize NativeRoutingLocalBudget
open NativeMatchProduction NativeMatchRoutingBudget

/-- Every finite Word64 reader has a uniform encoded-width bound on every
reply branch. No fixed user-key width or execution-success premise is needed. -/
def NativeRoutingFiniteEncodedWidth_statement : Prop :=
  ∀ {Q α : Type} (tree : ReadTree Q α) (encode : Q → LogicalKey),
    ReadTree.allQueries
      (fun q => (encode q).length ≤ NativeRoutingLocalReference.encodedWidth encode tree) tree

/-- The finite reference joint law needs only domain coverage and injection;
finite branching supplies the replay's auxiliary width bound. -/
def NativeRoutingFiniteReference_statement : Prop :=
  ∀ {α Value : Type} [MeasurableSpace (Option Value)]
    (tree : ReadTree IdealKey.Coord α) (D : Set IdealKey.Coord)
    (encode : IdealKey.Coord → LogicalKey),
    ReadTree.allQueries D tree → Set.InjOn encode D →
    ∀ (observe : α → Value),
    ((answerLaw 64 (depth tree)).prod (tapeLaw 128)).map
      (fun p => ((NativeRoutingLocalBudget.replayResult encode tree p.1).map observe, p.2)) =
    (IdealKey.tapeLaw.map (fun tape => some (observe (ReadTree.evaluate tape tree)))).prod
      (tapeLaw 128)

/-- Every sparse production read lies in the public complete-message domain,
including inconsistent repeated-coordinate reply branches. -/
def NativeRoutingLocalDomain_statement : Prop :=
  ∀ {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h),
    ReadTree.allQueries (publicDomain ctx.geo.cfg ctx.schedule 2 (live ctx) ctx.client.shape)
      (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)

/-- Production reference replay has its canonical adaptive law jointly with
independent normalization. The existing field/counter obligations validate the
complete-message encoding. This is a marginal law, not native API agreement. -/
def NativeRoutingLocalReference_statement : Prop :=
  ∀ {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h), FieldsFit ctx → CounterFit ctx →
  ∀ {Value : Type} [MeasurableSpace (Option Value)] (observe : Acc ctx.transcriptWidth → Value),
    ((answerLaw 64 (NativeRoutingLocalBudget.readBudget ctx.geo.cfg ctx.geo.shapes ctx.unit
      ctx.schedule ctx.client)).prod (tapeLaw 128)).map
      (fun p => ((NativeRoutingLocalBudget.replayResult
        (Coordinates.referenceCode ∘ wire ctx)
        (NativeRoutingLocalReplay.readProgram ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)
        p.1).map observe, p.2)) =
    (IdealKey.tapeLaw.map (fun tape => some (observe
      (interact ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape))))).prod (tapeLaw 128)
end RebuildBound.Spec
