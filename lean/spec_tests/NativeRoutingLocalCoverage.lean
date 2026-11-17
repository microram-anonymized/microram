import RebuildBound.Proofs.NativeRoutingLocalCoverage
import RebuildBound.Proofs.NativeRoutingLocalReference

/-! Prefix and alias regressions retain complete message families and exercise
future extension, demand-driven initialization, and whole adaptive read lists. -/
namespace RebuildBound.NativeRoutingLocalCoverageTests
open Model Model.Hierarchy Model.Online Model.OnlineBatch Model.Adaptive Spec
open NativeRoutingActual NativeRoutingLocalReplay NativeRoutingLocalPairs NativeNormalizePairs
open NativeMatchProduction NativeNormalize NativeRoutingCoupling NativeMatchRoutingBudget

private def cfg : Config := ⟨[4], 2, 8, 32, 128, true⟩
private def unit : OnlineGeom := ⟨64, 1⟩
private def recordA : Rec := ⟨[0], 7, false⟩
private def recordB : Rec := ⟨[1], 9, false⟩
private def issued : BatchRun := ⟨[.probe recordA], [recordB], fun _ => false⟩
private def future : BatchRun :=
  ⟨[.probe recordA, .blind recordB, .batch [recordA, recordB]], [recordB], fun _ => false⟩
private def plan : Schedule := fun _ => ⟨0, [(2, 0)]⟩

/-- An initialized base gives a genuine construction read; arbitrary future
requests preserve the complete first-lane program, for all reply branches. -/
example (sh : Shapes) : laneProgram cfg sh unit issued plan 0 2 =
    laneProgram cfg sh unit future plan 0 2 := by
  rfl

/-- Two blind adaptive decisions read neither construction nor routing words,
even with a nonempty initialized base and arbitrary client choices. -/
example (sh : Shapes) (tape : IdealKey.Tape) (choose : List (Fin 2 → Nat) → Nat → Rec) :
    ReadTree.reads tape (NativeRoutingLocalReplay.readProgram cfg sh unit plan
      (⟨[.blind, .blind], [recordB], fun _ => false, choose⟩ : AdaptiveRun 2)) = [] := by
  rfl

/-- A full fingerprint collision does not alias distinct complete families. -/
example (stored : Tape 128) (key key' : LogicalKey) :
    Coordinates.nativeCode stored (.real 0 1 key) ≠
      Coordinates.nativeCode stored (.real 0 2 key') := by
  intro he
  have hfields := (NativeRoutingRealCodeFamily stored 0 0 1 2 key key').mp he
  have hlevel := congrArg Fin.val hfields.2.1
  norm_num at hlevel

/-- Conversely, any two distinct read coordinates with one native message
force the same canonical routing inventory to be bad. The hypotheses contain
no capacity/ring-success premise or lifetime normalization-injectivity claim. -/
example {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members) (hv : ctx.Valid)
    (hf : FieldsFit ctx) (hc : CounterFit ctx) (tape : IdealKey.Tape) (stored : Tape 128)
    (a b : IdealKey.Coord)
    (ha : a ∈ (ReadTree.reads tape (NativeRoutingLocalReplay.readProgram
      ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)).map Prod.fst)
    (hb : b ∈ (ReadTree.reads tape (NativeRoutingLocalReplay.readProgram
      ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.client)).map Prod.fst)
    (hne : a ≠ b)
    (he : Coordinates.nativeCode stored (wire ctx a) = Coordinates.nativeCode stored (wire ctx b)) :
    PairBad stored (routingPairs ctx tape) := by
  by_contra hs
  exact hne (NativeRoutingLocalCoverageProof.native_injective NativeRoutingLocalDomain ctx hm hv hf hc tape stored hs ha hb he)

end RebuildBound.NativeRoutingLocalCoverageTests
