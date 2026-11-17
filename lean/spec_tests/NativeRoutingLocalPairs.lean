import RebuildBound.Proofs.NativeMatchLocalBound

/-! Pair orientation, repeated keys, family separation, actual-q indexing and
the conservative numerical coefficients are checked independently here. -/
namespace RebuildBound.NativeRoutingLocalPairsTests
open Model Spec NativeRoutingLocalPairs NativeNormalizePairs NativeRoutingBuildSupport

example : unorderedPairs ([0, 0, 1] : List Nat) = [(0, 0), (0, 1), (0, 1)] := rfl
example : unorderedPairs ([0, 1, 2] : List Nat) = [(0, 1), (0, 2), (1, 2)] := rfl

/-- A repeated logical identity alone never creates a collision event. -/
example : ¬ PairBad (fun _ : Nat => 0) (unorderedPairs [7, 7]) := by
  simp [PairBad, unorderedPairs]

/-- Colliding retired keys in different singleton supports add no pair. -/
example : ¬ PairBad (fun _ : Nat => 0) (unorderedPairs [0] ++ unorderedPairs [1]) := by
  simp [PairBad, unorderedPairs]

/-- A shared family exposes the same distinct-key collision. -/
example : PairBad (fun _ : Nat => 0) (unorderedPairs [0, 1]) := by
  simp [PairBad, unorderedPairs]

example (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : NativeMatchProduction.Context member initialized h) (tape : IdealKey.Tape)
    (family : IdealKey.Family) :
    familyKeys ctx tape family ∪ familyKeys ctx tape family = familyKeys ctx tape family :=
  Finset.union_self _

/-- The public family index is unaffected by unused certificate horizon. -/
example (cfg : Model.Config) (q horizon : Nat) :
    completedCoordinates { cfg with horizon := horizon } q = completedCoordinates cfg q := rfl

section Combined
open Model.Hierarchy NativeMatchProduction NativeMatchPhysical NativeMatchLocalApi MeasureTheory

open NativeMatchLocalBound
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

/-- A stopped reference run empties only the normalization inventory; the
same branch is still included in the shared error event. -/
example (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (stored : NativeNormalize.Tape 128)
    (hr : ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = false) :
    normalizationPairs ctx tape = [] ∧ bad ctx (tape, stored) := by
  exact ⟨by simp [normalizationPairs, hr], Or.inr (Or.inr hr)⟩

/-- Exact and routing collisions are covered by the very same guarded event. -/
example (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (stored : NativeNormalize.Tape 128)
    (hr : ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true) :
    PairBad stored (normalizationPairs ctx tape) ↔
      PairBad stored (exactPairs ctx tape) ∨ PairBad stored (routingPairs ctx tape) := by
  simpa only [normalizationPairs, hr, ↓reduceIte] using
    NativeNormalizePairsEvent.1 stored (exactPairs ctx tape) (routingPairs ctx tape)

/-- The combined probability witness uses the registered theorem. -/
example (ctx : Context member initialized h) (hm : member ∈ ConfigurationFamily.members)
    (hv : ctx.Valid) :
    (IdealKey.tapeLaw.prod (NativeNormalize.tapeLaw 128))
      {p | PairBad p.2 (normalizationPairs ctx p.1)} ≤
      pairBound 128 (routeA member initialized +
        ctx.accesses * (NativeMatchExactCounts.perAccess member + routeB member initialized)) :=
  NativeMatchLocalBoundNormalize member initialized h ctx hm hv

end Combined

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
example : ∀ member ∈ ConfigurationFamily.members, ∀ initialized : Bool,
    337365056 ≤ routeA member initialized ∧
    routeA member initialized ≤ 32996938953720914226144 ∧
    1976750 ≤ routeB member initialized ∧
    routeB member initialized ≤ 38105652067504887609 ∧
    1987566 ≤ NativeMatchExactCounts.perAccess member + routeB member initialized ∧
    NativeMatchExactCounts.perAccess member + routeB member initialized ≤ 38105652134076881273 := by
  simp only [NativeRoutingLocalPairs.routeA, NativeRoutingLocalPairs.routeB, familyPairAllowance, Nat.choose_two_right]
  decide +kernel

end RebuildBound.NativeRoutingLocalPairsTests
