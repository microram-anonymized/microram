import RebuildBound.Spec.NativeRouting.BuildSupport
import RebuildBound.Spec.NativeRouting.LocalReplay
import RebuildBound.Spec.NativeNormalizePairs
import Mathlib.Data.Nat.Choose.Basic

/-! A canonical routing collision inventory, independent of normalization.
Build and probe keys are deduplicated per complete-message family before making
unordered pairs. The public family index uses actual charged lanes. The lane
coverage result concerns reconstruction against the complete canonical run;
transport through the adaptive reader's issued prefixes remains separate. -/
namespace RebuildBound.Spec.NativeRoutingLocalPairs
open Model Model.Hierarchy NativeMatchProduction NativeRoutingBuildSupport
open NativeRoutingFamilyExposure NativeNormalizePairs

/-- Every two positions occur once, in list order. Applied to a deduplicated
family-key list, this contains exactly one orientation of each distinct pair. -/
def unorderedPairs {Key : Type} : List Key → Pairs Key
  | [] => []
  | key :: keys => keys.map (fun other => (key, other)) ++ unorderedPairs keys

noncomputable def familyKeys {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (tape : IdealKey.Tape)
    (family : IdealKey.Family) : Finset LogicalKey :=
  buildKeys ctx tape family ∪ probeKeys ctx tape family

/-- Extra nonterminal family indices contribute no new reads and are safe to
include. This actual-q index avoids a horizon-wide family enumeration. -/
noncomputable def routingPairs {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}
    (ctx : Context member initialized h) (tape : IdealKey.Tape) : Pairs LogicalKey :=
  (completedCoordinates ctx.geo.cfg ctx.accesses).toList.flatMap fun family =>
    unorderedPairs (familyKeys ctx tape family).toList

def keyAllowance (member : ConfigurationFamily.Member) (initialized : Bool) : Nat :=
  buildAllowance member + probeSpan member initialized

def familyPairAllowance (member : ConfigurationFamily.Member) (initialized : Bool) : Nat :=
  Nat.choose (keyAllowance member initialized) 2

def routeA (member : ConfigurationFamily.Member) (initialized : Bool) : Nat :=
  (member.config initialized).levels * familyPairAllowance member initialized

/-- Ceiling division gives a geometry-only coefficient. It is unrelated to
the finite read budget used to run a replay tree. -/
def routeB (member : ConfigurationFamily.Member) (initialized : Bool) : Nat :=
  (Finset.Icc 1 (member.config initialized).levels).sum fun level =>
    (familyPairAllowance member initialized + (member.config initialized).carryPositions level - 1) /
      (member.config initialized).carryPositions level

end RebuildBound.Spec.NativeRoutingLocalPairs

namespace RebuildBound.Spec
open Model Model.Hierarchy NativeMatchProduction NativeMatchPhysical
open NativeRoutingActual NativeRoutingBuildSupport NativeRoutingLocalReplay NativeRoutingLocalPairs
open NativeNormalizePairs

/-- The pair event is exactly a collision within one indexed family support;
equal fingerprints in different families introduce no event on their own. -/
def NativeRoutingLocalPairsEvent_statement : Prop :=
  ∀ {Stored : Type} (stored : LogicalKey → Stored)
    (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h) (tape : IdealKey.Tape),
    PairBad stored (routingPairs ctx tape) ↔
      ∃ family ∈ completedCoordinates ctx.geo.cfg ctx.accesses,
        ∃ x ∈ familyKeys ctx tape family, ∃ y ∈ familyKeys ctx tape family,
          x ≠ y ∧ stored x = stored y

/-- The independently selected pair inventory has finite routing support,
and therefore measurable fibres on the unconditional canonical experiment. -/
def NativeRoutingLocalPairsFiniteRead_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), IdealKey.FiniteRead (routingPairs ctx)

/-- Each family's deduplicated population combines the checked build/probe
allowances. Ring readiness is the existing canonical guard. -/
def NativeRoutingLocalPairsKeysBound_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ tape, ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true →
    ∀ family, (familyKeys ctx tape family).card ≤ keyAllowance member initialized

/-- Every real read of a canonical full-run lane is in the indexed family
support. This includes repeated construction and level-one old-home reads;
dummies are outside the normalization inventory. -/
def NativeRoutingLocalPairsLaneCovered_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ (tape : IdealKey.Tape) t, t < ctx.accesses →
    ∀ family key, Sum.inl (family, key) ∈
      (ReadTree.reads tape (laneProgram ctx.geo.cfg ctx.geo.shapes ctx.unit
        (ctx.run tape) ctx.schedule t ctx.transcriptWidth)).map Prod.fst →
      family ∈ completedCoordinates ctx.geo.cfg ctx.accesses ∧ key ∈ familyKeys ctx tape family

/-- Actual-q affine routing-pair count. The coefficients contain no horizon,
key identities or random outcomes. This is a support/count theorem, not a
native coupling or complete-message probability endpoint. -/
def NativeRoutingLocalPairsLinear_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ tape, ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true →
      (routingPairs ctx tape).length ≤ routeA member initialized + ctx.accesses * routeB member initialized

end RebuildBound.Spec
