import RebuildBound.Spec.NativeMatch.Api
import RebuildBound.Spec.NativeMatch.ExactPairs

/-! Local normalization agreement for the existing logical-routing experiment.
The native engine is unchanged. Its reference pair inventory covers exact-byte
comparisons and the existing VP2 inventory covers approximate matches. Sparse
complete-message routing and an affine geometry count remain separate gates. -/
namespace RebuildBound.Spec.NativeMatchLocalApi
open Model Model.Online NativeMatchProduction NativeMatchExactPairs NativeNormalizePairs
variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

/-- Reference prestates depend on the canonical routing tape, never on stored
fingerprints. Every actually issued slot and operation is charged. -/
noncomputable def exactPairs (ctx : Context member initialized h) (tape : IdealKey.Tape) :
    Pairs LogicalKey :=
  runPairs ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule (IdealHierarchy.words tape)

end RebuildBound.Spec.NativeMatchLocalApi

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online NativeMatch NativeMatch.Lanes
open NativeNormalizePairs NativeMatchApi NativeMatchProduction NativeMatchLocalApi

/-- Arbitrary adaptive choices still leave the canonical pair inventory a
finite-read function of the independent logical-routing tape. -/
def NativeMatchLocalApiFiniteRead_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), IdealKey.FiniteRead (exactPairs ctx)

/-- Every decision-prefix step agrees, including adaptive requests, selected
records and requester updates. The exact-pair coverage package is an explicit
dependency, not an additional execution-agreement premise. -/
def NativeMatchLocalApiFrame_statement : Prop :=
  NativeMatchExactPairsRun_statement →
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ (policy : Policy) (stored : LogicalKey → Stored) tape,
    ¬ctx.capacityBad tape →
    NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true →
    ¬PairBad stored (exactPairs ctx tape) → (∀ e ∈ ctx.inventory tape, ¬e.bad stored) →
    ∀ j frame, ctx.frames[j]? = some frame →
    issueFrame policy stored ctx.codec ctx.geo.cfg ctx.geo.shapes ctx.unit ctx.schedule ctx.init
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) ctx.compiled
      (referenceState ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (reference ctx tape).requests
        j ctx.transcriptWidth) frame =
      .ok (referenceState ctx.geo.cfg ctx.geo.shapes ctx.unit (ctx.run tape) ctx.schedule
        (IdealHierarchy.words tape) (IdealHierarchy.dummy tape) (reference ctx tape).requests
        (j + 1) ctx.transcriptWidth)

/-- The former global used-key collision premise is replaced by exact local
pair coverage. This endpoint still uses canonical logical routing words. -/
def NativeMatchLocalApiProjection_statement : Prop :=
  NativeMatchExactPairsRun_statement →
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool) h
    (ctx : Context member initialized h), member ∈ ConfigurationFamily.members → ctx.Valid →
    ∀ (policy : Policy) (stored : LogicalKey → Stored) tape,
    ¬ctx.capacityBad tape →
    NativeMatchPhysical.ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses = true →
    ¬PairBad stored (exactPairs ctx tape) → (∀ e ∈ ctx.inventory tape, ¬e.bad stored) →
    production ctx policy stored tape = .ok (reference ctx tape)

end RebuildBound.Spec
