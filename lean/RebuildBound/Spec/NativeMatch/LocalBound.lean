import RebuildBound.Spec.NativeMatch.LocalApi
import RebuildBound.Spec.NativeMatch.ExactCounts
import RebuildBound.Spec.NativeRouting.LocalPairs
import RebuildBound.Spec.NativeMatch.Coded

/-! One canonical normalization inventory and one shared error allowance.
The ring guard is a function of the independent reference tape. The probability
law is unconditional. These results prepare complete-message transfer; the
agreement statement here still uses canonical logical routing. -/
namespace RebuildBound.Spec.NativeMatchLocalBound
open Model NativeMatchProduction NativeMatchLocalApi NativeRoutingLocalPairs
open NativeNormalizePairs NativeMatchPhysical NativeNormalize
open scoped ENNReal

variable {member : ConfigurationFamily.Member} {initialized : Bool} {h : Nat}

noncomputable def normalizationPairs (ctx : Context member initialized h)
    (tape : IdealKey.Tape) : Pairs LogicalKey :=
  if ready ctx.unit (ctx.run tape) ctx.snapshots ctx.accesses then
    exactPairs ctx tape ++ routingPairs ctx tape else []

def coefficientA (member : ConfigurationFamily.Member) (initialized : Bool) : Nat :=
  routeA member initialized

def coefficientB (member : ConfigurationFamily.Member) (initialized : Bool) : Nat :=
  NativeMatchExactCounts.perAccess member + routeB member initialized

noncomputable def normalizeCost (ctx : Context member initialized h) : ℝ≥0∞ :=
  pairBound 128 (coefficientA member initialized + ctx.accesses * coefficientB member initialized)

noncomputable def error (ctx : Context member initialized h) : ℝ≥0∞ :=
  (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^64) + normalizeCost ctx + NativeMatchCoded.ringCost ctx

/-- Capacity and VP2 keep their existing combined allocation. Normalization
appears once, for exact comparisons and routing together. -/
noncomputable def bad (ctx : Context member initialized h)
    (p : IdealKey.Tape × Tape 128) : Prop :=
  (ctx.capacityBad p.1 ∨ ∃ e ∈ ctx.inventory p.1, e.bad p.2) ∨
    PairBad p.2 (normalizationPairs ctx p.1) ∨
    ready ctx.unit (ctx.run p.1) ctx.snapshots ctx.accesses = false

end RebuildBound.Spec.NativeMatchLocalBound

namespace RebuildBound.Spec
open Model NativeMatchProduction NativeMatchLocalBound NativeNormalizePairs
open NativeMatchApi NativeNormalize MeasureTheory

def NativeMatchLocalBoundFiniteRead_statement : Prop :=
  ∀ member initialized h (ctx : Context member initialized h),
    IdealKey.FiniteRead (normalizationPairs ctx)

/-- The count uses actual charged accesses, not the certificate horizon. -/
def NativeMatchLocalBoundLinear_statement : Prop :=
  ∀ member initialized h (ctx : Context member initialized h),
    member ∈ ConfigurationFamily.members → ctx.Valid → ∀ tape,
    (normalizationPairs ctx tape).length ≤
      coefficientA member initialized + ctx.accesses * coefficientB member initialized

def NativeMatchLocalBoundNormalize_statement : Prop :=
  ∀ member initialized h (ctx : Context member initialized h),
    member ∈ ConfigurationFamily.members → ctx.Valid →
    (IdealKey.tapeLaw.prod (tapeLaw 128))
      {p | PairBad p.2 (normalizationPairs ctx p.1)} ≤ normalizeCost ctx

/-- A single unconditional error budget for subsequent guarded transfer. -/
def NativeMatchLocalBoundError_statement : Prop :=
  ∀ member initialized, member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
    ∀ (ctx : Context member initialized h), ctx.Valid →
    (IdealKey.tapeLaw.prod (tapeLaw 128)) {p | bad ctx p} ≤ min 1 (error ctx)

/-- Off that shared event the existing logical-routing API agrees. This does
not assert a complete-message marginal or native API coupling. -/
def NativeMatchLocalBoundProjection_statement : Prop :=
  ∀ member initialized h (ctx : Context member initialized h),
    member ∈ ConfigurationFamily.members → ctx.Valid → ∀ policy tape stored,
    ¬bad ctx (tape, stored) →
    production ctx policy stored tape = .ok (reference ctx tape)

end RebuildBound.Spec
