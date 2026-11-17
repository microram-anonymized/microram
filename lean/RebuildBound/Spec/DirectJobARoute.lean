import RebuildBound.Spec.DirectJobABounds

/-! Route-only probability adapters. Direct A distribution has no range check,
even when the completed A pool is nonempty. Its native range fields need not
satisfy the DFS probability adapter's `I < K` premise. -/

open scoped ENNReal NNReal

namespace RebuildBound.Model.DirectJob

/-- Only the topology and storage capacities consumed by A preparation.
Distribution and tier fields are deliberately absent. -/
structure ARouteProbabilityGeometry (g : Geometry) (s : SepGeom) : Prop where
  C : s.C = 64
  K : s.K = g.K
  e : s.e = val2 g.digit
  r : s.r = g.digit / 2 ^ val2 g.digit
  route : g.routeCapacity = s.stashPages * s.C
  radix : g.radixCapacity = s.stashPages * s.C

end RebuildBound.Model.DirectJob

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- Unconditional route-witness containment, independent of the range plan. -/
def DirectJobARouteWitnessBound_statement : Prop :=
  ∀ (g : Geometry) (s : SepGeom), g.Valid → 2 ≤ g.digit →
    ARouteProbabilityGeometry g s → s.Valid →
    ∀ (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (sinp : SInputs),
    sinp.aMain = inp.aMain → SInputShape s oldWord word sinp →
    aRouteWitness g word inp → sharedARouteWitness s oldWord word sinp

/-- Storage terms alone bound the route witness, without a successful-tier or
successful-range condition. The full finite-word radix density is retained. -/
def DirectJobARouteWitnessProbability_statement : Prop :=
  ∀ (g : Geometry) (s : SepGeom), g.Valid → 2 ≤ g.digit →
    ARouteProbabilityGeometry g s → s.Valid →
    ∀ (L : SJobLaw s) (lam D : ℝ≥0) (cutoff : Nat),
    SInputLaw L lam D → 0 < lam → (lam : ℝ) ≤ s.C →
    s.stashPages * s.C < cutoff →
    ∀ direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs,
    (∀ hist hw, (direct hist (L.wordFn hw)).aMain = (L.inputs hist (L.wordFn hw)).aMain) →
    L.prob (fun hist word => aRouteWitness g word (direct hist word)) ≤
      s.k * ENNReal.ofReal (witness s.N s.C lam (s.stashPages * s.C) cutoff D) +
      (if 1 < s.r then ENNReal.ofReal
        (witness s.N s.C lam (s.stashPages * s.C) cutoff (s.curDensity L.W L.KA.card)) else 0)

/-- A direct distributor adds no range event. This includes the family's
eight-home, digit-two job with a nonempty A tier and pool. -/
def DirectJobADirectWitnessProbability_statement : Prop :=
  ∀ (g : Geometry) (s : SepGeom), g.Valid → 2 ≤ g.digit →
    ARouteProbabilityGeometry g s → s.Valid → g.ranges = .direct →
    ∀ (L : SJobLaw s) (lam D : ℝ≥0) (cutoff : Nat),
    SInputLaw L lam D → 0 < lam → (lam : ℝ) ≤ s.C →
    s.stashPages * s.C < cutoff →
    ∀ direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs,
    (∀ hist hw, (direct hist (L.wordFn hw)).aMain = (L.inputs hist (L.wordFn hw)).aMain) →
    L.prob (fun hist word =>
      aRouteWitness g word (direct hist word) ∨ aRangeWitness g word (direct hist word)) ≤
      s.k * ENNReal.ofReal (witness s.N s.C lam (s.stashPages * s.C) cutoff D) +
      (if 1 < s.r then ENNReal.ofReal
        (witness s.N s.C lam (s.stashPages * s.C) cutoff (s.curDensity L.W L.KA.card)) else 0)

end RebuildBound.Spec
