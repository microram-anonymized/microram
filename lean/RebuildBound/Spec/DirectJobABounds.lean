import RebuildBound.Spec.DirectJobA
import RebuildBound.Spec.DirectJobFailure
import RebuildBound.Spec.SepBound

/-! Narrow adapters for selected page-aligned A geometries. The topology,
capacities, range plan and input law are explicit. In particular, a DFS failure
is compared to the truncated completed-A witness only after preparation passes. -/
open scoped ENNReal NNReal

namespace RebuildBound.Model.DirectJob

/-- A probability geometry for a selected direct reference job. This does not certify
arbitrary boundary-test geometries or unequal stage/radix capacities. -/
structure AProbabilityGeometry (g : Geometry) (s : SepGeom) : Prop where
  C : s.C = 64
  K : s.K = g.K
  e : s.e = val2 g.digit
  r : s.r = g.digit / 2 ^ val2 g.digit
  route : g.routeCapacity = s.stashPages * s.C
  radix : g.radixCapacity = s.stashPages * s.C
  tier : g.aTierCapacity = s.aTierPages * s.C
  ranges : g.ranges = .dfs s.I s.rangeBits (s.poolPages * s.C)

/-- B-independent A witnesses, defined on every word assignment. -/
def sharedARouteWitness (s : SepGeom) (oldWord word : LogicalKey → Nat) (inp : SInputs) : Prop :=
  (∃ j < s.k, s.stashPages * s.C < sRawStageExcess s oldWord word inp j) ∨
  (1 < s.r ∧ s.stashPages * s.C < sAHomeExcess s word inp)

def sharedARangeWitness (s : SepGeom) (word : LogicalKey → Nat) (inp : SInputs) : Prop :=
  ∃ v < s.ranges, s.C < sRefCoarse s word
    (sReferenceWith engineRule s word inp s.canonicalOps) inp s.earlyCap v

end RebuildBound.Model.DirectJob

namespace RebuildBound.Spec
open Model Model.DirectJob

def DirectJobARouteBound_statement : Prop :=
  ∀ (g : Geometry) (s : SepGeom), g.Valid → 2 ≤ g.digit →
    AProbabilityGeometry g s → s.Valid →
    ∀ (oldWord word : LogicalKey → Nat) (inp : SInputs), SInputShape s oldWord word inp →
    ∀ e, prepareA g word inp.aMain = .error e → sharedARouteWitness s oldWord word inp

def DirectJobARangeBound_statement : Prop :=
  ∀ (g : Geometry) (s : SepGeom), g.Valid → 2 ≤ g.digit →
    AProbabilityGeometry g s → s.Valid →
    ∀ (oldWord word : LogicalKey → Nat) (inp : SInputs), SInputShape s oldWord word inp →
    STiersFit s inp → ∀ st, prepareA g word inp.aMain = .ok st →
    ∀ e, distributeABounded g word (aOperational st inp.aTier inp.bTier.flatten) = .error e →
      sharedARangeWitness s word inp

/-- Adapt the existing unconditional direct A inventory as a disjunction.
A completed residual overflow may have arisen after route overflow; in that
case the route witness accounts for it before invoking the truncated range bound. -/
def DirectJobAWitnessBound_statement : Prop :=
  ∀ (g : Geometry) (s : SepGeom), g.Valid → 2 ≤ g.digit →
    AProbabilityGeometry g s → s.Valid →
    ∀ (oldWord word : LogicalKey → Nat) (inp : DirectJob.Inputs) (sinp : SInputs),
    sinp.aMain = inp.aMain → sinp.aTier = inp.aTier → SInputShape s oldWord word sinp →
    STiersFit s sinp → (aRouteWitness g word inp ∨ aRangeWitness g word inp) →
      sharedARouteWitness s oldWord word sinp ∨ sharedARangeWitness s word sinp

/-- Existing unconditional direct A witnesses, with the direct reference history/input
adapter supplied on the support of the shared finite law. Storage terms reuse
the existing minimum of subset and positive-series bounds; ranges reuse SG2. -/
def DirectJobAWitnessProbability_statement : Prop :=
  ∀ (g : Geometry) (s : SepGeom), g.Valid → 2 ≤ g.digit →
    AProbabilityGeometry g s → s.Valid →
    ∀ (L : SJobLaw s) (lam D : ℝ≥0) (cutoff : Nat),
    SInputLaw L lam D → 0 < lam → (lam : ℝ) ≤ s.C → s.I < s.K →
    s.stashPages * s.C < cutoff →
    ∀ direct : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs,
    (∀ hist hw, (direct hist (L.wordFn hw)).aMain = (L.inputs hist (L.wordFn hw)).aMain ∧
      (direct hist (L.wordFn hw)).aTier = (L.inputs hist (L.wordFn hw)).aTier) →
    L.prob (fun hist word => STiersFit s (L.inputs hist word) ∧
      (aRouteWitness g word (direct hist word) ∨ aRangeWitness g word (direct hist word))) ≤
      s.k * ENNReal.ofReal (witness s.N s.C lam (s.stashPages * s.C) cutoff D) +
      (if 1 < s.r then ENNReal.ofReal
        (witness s.N s.C lam (s.stashPages * s.C) cutoff (s.curDensity L.W L.KA.card)) else 0) +
      (D : ℝ≥0∞) * 2 ^ (s.k - s.I) *
        ∑ a ∈ Finset.range s.r,
          stopLoss (rangeLawR s.C lam s.earlyCap (2 ^ s.I) (s.k - s.I) s.r
            (qMass L.W s.k s.r a)) s.C

end RebuildBound.Spec
