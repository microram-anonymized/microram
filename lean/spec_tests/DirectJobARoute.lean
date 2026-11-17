import RebuildBound.Proofs.DirectJobABounds
import spec_tests.ConfigurationFamilyData

/-! The native eight-home direct A pool is nonempty. Its range fields do not
meet the DFS probability premise; the route-only adapter must cover it. -/

namespace DirectJobARouteTest
open RebuildBound RebuildBound.Model RebuildBound.Model.DirectJob RebuildBound.Spec
open scoped ENNReal NNReal

def direct : Geometry := ⟨2, 2, 8, 64, 64, 64, 64, 64, 64, .direct⟩
def sep : SepGeom := ⟨64, 2, 1, 1, 0, 3, 1, 1, 1, 1⟩

theorem geometry : direct.Valid ∧ sep.Valid ∧ 0 < direct.aTierCapacity ∧
    0 < direct.poolCapacity ∧ ¬ sep.I < sep.K := by decide

theorem adapter : ARouteProbabilityGeometry direct sep := by constructor <;> decide

example : ¬ AProbabilityGeometry direct sep := by
  intro h
  cases h.ranges

/-- All nonempty direct A pools in the finite family have this exact shape. -/
example : ∀ m ∈ ConfigurationFamilyTest.members, ∀ d ∈ List.range' 1 (m.config true).fanouts.head!,
    (m.direct d).ranges = .direct → 0 < (m.direct d).poolCapacity → m.direct d = direct := by
  decide +kernel

example : (ConfigurationFamilyTest.members.filter fun m => m.direct 2 = direct).length = 33 := by
  decide +kernel

/-- These contracts reject mismatched topology and either storage capacity. -/
example : ¬ ARouteProbabilityGeometry { direct with K := 3 } sep := by
  intro h
  have := h.K
  contradiction

example : ¬ ARouteProbabilityGeometry { direct with routeCapacity := 128 } sep := by
  intro h
  have := h.route
  contradiction

example : ¬ ARouteProbabilityGeometry { direct with radixCapacity := 128 } sep := by
  intro h
  have := h.radix
  contradiction

example : ¬ ARouteProbabilityGeometry direct { sep with r := 3 } := by
  intro h
  have := h.r
  contradiction

/-- Absence of distributor checks holds for arbitrary inputs, including tiers
that overflow their advertised capacity. Route storage is still accounted for. -/
example (word : LogicalKey → Nat) (inp : DirectJob.Inputs) :
    (aRouteWitness direct word inp ∨ aRangeWitness direct word inp) ↔
      aRouteWitness direct word inp := by
  simp [DirectJobABoundsProof.no_direct_range direct rfl]

theorem probability (L : SJobLaw sep) (lam D : ℝ≥0) (cutoff : Nat)
    (hL : SInputLaw L lam D) (hlam : 0 < lam) (hC : (lam : ℝ) ≤ sep.C)
    (hcut : sep.stashPages * sep.C < cutoff)
    (inputs : L.Hist → (LogicalKey → Nat) → DirectJob.Inputs)
    (hmain : ∀ hist hw, (inputs hist (L.wordFn hw)).aMain = (L.inputs hist (L.wordFn hw)).aMain) :
    L.prob (fun hist word =>
      aRouteWitness direct word (inputs hist word) ∨ aRangeWitness direct word (inputs hist word)) ≤
      3 * ENNReal.ofReal (witness 8 64 lam 64 cutoff D) := by
  simpa [sep, SepGeom.k, SepGeom.N] using
    DirectJobADirectWitnessProbability direct sep geometry.1 (by decide) adapter
      geometry.2.1 rfl L lam D cutoff hL hlam hC hcut inputs hmain

end DirectJobARouteTest
