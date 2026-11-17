import RebuildBound.Spec.ConfigurationFamily
import RebuildBound.Spec.AdaptiveStepsJobs
import RebuildBound.Spec.DirectJobARoute
import RebuildBound.Spec.DirectJobHistoryGeometry

/-! Exact direct-job probability shapes and shared analytic budgets for the
finite family. Direct A routing has no range term; all finite-word density
factors remain explicit. Numerical certificates are separate. -/

open MeasureTheory
open scoped ENNReal NNReal
namespace RebuildBound.Spec
open Model Model.DirectJob
namespace ConfigurationFamily

/-- The probability input uses the actual topology, range plan and pages,
with the shared unrestricted one-page B reference tier. -/
def Member.directSep (m : Member) (d : Nat) : SepGeom :=
  let g := m.direct d
  let rangeBits := match g.ranges with | .direct => 0 | .dfs _ bits _ => bits
  let indexBits := match g.ranges with | .direct => ceilLog2 g.outputHomes | .dfs lo _ _ => lo
  ⟨64, g.K, val2 d, d / 2 ^ val2 d, rangeBits, indexBits,
    m.stashPages 1, m.tierPages 1, 1, m.tierPages 1⟩

/-- Conservative shared A budget. The direct path never consumes a range
certificate. Both branches reuse the existing separated arithmetic registry. -/
noncomputable def directABound (m : Member) (d : Nat) : ℝ≥0∞ :=
  if (m.direct d).ranges = .direct then selRest (m.directSep d)
  else selSepBound (m.directSep d)

noncomputable def directBBound (m : Member) (d : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal (Phi 256 (m.direct d).U 64 32 (m.direct d).bCapacity)

noncomputable def directUBound (m : Member) (d : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal ((m.directSep d).curDensity 64 (32 * (m.directSep d).N) *
    Phi 256 (m.direct d).outputHomes 64 32 (m.direct d).outputCapacity)

noncomputable def directBound (m : Member) (d : Nat) : ℝ≥0∞ :=
  if d = 1 then directBBound m d else directBBound m d + directABound m d + directUBound m d

end ConfigurationFamily

/-- The same unconditional A-history estimate serves fixed cycles and causal
cells. Source-law applicability is derived from the finite family geometry. -/
def ConfigurationFamilyDirectA_statement : Prop :=
  ∀ m ∈ ConfigurationFamily.members, ∀ d,
    2 ≤ d → d ≤ (m.config true).fanout 1 →
    ∀ data : DirectHistoryData, data.ValidFor (m.directSep d) 32 →
      (data.lawFor (m.direct (d - 1)) (m.directSep d)).prob (fun hist word =>
        levelOneA (m.direct d) word (data.directFor (m.direct (d - 1)) hist word)) ≤
      ConfigurationFamily.directABound m d

/-- Direct first-failure probabilities at every horizon use the actual
source width and shapes, from either start, for arbitrary causal clients. -/
def ConfigurationFamilyDirect_statement : Prop :=
  ∀ (initialized : Bool) m, m ∈ ConfigurationFamily.members → ∀ h : Nat,
    let geo := (m.geometry initialized).chunk h
    CausalBound geo fun μ tr words => ∀ o,
      JobId.ordinary 1 o ∈ geo.cfg.potentialJobs →
      μ {ω | JobFailsFirst geo.cfg geo.shapes (tr ω) (words ω) (.ordinary 1 o)} ≤
        ConfigurationFamily.directBound m (geo.cfg.digitAt 1 o)

end RebuildBound.Spec
