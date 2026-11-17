import RebuildBound.Spec.ConfigurationFamilyDirect
import RebuildBound.Proofs.ConfigurationFamilyProbability.Facts
import RebuildBound.Proofs.AdaptiveLevelOneBU.Geometry
import RebuildBound.Proofs.DirectJobCycleGeometry.Chain

/-! Finite direct-job applicability, shared by every source-law adapter. -/
namespace RebuildBound.ConfigurationFamilyDirectProof
open Model Model.DirectJob Spec Spec.ConfigurationFamily

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- All consumed scalar equalities and range-specific applicability checks. -/
def DirectFacts (m : Member) (d : Nat) : Prop :=
  let g := m.direct d
  let s := m.directSep d
  g.Valid ∧ g.digit = d ∧ g.K ≤ 64 ∧ g.U = 2 * m.r0 ∧
    g.bCapacity < 256 ∧ g.outputCapacity < 256 ∧
    (2 ≤ d →
      ReferenceInputCompatible (m.direct (d - 1)) s ∧ s.Valid ∧ s.d = d ∧
      s.U = 2 * m.r0 ∧ s.k < 64 ∧ s.K + val2 (s.d - 1) ≤ 64 ∧
      0 < (s.d - 1) / 2 ^ val2 (s.d - 1) ∧ s.C = 64 ∧
      s.stashPages * s.C < 256 ∧ g.outputHomes = s.N ∧
      s.K = g.K ∧ s.e = val2 g.digit ∧ s.r = g.digit / 2 ^ val2 g.digit ∧
      g.routeCapacity = s.stashPages * s.C ∧ g.radixCapacity = s.stashPages * s.C ∧
      (g.ranges ≠ .direct → g.aTierCapacity = s.aTierPages * s.C ∧
        g.ranges = .dfs s.I s.rangeBits (s.poolPages * s.C) ∧ s.I < s.K))

instance (m : Member) (d : Nat) : Decidable (DirectFacts m d) := by
  unfold DirectFacts
  infer_instance

theorem finiteFacts : ∀ m ∈ members,
    ∀ d ∈ List.range' 1 ((m.config true).fanout 1), DirectFacts m d := by decide +kernel

theorem facts (m : Member) (hm : m ∈ members) (d : Nat)
    (hd : 1 ≤ d) (hdn : d ≤ (m.config true).fanout 1) : DirectFacts m d := by
  apply finiteFacts m hm d
  apply List.mem_range'.2
  refine ⟨d - 1, ?_, by omega⟩
  omega

theorem finiteLinks : ∀ m ∈ members,
    ∀ d ∈ List.range' 1 ((m.config true).fanout 1 - 1),
      (m.direct (d + 1)).K = (m.direct d).K ∧
      (m.direct (d + 1)).digit = (m.direct d).digit + 1 ∧
      (m.direct d).outputCapacity ≤ (m.direct (d + 1)).aTierCapacity := by decide +kernel

theorem cycleGeometry (m : Member) (hm : m ∈ members) :
    DirectCycleGeometry m.direct ((m.config true).fanout 1) := by
  refine ⟨fun hn => (facts m hm 1 le_rfl hn).2.1, fun d hd hdn => (facts m hm d hd hdn).1, ?_⟩
  intro d hd hdn
  exact finiteLinks m hm d (List.mem_range'.2 ⟨d - 1, by omega, by omega⟩)

theorem causalGeometry (initialized : Bool) (m : Member) (hm : m ∈ members) (h : Nat) :
    AdaptiveLevelOneBUProof.CausalGeometryFacts ((m.geometry initialized).chunk h) := by
  have hs := HierarchySemanticsProof.lower (ConfigurationFamilyStructural initialized m hm).1
  have hc := ConfigurationFamilyProbabilityProof.coveringFacts initialized m hm
  exact { levels := hs.levels2
          time := HierarchyLocalityChunksProof.timeFacts_chunk
            { seed := hs.seed
              prod := fun ℓ h1 hL => hc.per_succ ℓ hL h1
              pos := fun ℓ _ hL => hc.per_pos ℓ (by omega) } h
          steps := ConfigurationFamilyProbabilityProof.stepFacts initialized m hm h
          invariant := ConfigurationFamilyProbabilityProof.invariant initialized m hm h
          locality := ConfigurationFamilyProbabilityProof.locality initialized m hm h }

end RebuildBound.ConfigurationFamilyDirectProof
