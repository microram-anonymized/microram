import RebuildBound.Proofs.ConfigurationFamily
import RebuildBound.Proofs.HierarchySemantics.Structure
import RebuildBound.Proofs.HierarchyLawsChunks31
import RebuildBound.Proofs.HierarchyFirstFailure

/-! Check each finite applicability fact once; horizon transport is symbolic. -/
namespace RebuildBound.ConfigurationFamilyProbabilityProof
open Model Model.Hierarchy Spec Spec.ConfigurationFamily

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem coveringFacts (initialized : Bool) : ∀ m ∈ members,
    let g := m.geometry initialized
    HierarchyCoveringProof.FactsFor g.cfg g.rows g.top g.prep g.init g.direct := by
  cases initialized <;>
    simp only [members, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true] <;>
    repeat' apply And.intro
  all_goals constructor <;> decide +kernel

theorem chunkFacts (initialized : Bool) : ∀ m ∈ members,
    HierarchyChunkArith.ChunkFacts (m.geometry initialized).cfg := by
  cases initialized <;>
    simp only [members, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true] <;>
    repeat' apply And.intro
  all_goals constructor <;> decide +kernel

/-- Arithmetic required by the existing local probability adapters. -/
def Arithmetic (geo : HierarchyGeometry) : Prop :=
  geo.cfg.Valid ∧ HierarchySepLawProof.Good geo.cfg ∧ geo.cfg.RowsMatch geo.rows ∧
    (∀ q ∈ geo.rows, q.1.k < 64 ∧ q.1.K + val2 (q.1.d - 1) ≤ 64 ∧
      0 < (q.1.d - 1) / 2 ^ val2 (q.1.d - 1) ∧ q.1.Valid ∧
      q.1.I < q.1.K ∧ q.1.C = 64 ∧ q.1.stashPages * q.1.C < 256) ∧
    geo.top.k + geo.top.e ≤ 64 ∧ geo.prep.k ≤ 64 ∧ geo.init.k ≤ 64

theorem arithmetic (initialized : Bool) : ∀ m ∈ members,
    Arithmetic (m.geometry initialized) := by
  cases initialized <;> unfold Arithmetic HierarchySepLawProof.Good Config.Valid <;> decide +kernel

theorem invariant (initialized : Bool) (m : Member) (hm : m ∈ members) (h : Nat) :
    HierarchyInvariantFor ((m.geometry initialized).chunk h) := by
  intro N tr hN hT hU words
  have hs := ConfigurationFamilyStructural initialized m hm
  exact HierarchyInvariantProof.contractsFor ((m.geometry initialized).chunk h)
    (HierarchyLawsChunks31Proof.lowFacts_horizon (HierarchySemanticsProof.lower hs.1) (h * 2 ^ 32))
    (HierarchyLawsChunks31Proof.topFacts_chunk
      (HierarchyInvariantProof.TopFacts.of_compatible hs.2) h) hN hT hU words

/-- Geometry does not change when only the execution horizon is extended. -/
theorem structural (initialized : Bool) (m : Member) (hm : m ∈ members) (h : Nat) :
    ((m.geometry initialized).chunk h).Structural := by
  have hs := ConfigurationFamilyStructural initialized m hm
  refine ⟨(HierarchySemanticsProof.lower_iff _).2
    (HierarchyLawsChunks31Proof.lowFacts_horizon (HierarchySemanticsProof.lower hs.1) _), ?_⟩
  have he := (HierarchyHorizonFree (m.geometry initialized).cfg
    (h * 2 ^ 32) (m.geometry initialized).rows).2.1
  have hi : ((m.geometry initialized).chunk h).incomingTopCapacity =
      (m.geometry initialized).incomingTopCapacity := by
    unfold HierarchyGeometry.incomingTopCapacity
    change (if (m.geometry initialized).cfg.levels = 2 then
      some ((m.geometry initialized).direct ((m.geometry initialized).cfg.fanout 1)).outputCapacity
      else (((m.geometry initialized).chunk h).cfg.sepRow (m.geometry initialized).rows
        ((m.geometry initialized).cfg.levels - 1)
        ((m.geometry initialized).cfg.fanout ((m.geometry initialized).cfg.levels - 1))).map
          (fun row => row.tierPages * row.C)) = _
    dsimp only [HierarchyGeometry.chunk, chunkConfig]
    rw [he]
  rw [HierarchyGeometry.TopCompatible, hi]
  exact hs.2

theorem timeFacts (initialized : Bool) (m : Member) (hm : m ∈ members) (h : Nat) :
    HierarchyLocalityProof.TimeFacts ((m.geometry initialized).chunk h).cfg := by
  have hs := HierarchySemanticsProof.lower (ConfigurationFamilyStructural initialized m hm).1
  have hc := coveringFacts initialized m hm
  exact HierarchyLocalityChunksProof.timeFacts_chunk
    { seed := hs.seed
      prod := fun ℓ h1 hL => hc.per_succ ℓ hL h1
      pos := fun ℓ _ hL => hc.per_pos ℓ (by omega) } h

theorem locality (initialized : Bool) (m : Member) (hm : m ∈ members) (h : Nat) :
    let geo := (m.geometry initialized).chunk h
    HierarchyLocalityFor geo.cfg geo.shapes :=
  HierarchyLocalityProof.localityFor _ _ (timeFacts initialized m hm h)

theorem stepFacts (initialized : Bool) (m : Member) (hm : m ∈ members) (h : Nat) :
    HierarchyLevelOneProof.StepFacts ((m.geometry initialized).chunk h).cfg := by
  have hs := HierarchySemanticsProof.lower (ConfigurationFamilyStructural initialized m hm).1
  exact HierarchyLawsChunks31Proof.stepFacts_chunk (chunkFacts initialized m hm)
    (fun ℓ h1 hL => by have := (hs.fan ℓ h1 hL).1; omega) h

theorem rowOK (initialized : Bool) (m : Member) (hm : m ∈ members) :
    ∀ q ∈ (m.geometry initialized).rows, HierarchySepLawProof.RowOK q.1 := by
  intro q hq
  obtain ⟨hk, hK, ho, _⟩ := (arithmetic initialized m hm).2.2.2.1 q hq
  exact HierarchySepLawProof.rowOK_of_width hk hK ho

end RebuildBound.ConfigurationFamilyProbabilityProof
