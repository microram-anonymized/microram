import RebuildBound.Spec.IdealBounded
import RebuildBound.Proofs.ApiBounded
import RebuildBound.Proofs.IdealCapacity

/-! The deterministic adapter transfer charges exactly the canonical reference
failure event. Independent seeds preserve the same unconditional containment. -/
namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online IdealHierarchy IdealDirect MeasureTheory
open HierarchyInvariantProof ConfigurationFamilyProbabilityProof

theorem IdealApiBounded : IdealApiBounded_statement := by
  intro initialized member hm h hh geo c g S init m width batches fs choose n compiled
    hinit hg hE hhor hS hcap a runs requests actual hagree
  have hgeo := structural initialized member hm h
  have G := TopFacts.of_compatible hgeo.2
  have hLen : init.length ≤ geo.init.C / 2 * geo.init.T := by
    rw [G.initC, G.topC, G.initT]
    exact hinit.2.1.trans G.capacity
  have ht := ApiBoundedTransfer geo hgeo c g S init m width batches choose
    hinit.2.2.2 hinit.1 hLen hg hE hhor hS IdealKey.tapeLaw words dummy
    runs requests actual hagree
  exact ⟨ht.1, ht.2.trans (IdealCapacity initialized member hm h hh c g S init m width
    batches choose hinit hg hE hhor hS hcap)⟩

theorem IdealSeedBounded : IdealSeedBounded_statement := by
  intro Seed _ _ _ μ _ initialized member hm h hh geo c g S init m width batches fs n
    choose hinit hg hE hhor hS hcap runs requests actual hagree bad
  have hgeo := structural initialized member hm h
  have G := TopFacts.of_compatible hgeo.2
  have hLen (seed : Seed) : (init seed).length ≤ geo.init.C / 2 * geo.init.T := by
    rw [G.initC, G.topC, G.initT]
    exact (hinit seed).2.1.trans G.capacity
  have hpoint (p : Seed × IdealKey.Tape) (hp : p ∉ bad) :
      ApiResultsCorrect geo c g (runs p) S n (words p.2) (dummy p.2)
        (requests p) (actual p) := by
    exact (ApiBoundedTransfer geo hgeo c g S (init p.1) m width batches (choose p.1)
      (hinit p.1).2.2.2 (hinit p.1).1 (hLen p.1) hg hE hhor hS IdealKey.tapeLaw
      words dummy (fun tape => runs (p.1, tape)) (fun tape => requests (p.1, tape))
      (fun tape => actual (p.1, tape)) (fun tape => hagree (p.1, tape))).1 p.2 hp
  refine ⟨hpoint, le_trans (measure_mono (t := bad) ?_) ?_⟩
  · intro p hbad
    by_contra hp
    exact hbad (hpoint p hp)
  · exact IdealSeedCapacity Seed μ initialized member hm h hh c g S init m width batches
      choose hinit hg hE hhor hS hcap

end RebuildBound
