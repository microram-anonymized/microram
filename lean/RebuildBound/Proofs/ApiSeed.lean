import RebuildBound.Spec.ApiSeed
import RebuildBound.Proofs.ApiLegal
import RebuildBound.Proofs.IdealMeasurable
import RebuildBound.Proofs.IdealSeed
import RebuildBound.Proofs.IdealFailure

/-! The seeded interface specializes the existing legal request client; it
introduces no alternate execution or decision points. Tape measurability comes
from finite local dependence of the actual adaptive interaction. -/
namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online MeasureTheory

theorem ApiSeedMeasurable : ApiSeedMeasurable_statement := by
  intro Seed _ _ _ c cfg sh g S init m width batches choose
  apply IdealSeedMeasurable
  intro seed
  exact IdealAdaptiveMeasurable cfg sh g S m
    (ApiSeed.run c cfg sh g S init m width batches choose seed) _

theorem ApiSeedLive : ApiSeedLive_statement := by
  intro Seed geo hgeo c g S init m width batches
  dsimp only
  intro choose hinit hg hE hhor hS hcap seed tape
  exact ApiLegalLive geo hgeo c g S (init seed) m width batches (choose seed)
    (hinit seed) hg hE hhor hS (hcap seed)
    (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)

theorem ApiSeedEventBound : ApiSeedEventBound_statement := by
  intro Seed _ _ _ μ _ c cfg sh g S init m width batches choose
  dsimp only
  intro event hevent bound hbound
  apply IdealSeedBound Seed μ _
    ((measurable_fst.prodMk (ApiSeedMeasurable Seed c cfg sh g S init m width batches choose)) hevent)
    bound
  exact hbound

theorem ApiSeedExact : ApiSeedExact_statement := by
  intro Seed _ _ _ μ _ c cfg sh g S init m width batches choose
  dsimp only
  intro simulator hsim hslice
  let := hsim
  exact IdealSeedExact Seed μ _ simulator _
    (ApiSeedMeasurable Seed c cfg sh g S init m width batches choose) hslice

theorem ApiSeedFailure : ApiSeedFailure_statement := by
  intro Seed _ _ _ μ _ c cfg sh g S init m width batches choose
  dsimp only
  let bad := ApiSeed.failure c cfg sh g S init m width batches choose
  have hsections (seed : Seed) : MeasurableSet (Prod.mk seed ⁻¹' bad) :=
    IdealAdaptiveFailureMeasurable cfg sh g S m
      (ApiSeed.run c cfg sh g S init m width batches choose seed)
  have hbad : MeasurableSet bad := by
    have he : bad = ⋃ seed, ({seed} ×ˢ (Prod.mk seed ⁻¹' bad)) := by
      ext p
      simp
    rw [he]
    exact MeasurableSet.iUnion fun seed => (measurableSet_singleton seed).prod (hsections seed)
  exact ⟨hbad, fun bound hbound => IdealSeedProof.constant_bound μ bad hbad bound hbound⟩

end RebuildBound
