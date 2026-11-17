import RebuildBound.Spec.IdealProbe
import RebuildBound.Proofs.ApiSeed
import RebuildBound.Proofs.ApiStructural
import RebuildBound.Proofs.BatchPattern
import RebuildBound.Proofs.BatchFresh
import RebuildBound.Proofs.BatchExact
import RebuildBound.Proofs.AdaptiveReplay
import RebuildBound.Proofs.IdealHierarchy

/-! Exact probe simulation uses a finite restriction separately for each replay
fibre. The private numeric provenance witness does not bound storage capacity
or the keys of other branches. Pattern and observable-coordinate freshness use
only lower structural facts; no top population or capacity-success premise is
needed. Internal routing reads need not be fresh relative to the transcript. -/
namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online MeasureTheory IdealHierarchy

namespace IdealProbeProof

/-- The compatibility dummy tape agrees on every observed cell. -/
theorem view_dummy (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (n m : Nat) (tape : IdealKey.Tape) :
    OnlineBatch.view cfg sh g run S n m (words tape) (dummyOf (dummyTape n m tape)) =
      OnlineBatch.view cfg sh g run S n m (words tape) (dummy tape) := by
  funext t i
  unfold OnlineBatch.view OnlineBatch.touched
  rw [(IdealHierarchyOnline cfg 0 n m).2 tape t i t.isLt i.isLt]

end IdealProbeProof

/-- Each finite supplied-record run has a finite restriction, with no imposed
bound on the size or numeric encoding of its exact byte keys. -/
theorem IdealBatchExact : IdealBatchExact_statement := by
  intro geo hgeo g run S n m hinit hg hE hhor hn hunsh hS
  refine ⟨IdealViewMeasurable geo.cfg geo.shapes g run S n m, ?_⟩
  obtain ⟨N, hkeys, htrace⟩ := ApiStructuralProof.run_premises geo.cfg g run hg hE hinit
  let compat : HierarchyGeometry := { geo with keyCapacity := N }
  have F : HierarchyInvariantProof.LowFacts compat.cfg compat.rows compat.direct :=
    HierarchySemanticsProof.lower hgeo
  have hs : BatchSettingFor compat N g run S n m :=
    ⟨le_rfl, hn, ⟨⟨hg, hE⟩, hhor, hkeys, htrace, hunsh⟩, hS⟩
  have hX := BatchExactProof.exactFor_of compat (BatchPatternProof.patternFor compat F)
    (BatchFreshProof.freshFor compat F) N g run S n m hs
    IdealKey.tapeLaw (familyTape geo.cfg N) (dummyTape n m) words
    (IdealHierarchyOnline geo.cfg N n m).1
  have he : (fun tape => OnlineBatch.view geo.cfg geo.shapes g run S n m
      (words tape) (dummyOf (dummyTape n m tape))) =
      (fun tape => OnlineBatch.view geo.cfg geo.shapes g run S n m (words tape) (dummy tape)) :=
    funext (IdealProbeProof.view_dummy geo.cfg geo.shapes g run S n m)
  change IdealKey.tapeLaw.map (fun tape => OnlineBatch.view geo.cfg geo.shapes g run S n m
    (words tape) (dummyOf (dummyTape n m tape))) = _ at hX
  rwa [he] at hX

/-- Countable transcript fibres allow a different finite key restriction on
 every branch while all fibres refer to the same canonical experiment. -/
theorem IdealAdaptiveExact : IdealAdaptiveExact_statement := by
  intro geo hgeo g S m a
  dsimp only
  intro hinit hg hE hhor hunsh hS
  let n := Adaptive.slotCount a.shape
  have hm := IdealAdaptiveMeasurable geo.cfg geo.shapes g S m a n
  refine ⟨hm, Measure.ext_of_singleton fun t => ?_⟩
  have hr := ReplayShape m a n t
  have hi : ((Adaptive.replay a t).init.map Rec.key).Nodup := by
    rw [hr.2.2.2.1]
    exact hinit
  obtain ⟨hvm, hmap⟩ := IdealBatchExact geo hgeo g (Adaptive.replay a t) S n m hi hg hE
    (by simpa only [hr.2.2.1] using hhor)
    (by simpa only [hr.2.2.1] using (le_rfl : n ≤ n)) (hunsh t) hS
  have hfib : (fun tape => Adaptive.transcript geo.cfg geo.shapes g S a n
      (words tape) (dummy tape)) ⁻¹' {t} =
      (fun tape => OnlineBatch.view geo.cfg geo.shapes g (Adaptive.replay a t) S n m
        (words tape) (dummy tape)) ⁻¹' {t} := by
    ext tape
    exact (AdaptiveReplayProof.adaptiveReplay (RowCausalityStep TracePrefix TraceUnitsPrefix)
      geo.cfg geo.shapes g S m a n rfl hg hE hS
      (words tape) (dummy tape)).2.2 t
  rw [Measure.map_apply hm (measurableSet_singleton t), hfib,
    ← Measure.map_apply hvm (measurableSet_singleton t), hmap, hr.1, hr.2.1]

/-- Request construction supplies each replay's flag promise; the public
client supplies neither a transcript law nor a population assumption. -/
theorem IdealApiExact : IdealApiExact_statement := by
  intro geo hgeo c g S init m width batches
  dsimp only
  intro choose hInit hinit hLen hg hE hhor hS
  let fs := ApiAdaptive.frames width g.unitEntries batches
  let compiled := ApiLegal.adapt geo.cfg (ApiAdaptive.shape fs) S choose
  let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs compiled
  have hf := ApiAdaptiveFrames width g.unitEntries batches
  apply IdealAdaptiveExact geo hgeo.1 g S m a hinit hg hE hhor
  · intro t
    have he : Adaptive.replay a t = ApiExecution.run c geo.cfg geo.shapes g S init
        (ApiAdaptive.requestGroups compiled
          (Adaptive.rowsOf t (Adaptive.slotCount (ApiAdaptive.shape fs))) fs) :=
      ApiAdaptiveReplay c geo.cfg geo.shapes g S init m fs compiled hf.1 t
    rw [he]
    exact (ApiExecutionStructural geo hgeo c g S init _ m hInit hinit hLen hg hE
      (by simpa only [ApiAdaptiveCorrectnessProof.requests_length] using hhor)
      (hf.2.2 m compiled _).1
      (by simpa only [ApiAdaptiveCorrectnessProof.requests_length] using hS)).2.1
  · exact hS

/-- Exact slice laws mix under independent client coins, including countable
seed distributions with unbounded support and seed-dependent initialization. -/
theorem IdealApiSeedExact : IdealApiSeedExact_statement := by
  intro Seed _ _ _ μ _ geo hgeo c g S init m width batches
  dsimp only
  intro choose hInit hinit hLen hg hE hhor hS
  let observe := ApiSeed.transcript c geo.cfg geo.shapes g S init m width batches choose
  have hm := ApiSeedMeasurable Seed c geo.cfg geo.shapes g S init m width batches choose
  let simulator := simLaw geo.cfg
    (OnlineBatch.slotSchedule
      (Adaptive.shapeWidths (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches))) S)
    (Adaptive.shapePattern (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches)))
    (Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches))) m
  have hslice : ∀ seed, IdealKey.tapeLaw.map (observe seed) = simulator := by
    intro seed
    exact (IdealApiExact geo hgeo c g S (init seed) m width batches (choose seed)
      (hInit seed) (hinit seed) (hLen seed) hg hE hhor hS).2
  have hsim : IsProbabilityMeasure simulator := by
    unfold simulator simLaw
    infer_instance
  exact ⟨hm, ApiSeedExact Seed μ c geo.cfg geo.shapes g S init m width batches choose
    simulator hsim hslice⟩

end RebuildBound
