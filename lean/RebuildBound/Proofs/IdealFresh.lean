import RebuildBound.Spec.IdealFresh
import RebuildBound.Proofs.ApiStructural
import RebuildBound.Proofs.AdaptiveReplay
import RebuildBound.Proofs.AdaptiveRowCausality
import RebuildBound.Proofs.AdaptiveTracePrefix
import RebuildBound.Proofs.HierarchySemantics
import RebuildBound.Proofs.BatchFresh

/-! Proof that two different real probes of a realized adaptive API run never
share a hash family and a key, for arbitrary byte keys. The structural API
theorem supplies request correctness, the adaptive replay supplies the slot
count, and the batch freshness theorem is applied to the run with its own
distinct-key count as the key capacity, so no key universe or capacity premise
enters. -/
namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online

theorem IdealApiFresh : IdealApiFresh_statement := by
  intro geo hgeo c g S init m width batches
  dsimp only
  intro choose hInit hinit hLen hg hE hhor hS words dummy
  have hcorrect := ApiAdaptiveStructural geo hgeo c g S init m width batches choose
    hInit hinit hLen hg hE hhor hS words dummy
  let a := ApiAdaptive.run c geo.cfg geo.shapes g S init
    (ApiAdaptive.frames width g.unitEntries batches) choose
  let n := Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames width g.unitEntries batches))
  let run := Adaptive.realized geo.cfg geo.shapes g S a words dummy
  have hrep : run = Adaptive.replay a (Adaptive.transcript geo.cfg geo.shapes g S a n words dummy) :=
    (AdaptiveReplayProof.adaptiveReplay (RowCausalityStep TracePrefix TraceUnitsPrefix)
      geo.cfg geo.shapes g S m a n rfl hg hE hS words dummy).1
  have hshape := ReplayShape m a n (Adaptive.transcript geo.cfg geo.shapes g S a n words dummy)
  have hlen : (OnlineBatch.slots run).length = n := by
    rw [hrep]; exact hshape.2.2.1
  have hinitrun : (run.init.map Rec.key).Nodup := hinit
  obtain ⟨N, hkeys, htrace⟩ := ApiStructuralProof.run_premises geo.cfg g run hg hE hinitrun
  let compat : HierarchyGeometry := { geo with keyCapacity := N }
  have F : HierarchyInvariantProof.LowFacts compat.cfg compat.rows compat.direct :=
    HierarchySemanticsProof.lower hgeo.1
  have hs : BatchSettingFor compat N g run S n m :=
    ⟨le_rfl, hlen.ge, ⟨⟨hg, hE⟩, by rw [hlen]; exact hhor, hkeys, htrace, hcorrect.2.1⟩, hS⟩
  exact (BatchFreshProof.freshFor compat F N g run S n m hs words).2

end RebuildBound
