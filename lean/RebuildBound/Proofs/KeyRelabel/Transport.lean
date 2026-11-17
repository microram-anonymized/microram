import RebuildBound.Proofs.KeyRelabel.Premises
import RebuildBound.Proofs.KeyRelabel.Online

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.KeyRelabel
open Spec Model Model.Hierarchy Model.Online

@[simp] theorem online_probePattern_eq (e : LogicalKey ≃ LogicalKey) (run : OnlineRun) :
    probePattern (onlineRun e run) = probePattern run := funext (online_probePattern e run)

@[simp] theorem batch_probePattern_eq (e : LogicalKey ≃ LogicalKey) (run : OnlineBatch.BatchRun) :
    OnlineBatch.probePattern (batchRun e run) = OnlineBatch.probePattern run :=
  funext (batch_probePattern e run)

/-- Exact scalar laws transfer through one bijection of the joint ideal tape. -/
theorem onlineExact_transport (geo : HierarchyGeometry) (hex : OnlineExactFor geo) :
    UniverseOnlineExactFor geo := by
  intro U g run S n m hs Ω _ μ _ tape dtape w ht
  have h := hex U.card g (onlineRun (compression U) run) S n m
    (online_setting geo U g run S n m hs) μ
    (fun ω => tapeEquiv geo.cfg U (tape ω)) dtape (fun ω => words (compression U) (w ω))
    (universe_online_tape_transport geo.cfg U n m μ tape dtape w ht)
  simpa only [online_view, online_probePattern_eq] using h

/-- Batch public widths and probe flags are unchanged by the same bijection. -/
theorem batchExact_transport (geo : HierarchyGeometry) (hex : BatchExactFor geo) :
    UniverseBatchExactFor geo := by
  intro U g run S n m hs Ω _ μ _ tape dtape w ht
  have h := hex U.card g (batchRun (compression U) run) S n m
    (batch_setting geo U g run S n m hs) μ
    (fun ω => tapeEquiv geo.cfg U (tape ω)) dtape (fun ω => words (compression U) (w ω))
    (universe_online_tape_transport geo.cfg U n m μ tape dtape w ht)
  simpa only [batch_view, batch_widths, batch_probePattern_eq] using h

theorem onlineFailure_transport (geo : HierarchyGeometry) (hf : OnlineFailureFor geo) :
    UniverseOnlineFailureFor geo := by
  intro U g run S n m hs Ω _ μ _ tape dtape w ht V _ obs ι hobs hι ha A hA
  have ha' : ∀ ω, ¬ Fails geo.cfg geo.shapes (traceOf g (onlineRun (compression U) run))
      (words (compression U) (w ω)) →
      obs ω = ι (view geo.cfg geo.shapes g (onlineRun (compression U) run) S n m
        (words (compression U) (w ω)) (dummyOf (dtape ω))) := by
    intro ω hn
    rw [online_traceOf, fails_rename] at hn
    simpa only [online_view] using ha ω hn
  have h := hf U.card g (onlineRun (compression U) run) S n m
    (online_setting geo U g run S n m hs) μ
    (fun ω => tapeEquiv geo.cfg U (tape ω)) dtape (fun ω => words (compression U) (w ω))
    (universe_online_tape_transport geo.cfg U n m μ tape dtape w ht)
    obs ι hobs hι ha' A hA
  simpa only [online_probePattern_eq, online_traceOf, fails_rename] using h

theorem batchFailure_transport (geo : HierarchyGeometry) (hf : BatchFailureFor geo) :
    UniverseBatchFailureFor geo := by
  intro U g run S n m hs Ω _ μ _ tape dtape w ht V _ obs ι hobs hι ha A hA
  have ha' : ∀ ω, ¬ Fails geo.cfg geo.shapes
      (OnlineBatch.traceOf g (batchRun (compression U) run)) (words (compression U) (w ω)) →
      obs ω = ι (OnlineBatch.view geo.cfg geo.shapes g (batchRun (compression U) run) S n m
        (words (compression U) (w ω)) (dummyOf (dtape ω))) := by
    intro ω hn
    rw [batch_traceOf, fails_rename] at hn
    simpa only [batch_view] using ha ω hn
  have h := hf U.card g (batchRun (compression U) run) S n m
    (batch_setting geo U g run S n m hs) μ
    (fun ω => tapeEquiv geo.cfg U (tape ω)) dtape (fun ω => words (compression U) (w ω))
    (universe_online_tape_transport geo.cfg U n m μ tape dtape w ht)
    obs ι hobs hι ha' A hA
  simpa only [batch_probePattern_eq, batch_widths, batch_traceOf, fails_rename] using h

theorem onlineOblivious_transport (geo : HierarchyGeometry) (error : ℝ≥0∞)
    (hf : OnlineObliviousFor geo error) : UniverseOnlineObliviousFor geo error := by
  intro h hh
  dsimp only
  intro U g run S n m hs Ω _ μ _ tape dtape w ht V _ obs ι hobs hι ha A hA
  have ha' : ∀ ω, ¬ Fails (geo.chunk h).cfg (geo.chunk h).shapes
      (traceOf g (onlineRun (compression U) run)) (words (compression U) (w ω)) →
      obs ω = ι (view (geo.chunk h).cfg (geo.chunk h).shapes g
        (onlineRun (compression U) run) S n m (words (compression U) (w ω))
        (dummyOf (dtape ω))) := by
    intro ω hn
    rw [online_traceOf, fails_rename] at hn
    simpa only [online_view] using ha ω hn
  have hb := hf h hh U.card g (onlineRun (compression U) run) S n m
    (online_setting (geo.chunk h) U g run S n m hs) μ
    (fun ω => tapeEquiv (geo.chunk h).cfg U (tape ω)) dtape
    (fun ω => words (compression U) (w ω))
    (universe_online_tape_transport (geo.chunk h).cfg U n m μ tape dtape w ht)
    obs ι hobs hι ha' A hA
  simpa only [online_probePattern_eq] using hb

theorem batchOblivious_transport (geo : HierarchyGeometry) (error : ℝ≥0∞)
    (hf : BatchObliviousFor geo error) : UniverseBatchObliviousFor geo error := by
  intro h hh
  dsimp only
  intro U g run S n m hs Ω _ μ _ tape dtape w ht V _ obs ι hobs hι ha A hA
  have ha' : ∀ ω, ¬ Fails (geo.chunk h).cfg (geo.chunk h).shapes
      (OnlineBatch.traceOf g (batchRun (compression U) run)) (words (compression U) (w ω)) →
      obs ω = ι (OnlineBatch.view (geo.chunk h).cfg (geo.chunk h).shapes g
        (batchRun (compression U) run) S n m (words (compression U) (w ω))
        (dummyOf (dtape ω))) := by
    intro ω hn
    rw [batch_traceOf, fails_rename] at hn
    simpa only [batch_view] using ha ω hn
  have hb := hf h hh U.card g (batchRun (compression U) run) S n m
    (batch_setting (geo.chunk h) U g run S n m hs) μ
    (fun ω => tapeEquiv (geo.chunk h).cfg U (tape ω)) dtape
    (fun ω => words (compression U) (w ω))
    (universe_online_tape_transport (geo.chunk h).cfg U n m μ tape dtape w ht)
    obs ι hobs hι ha' A hA
  simpa only [batch_probePattern_eq, batch_widths] using hb

end RebuildBound.KeyRelabel
