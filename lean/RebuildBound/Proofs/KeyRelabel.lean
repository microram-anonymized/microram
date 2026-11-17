import RebuildBound.Proofs.KeyRelabel.Semantics
import RebuildBound.Proofs.OnlineOblivious31
import RebuildBound.Proofs.BatchOblivious31

/-! Logical keys with 64-bit fixture identifiers in a fixed universe of at most 2^31 keys. These
endpoints apply the existing certified endpoints to a reversible compression;
they add no native-execution or AES-reduction claim. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound
open Spec Model Model.Hierarchy KeyRelabel

theorem GenericOnlineOblivious31 : GenericOnlineOblivious31_statement :=
  onlineOblivious_transport _ _ OnlineOblivious31

theorem GenericBatchOblivious31 : GenericBatchOblivious31_statement :=
  batchOblivious_transport _ _ BatchOblivious31

theorem GenericHierarchyWindows31 : GenericHierarchyWindows31_statement := by
  intro h U tr hh _ hU htr hu Ω _ μ _ tape w ht
  have htr' := tracePremises_rename (compression U) (chunkConfig config31 h) U U.card tr
    (fun k hk => (compression_lt U k).2 hk) htr
  have hu' := unshPromise_rename (compression U) (chunkConfig config31 h)
    (geometry31.chunk h).shapes tr hu
  have hb := HierarchyWindows31 h U.card (trace (compression U) tr) hh hU htr' hu' μ
    (fun ω => tapeEquiv (chunkConfig config31 h) U (tape ω))
    (fun ω => words (compression U) (w ω))
    (universe_tape_transport (chunkConfig config31 h) U μ tape w ht)
  simpa only [fails_rename, show geometry31.cfg = config31 from rfl] using hb

theorem GenericHierarchyChunk31 : GenericHierarchyChunk31_statement := by
  intro k U tr _ hU htr hu Ω _ μ _ tape w ht
  have htr' := tracePremises_rename (compression U) (chunkConfig config31 (k + 1)) U U.card tr
    (fun x hx => (compression_lt U x).2 hx) htr
  have hu' := unshPromise_rename (compression U) (chunkConfig config31 (k + 1))
    (geometry31.chunk (k + 1)).shapes tr hu
  have hb := HierarchyChunk31 k U.card (trace (compression U) tr) hU htr' hu' μ
    (fun ω => tapeEquiv (chunkConfig config31 (k + 1)) U (tape ω))
    (fun ω => words (compression U) (w ω))
    (universe_tape_transport (chunkConfig config31 (k + 1)) U μ tape w ht)
  simpa only [chunkFails_rename, show geometry31.cfg = config31 from rfl] using hb

end RebuildBound
