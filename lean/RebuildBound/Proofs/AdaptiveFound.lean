import RebuildBound.Proofs.AdaptiveFound.Batch
import RebuildBound.Proofs.AdaptiveFound.Causal

/-! # AdaptiveFound: the record a probing lane selects

Statements in `Spec/AdaptiveNative.lean`.

* `BatchFound31`: `batchFoundFor` at `geometry31.chunk h`, after relabeling
  the universe keys (`AdaptiveFound/Batch.lean`).
* `BatchFoundCausal`: proved for every configuration
  (`AdaptiveFound/Causal.lean`).

No probability is involved, so no measure-theoretic obstacle arose.
-/

namespace RebuildBound
open Spec Model Model.Hierarchy HierarchyInvariantProof AdaptiveFoundProof

theorem BatchFound31 : BatchFound31_statement := by
  intro h hh U g run S n m hs words words' dummy dummy' t ht
  let e := KeyRelabel.compression U
  have hsetting := KeyRelabel.batch_setting _ U g run S n m hs
  have key := batchFoundFor (geometry31.chunk h)
    (HierarchyLawsChunks31Proof.lowFacts_horizon HierarchyInvariant31Proof.lowFacts (h * 2 ^ 32))
    (HierarchyLawsChunks31Proof.topFacts_chunk (TopFacts.of_compatible Geometry31.1) h) rfl
    U.card g _ S n m hsetting (KeyRelabel.words e words) (KeyRelabel.words e words')
    dummy dummy' t ht
  rw [KeyRelabel.probe_batch_found, KeyRelabel.probe_batch_found] at key
  exact Option.map_injective (KeyRelabel.rec_injective e) key

theorem BatchFoundCausal : BatchFoundCausal_statement := foundCausal

end RebuildBound
