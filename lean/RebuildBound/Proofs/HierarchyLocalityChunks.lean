import RebuildBound.Proofs.HierarchyLocality
import RebuildBound.Spec.HierarchyChunk

/-!
# HierarchyLocalityChunks: word locality at every chunk horizon

`HierarchyLocality`'s generic proof (`localityAt`) needs only `TimeFacts`,
which reads the levels, seeds, fanouts and products, never the horizon; so
the selected configurations' facts hold at every chunk configuration by
definitional unfolding. The horizon-freeness hypothesis is not needed.
-/

namespace RebuildBound.HierarchyLocalityChunksProof
open Model Model.DirectJob Model.Hierarchy Spec HierarchyLocalityProof

theorem timeFacts_chunk {cfg : Config} (hf : TimeFacts cfg) (h : Nat) :
    TimeFacts (chunkConfig cfg h) :=
  ⟨hf.seed, hf.prod, hf.pos⟩

end RebuildBound.HierarchyLocalityChunksProof

open RebuildBound.HierarchyLocalityChunksProof RebuildBound.HierarchyLocalityProof in
theorem RebuildBound.HierarchyLocalityChunks :
    RebuildBound.Spec.HierarchyLocalityChunks_statement := fun _ h _ =>
  ⟨localityAt _ _ (timeFacts_chunk timeFacts_uniform h), localityAt _ _ (timeFacts_chunk timeFacts_half h)⟩
