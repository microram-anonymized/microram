import RebuildBound.Proofs.ShadowNet.Core
import RebuildBound.Proofs.ShadowNet.Forest
import RebuildBound.Proofs.ShadowNet.Fiber
import RebuildBound.Proofs.ShadowNet.Swap
import RebuildBound.Proofs.ShadowNet.Class
import RebuildBound.Proofs.ShadowNet.Glue

/-!
# ShadowNet: shadow-network averaging lemmas

The `P11aProof`, `P11bProof`, `P11cProof` and `P11abProof` lemma families
reused by P12 and P13 (averages `avgB`/`cnt`, forests and read sets, bit
updates and conditional averages, swaps and binomial counts, the terminal test
per class, gluing). Moved out of P11a/b/c/ab; namespaces kept.
-/
